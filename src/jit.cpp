#include <sstream>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cstring>
#include <getopt.h>
#include <numeric>
#include <stack>

#include "wasmdefs.h"
#include "common.h"
#include "parse.h"
#include "ir.h"
#include "xbyak/xbyak.h"
#include "xbyak/xbyak_util.h"

struct Code : Xbyak::CodeGenerator {
  Code(size_t cap=1<<16) : Xbyak::CodeGenerator(cap) {}
};

std::vector<Xbyak::Label> function_header_labels;
std::vector<Xbyak::Label> error_labels;

int error_condition = 0;

std::unordered_map<int, int> fn_to_stack_size;

extern FuncDecl* find_main_function(WasmModule& module);

using JitEntry = uint64_t (*)();

typedef struct Table {
  int  num_entries;
  int* func_refs;
} Table;

Table jit_table;
uint64_t* globals;
void* mem_base_ptr;
uint32_t* mem_size; 
const void** fn_entry_ptr; 
int* fn_sig_id;

int get_func_stack_size(int function_index, WasmModule& module) {
  FuncDecl* func = module.getFunc(function_index);
  auto code   = func->code_bytes;

  buffer_t buf{
    .start = code.data(),
    .ptr   = code.data(),
    .end   = code.data() + code.size(),
  };

  buf.ptr = buf.start;

  int stack_size = 0;

  while (buf.ptr && buf.ptr < buf.end) {
    Opcode_t curr_instr = RD_OPCODE();
    TRACE("Reading opcode in get function stack size!\n");
    switch (curr_instr) {
      case WASM_OP_I32_ADD: 
      case WASM_OP_I32_SUB:
      case WASM_OP_I32_MUL:
      case WASM_OP_I32_DIV_S:
      case WASM_OP_I32_DIV_U:
      case WASM_OP_I32_REM_S:
      case WASM_OP_I32_REM_U:
      case WASM_OP_I32_AND:
      case WASM_OP_I32_OR:
      case WASM_OP_I32_XOR:
      case WASM_OP_I32_SHL:
      case WASM_OP_I32_SHR_S:
      case WASM_OP_I32_SHR_U: 
      case WASM_OP_I32_ROTL:
      case WASM_OP_I32_ROTR: 
      case WASM_OP_I32_EQ:
      case WASM_OP_I32_NE:
      case WASM_OP_I32_LT_S:
      case WASM_OP_I32_LT_U:
      case WASM_OP_I32_GT_S:
      case WASM_OP_I32_GT_U:
      case WASM_OP_I32_LE_S:
      case WASM_OP_I32_LE_U:
      case WASM_OP_I32_GE_S:
      case WASM_OP_I32_GE_U: {
        break;
      }
      case WASM_OP_NOP:
      case WASM_OP_I32_CLZ:
      case WASM_OP_I32_CTZ: 
      case WASM_OP_I32_POPCNT: {
        break;
      } 
      case WASM_OP_BR: {
        RD_U32();
        break;
      }
      case WASM_OP_BR_IF:
      case WASM_OP_BR_TABLE: {
        RD_U32();
        break;
      }
      case WASM_OP_GLOBAL_SET:
      case WASM_OP_LOCAL_SET: {
        RD_U32();
        break;
      }
      case WASM_OP_I32_CONST: {
        RD_I32();
        stack_size++;
        break;
      }
      case WASM_OP_GLOBAL_GET:
      case WASM_OP_LOCAL_GET: {
        RD_U32();
        stack_size++;
        break;
      } 
      case WASM_OP_CALL: {
        uint32_t called_function_idx = RD_U32();
        stack_size += (module.getFunc(called_function_idx)->sig->num_results - module.getFunc(called_function_idx)->sig->num_params);
        break;
      }
      case WASM_OP_CALL_INDIRECT: {
        int max_args = -1;
        for (int i = 0; i < jit_table.num_entries; i++) {
          if (jit_table.func_refs[i] != -1) {
            if (module.getFunc(jit_table.func_refs[i])->sig->num_params > max_args) {
              max_args = module.getFunc(jit_table.func_refs[i])->sig->num_params;
            }
          }
        }
        stack_size += max_args;
        break;
      }
      case WASM_OP_F64_STORE:
      case WASM_OP_I32_STORE16:
      case WASM_OP_I32_STORE8:
      case WASM_OP_I32_STORE: {
        RD_U32();
        RD_U32();
        break;
      }
      case WASM_OP_F64_LOAD:
      case WASM_OP_I32_LOAD16_S:
      case WASM_OP_I32_LOAD16_U:
      case WASM_OP_I32_LOAD8_U:
      case WASM_OP_I32_LOAD8_S:
      case WASM_OP_I32_LOAD: {
        RD_U32();
        RD_U32();
        break;
      }
      case WASM_OP_F64_CONST: {
        RD_U64_RAW();
        break;
      }
      default: {
        break;
      }
    }
  }
  return stack_size;
}

void add_fn_prologue(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;

  auto params = module.getFunc(function_index)->sig->num_params;
  auto num_locals = module.getFunc(function_index)->num_pure_locals;
  auto stack_size = get_func_stack_size(function_index, module);

  int alloc_size = params + num_locals + stack_size;

  if (alloc_size % 2 == 0) {
    alloc_size += 1;
  }

  fn_to_stack_size[function_index] = alloc_size;

  fn_asm->L(function_header_labels[function_index]);
  fn_asm->push(rbp); 
  fn_asm->mov(rbp, rsp);
  fn_asm->push(rbx); 
  fn_asm->push(r12); 
  fn_asm->push(r13); 
  fn_asm->push(r14); 
  fn_asm->push(r15);
  fn_asm->sub(rsp, (alloc_size) * 8);
  fn_asm->lea(rbx, ptr[rsp + ((stack_size + params + num_locals) * 8) - 8]);
  fn_asm->lea(r12, ptr[rsp + ((stack_size + params + num_locals) * 8) - 8]);

  return;
}

void add_fn_epilogue(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;

  auto alloc_size = fn_to_stack_size[function_index];

  fn_asm->add(rsp, (alloc_size) * 8);
  fn_asm->pop(r15); 
  fn_asm->pop(r14); 
  fn_asm->pop(r13); 
  fn_asm->pop(r12); 
  fn_asm->pop(rbx);
  fn_asm->pop(rbp);
  fn_asm->ret();

  return;
}

int store_args_to_call(Code* fn_asm, int sig_idx, WasmModule& module) {
  TRACE("In store args to call!\n");

  int called_fn_num_params = module.getSig(sig_idx)->num_params;
  std::vector<wasm_type_t> param_types(module.getSig(sig_idx)->params.begin(), module.getSig(sig_idx)->params.end());
  std::vector<Xbyak::Reg> int_arg_regs = {Xbyak::util::rdi, Xbyak::util::rsi, Xbyak::util::rdx, Xbyak::util::rcx, Xbyak::util::r8, Xbyak::util::r9};

  for (int i = 0; i < called_fn_num_params; i++) {
    switch (param_types[i]) {
      case WASM_TYPE_I32: {
        if (i < 6) {
          fn_asm->mov(int_arg_regs[i], Xbyak::util::ptr [Xbyak::util::rbx+(called_fn_num_params-i)*8]);
        } else {
          fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx+(i-5)*8]);
          fn_asm->push(Xbyak::util::r13);
        }
        break;
      }
      case WASM_TYPE_F64: {
        if (i < 6) {
          fn_asm->mov(int_arg_regs[i], Xbyak::util::ptr [Xbyak::util::rbx+(called_fn_num_params-i)*8]);
        } else {
          fn_asm->mov(Xbyak::util::r13, Xbyak::util::xmm0);
        }
        break;
      }
    }
  }
  fn_asm->add(Xbyak::util::rbx, called_fn_num_params*8);

  TRACE("Out of store args to call!\n");

  return (std::max(0, called_fn_num_params - 6));
}

void load_args(Code* fn_asm, int function_index, WasmModule& module) {
  TRACE("In loading args stage!\n");

  int fn_num_params = module.getFunc(function_index)->sig->num_params;
  std::vector<wasm_type_t> param_types(module.getFunc(function_index)->sig->params.begin(), module.getFunc(function_index)->sig->params.end());
  std::vector<Xbyak::Operand> arg_regs = {Xbyak::util::rdi, Xbyak::util::rsi, Xbyak::util::rdx, Xbyak::util::rcx, Xbyak::util::r8, Xbyak::util::r9};

  for (int i = 0; i < fn_num_params; i++) {
    switch (param_types[i]) {
      case WASM_TYPE_I32: {
        if (i < 6) {
          fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], arg_regs[i]);
          fn_asm->sub(Xbyak::util::rbx, 8);
        } else {
          fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbp + 16 + (i - 6) * 8]);
          fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
          fn_asm->sub(Xbyak::util::rbx, 8);
        } 
        break;
      } 
      case WASM_TYPE_F64: {
        if (i < 6) {
          fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], arg_regs[i]);
          fn_asm->sub(Xbyak::util::rbx, 8);
        } else {
          fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::ptr [Xbyak::util::rbp + 16 + (i - 6) * 8]);
          fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
          fn_asm->sub(Xbyak::util::rbx, 8);
        } 
        break;
      }
    }
  }
  for (int i = 0; i < module.getFunc(function_index)->num_pure_locals; i++) {
    fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], 0);
    fn_asm->sub(Xbyak::util::rbx, 8);
  }
  fn_asm->sub(Xbyak::util::rbx, 8);

  TRACE("Out of loading args stage!\n");
}

void store_args(Code* fn_asm, int function_index, WasmModule& module, std::vector<std::string>& args) {
  TRACE("In store args!\n");

  using namespace Xbyak::util;

  auto params = module.getFunc(function_index)->sig->params;
  std::vector<wasm_type_t> param_vec(params.begin(), params.end());
  std::vector<Xbyak::Operand> arg_regs = {Xbyak::util::rdi, Xbyak::util::rsi, Xbyak::util::rdx, Xbyak::util::rcx, Xbyak::util::r8, Xbyak::util::r9};

  fn_asm->push(rbp); 
  fn_asm->mov(rbp, rsp);
  fn_asm->push(rbx); 
  fn_asm->push(r12); 
  fn_asm->push(r13); 
  fn_asm->push(r14); 
  fn_asm->push(r15);

  for (int i = 0; i < args.size(); i++) {
    if (i < 6) {
      switch (param_vec[i]) {
        case WASM_TYPE_I32: {
          fn_asm->mov(arg_regs[i], stoi(args[i]));
          break;
        }
        case WASM_TYPE_F64: {
          fn_asm->mov(arg_regs[i], std::bit_cast<uint64_t>(stod(args[i])));
          break;
        }
      }
    } else {
      switch (param_vec[i]) {
        case WASM_TYPE_I32: {
          fn_asm->mov(Xbyak::util::r13, stoi(args[i]));
          fn_asm->push(Xbyak::util::r13);
          break;
        }
        case WASM_TYPE_F64: {
          fn_asm->mov(Xbyak::util::r13, std::bit_cast<uint64_t>(stod(args[i])));
          fn_asm->push(Xbyak::util::r13);
          break;
        }
      }
    }
  }

  int rsp_push_size = std::max(0, (int)(args.size()) - 6);

  if (args.size() % 2 == 0) {
    rsp_push_size += 1; 
    fn_asm->sub(Xbyak::util::rsp, 8);
  }

  fn_asm->call(function_header_labels[function_index]);
  fn_asm->add(Xbyak::util::rsp, rsp_push_size * 8);
  fn_asm->pop(r15); 
  fn_asm->pop(r14); 
  fn_asm->pop(r13); 
  fn_asm->pop(r12); 
  fn_asm->pop(rbx);
  fn_asm->pop(rbp);
  fn_asm->ret();

  TRACE("Out of store args!\n");
}

void setup_error_function(Code* fn_asm, int function_index, WasmModule& module) {
  fn_asm->L(error_labels[function_index]);
  fn_asm->mov(Xbyak::util::r13, (uintptr_t)(&error_condition));
  fn_asm->mov(Xbyak::util::qword [Xbyak::util::r13], 1);
  add_fn_epilogue(fn_asm, function_index, module);
}

void move_ret_val(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;
  auto ret_vals = module.getFunc(function_index)->sig->results;
  std::vector<wasm_type_t> ret_vec(ret_vals.begin(), ret_vals.end());
  if (ret_vec.size()) {
    TRACE("Moving return value!\n");
    fn_asm->mov(rax, qword [rbx + 8]);
  }
}

typedef enum ctrl_flow_block_t {
  FUNCTION,
  BLOCK, 
  LOOP,
  IF,
  IF_WITH_ELSE, 
  IF_NO_ELSE,
  ELSE,
  FN_END
} ctrl_flow_block_t; 

typedef struct control_flow_label_t {
  Xbyak::Label branch_label;
  Xbyak::Label else_label;
  ctrl_flow_block_t block_type; 
} control_flow_label_t;

void wasm_to_x86_loop(Code* fn_asm, int function_index, WasmModule& module) {
  auto label_stack = std::deque<control_flow_label_t>();
  auto code = module.getFunc(function_index)->code_bytes;

  control_flow_label_t fn_label;
  Xbyak::Label base_fn_label;
  fn_label.block_type = FUNCTION;
  fn_label.branch_label = base_fn_label;
  label_stack.push_front(fn_label);

  fn_asm->nop();

  buffer_t buf{
    .start = code.data(),
    .ptr   = code.data(),
    .end   = code.data() + code.size(),
  };

  buf.ptr = buf.start;

  while (buf.ptr != buf.end) {
    auto opcode = RD_OPCODE();
    switch (opcode) {
      case WASM_OP_UNREACHABLE: {
        fn_asm->jmp(error_labels[function_index]);
        break;
      }
      case WASM_OP_NOP: {
        fn_asm->nop();
        break;
      }
      case WASM_OP_RETURN: {
        move_ret_val(fn_asm, function_index, module);
        add_fn_epilogue(fn_asm, function_index, module);
        break;
      }
      case WASM_OP_CALL: {
        uint32_t called_function_idx = RD_U32(); 
        const auto& called_label = function_header_labels[called_function_idx];
        int num_spilled_args = store_args_to_call(fn_asm, module.getSigIdx(module.getFunc(called_function_idx)->sig), module);
        int rsp_offset = 0;

        if (num_spilled_args % 2 == 0 && fn_to_stack_size[function_index] % 2 == 0 || 
            num_spilled_args % 2 == 1 && fn_to_stack_size[function_index] % 2 == 1) {
          fn_asm->sub(Xbyak::util::rsp, 8);
          rsp_offset = 1;
        }        

        fn_asm->call(called_label);
        fn_asm->add(Xbyak::util::rsp, (num_spilled_args + rsp_offset) * 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_CALL_INDIRECT: {
        uint32_t type_index = RD_U32();
        RD_BYTE();
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]); // R13D now contains the table index. 
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->cmp(Xbyak::util::r13d, jit_table.num_entries);
        fn_asm->jae(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r14, (uintptr_t)(fn_sig_id));
        fn_asm->lea(Xbyak::util::r14, Xbyak::util::ptr[Xbyak::util::r14 + Xbyak::util::r13 * 4]); // R14 now contains the ptr to the sig index.
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::qword [Xbyak::util::r14]); //R14 now contains the signature index.
        fn_asm->mov(Xbyak::util::r14d, Xbyak::util::r14d);
        fn_asm->cmp(Xbyak::util::r14d, type_index);
        fn_asm->jne(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)(jit_table.func_refs)); //R15 now contains a ptr to the base of the func_ref table.
        fn_asm->lea(Xbyak::util::r13, Xbyak::util::ptr[Xbyak::util::r15 + Xbyak::util::r13 * 4]); 
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::qword [Xbyak::util::r13]); // This will load the function index from the table.
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::r13d);
        fn_asm->cmp(Xbyak::util::r13d, -1);
        fn_asm->je(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)(fn_entry_ptr));
        fn_asm->lea(Xbyak::util::r13, Xbyak::util::ptr[Xbyak::util::r15 + Xbyak::util::r13 * 8]); // R13 now contains the pointer to the function function index. 
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r13]); 

        int num_spilled_args = store_args_to_call(fn_asm, type_index, module);
        int rsp_offset = 0;
        if (num_spilled_args % 2 == 0 && fn_to_stack_size[function_index] % 2 == 0 || 
            num_spilled_args % 2 == 1 && fn_to_stack_size[function_index] % 2 == 1) {
          fn_asm->sub(Xbyak::util::rsp, 8);
          rsp_offset = 1;
        }

        fn_asm->call(Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rsp, (num_spilled_args + rsp_offset) * 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_LOOP: {
        RD_U32();
        control_flow_label_t new_label;
        Xbyak::Label new_loop_label;

        new_label.block_type = LOOP;
        new_label.branch_label = new_loop_label;

        fn_asm->L(new_label.branch_label);
        label_stack.push_front(new_label);
        break;
      }
      case WASM_OP_BLOCK: {
        RD_U32();
        control_flow_label_t new_label;
        new_label.block_type = BLOCK;
        Xbyak::Label new_block_label;
        new_label.branch_label = new_block_label;
        label_stack.push_front(new_label);
        break;
      }
      case WASM_OP_IF: {
        RD_U32();
        control_flow_label_t new_label;
        Xbyak::Label new_if_label;
        Xbyak::Label new_end_label;
        new_label.block_type = IF_NO_ELSE; 
        new_label.else_label = new_if_label;
        new_label.branch_label = new_end_label;
        label_stack.push_front(new_label);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->cmp(Xbyak::util::r13, 0);
        const auto& label = label_stack[0];
        fn_asm->je(label.else_label, fn_asm->T_NEAR); // To go to the ELSE.
        break;
      }
      case WASM_OP_ELSE: {
        Xbyak::Label new_else_label;
        const auto& label = label_stack[0];
        label_stack[0].block_type = IF_WITH_ELSE;
        fn_asm->jmp(label.branch_label, fn_asm->T_NEAR);
        fn_asm->L(label_stack[0].else_label);
        break;
      }
      case WASM_OP_BR: {
        uint32_t label = RD_U32();
        const auto& jump_label = label_stack[label];
        fn_asm->jmp(jump_label.branch_label, fn_asm->T_NEAR);
        break;
      }
      case WASM_OP_BR_IF: {
        uint32_t label = RD_U32();
        const auto& jump_label = label_stack[label];
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->cmp(Xbyak::util::r13, 0);
        fn_asm->jne(jump_label.branch_label, fn_asm->T_NEAR);
        break;
      }
      case WASM_OP_BR_TABLE: {
        uint32_t number_of_labels = RD_U32();
        std::vector<uint32_t> table_labels;
        for (int i = 0; i < number_of_labels; i++) {
          uint32_t label = RD_U32();
          table_labels.push_back(label);
        }
        uint32_t default_label = RD_U32(); 
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        for (int i = 0; i < number_of_labels; i++) {
          fn_asm->cmp(Xbyak::util::r13, i); fn_asm->je(label_stack[table_labels[i]].branch_label, fn_asm->T_NEAR);
        }
        fn_asm->jmp(label_stack[default_label].branch_label, fn_asm->T_NEAR);
        break;
      }
      case WASM_OP_END: {
        control_flow_label_t patched_label = label_stack.front();
        if (patched_label.block_type != LOOP) {
          if (patched_label.block_type == IF_NO_ELSE) {
            fn_asm->L(patched_label.else_label);
          }
          fn_asm->L(patched_label.branch_label);
        }
        label_stack.pop_front();
        break; 
      }
      case WASM_OP_SELECT: {
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->mov(Xbyak::util::r14d, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::r15d, Xbyak::util::qword [Xbyak::util::rbx + 24]);
        fn_asm->add(Xbyak::util::rbx, 24);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r15d);
        fn_asm->cmp(Xbyak::util::r13d, 0);
        fn_asm->cmovge(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_LOCAL_TEE: {
        int const_arg = RD_U32();
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::r12 - const_arg * 8], Xbyak::util::r13);
        break;
      }
      case WASM_OP_I32_CONST: {
        int const_arg = RD_I32(); 
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], const_arg);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_LOCAL_GET: {
        int const_arg = RD_U32();
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::r12 - const_arg * 8]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_LOCAL_SET: {
        int const_arg = RD_U32();
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::r12 - const_arg * 8], Xbyak::util::r13);
        fn_asm->add(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LOAD8_S: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 1);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::rax, 0);
        fn_asm->mov(Xbyak::util::al, Xbyak::util::byte [Xbyak::util::r13]);
        fn_asm->cbw();
        fn_asm->cwde();
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LOAD8_U: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 1);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::rax, 0);
        fn_asm->mov(Xbyak::util::al, Xbyak::util::byte [Xbyak::util::r13]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LOAD16_S: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 2);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::rax, 0);
        fn_asm->mov(Xbyak::util::ax, Xbyak::util::word [Xbyak::util::r13]);
        fn_asm->cwde();
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LOAD16_U: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 2);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::rax, 0);
        fn_asm->mov(Xbyak::util::ax, Xbyak::util::word [Xbyak::util::r13]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LOAD: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 4);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::r13]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      } 
      case WASM_OP_I32_STORE8: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 1);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::ptr [Xbyak::util::rbx + 8]); // Value
        fn_asm->add(Xbyak::util::rbx, 16); 
        fn_asm->mov(Xbyak::util::byte [Xbyak::util::r13], Xbyak::util::r15b);
        break;
      }
      case WASM_OP_I32_STORE16: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 2);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::ptr [Xbyak::util::rbx + 8]); // Value
        fn_asm->add(Xbyak::util::rbx, 16); 
        fn_asm->mov(Xbyak::util::word [Xbyak::util::r13], Xbyak::util::r15w);
        break;
      }
      case WASM_OP_I32_STORE: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 4);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::ptr [Xbyak::util::rbx + 8]); // Value
        fn_asm->add(Xbyak::util::rbx, 16); 
        fn_asm->mov(Xbyak::util::dword [Xbyak::util::r13], Xbyak::util::r15d);
        break;
      }
      case WASM_OP_I32_ADD: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_SUB: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->sub(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_MUL: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->imul(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_DIV_S: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->cdq();
        fn_asm->cmp(Xbyak::util::qword [Xbyak::util::rbx + 8], 0);
        fn_asm->je(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->idiv(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::eax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_DIV_U: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::edx, 0);
        fn_asm->cmp(Xbyak::util::qword [Xbyak::util::rbx + 8], 0);
        fn_asm->je(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->div(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::eax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_REM_S: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->cdq();
        fn_asm->cmp(Xbyak::util::qword [Xbyak::util::rbx + 8], 0);
        fn_asm->je(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->idiv(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::edx);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_REM_U: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::edx, 0);
        fn_asm->cmp(Xbyak::util::qword [Xbyak::util::rbx + 8], 0);
        fn_asm->je(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->div(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::edx);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_AND: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_OR: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->or_(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_XOR: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->xor_(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_SHL: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::rcx, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->shl(Xbyak::util::r13d, Xbyak::util::cl);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_SHR_S: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::rcx, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->sar(Xbyak::util::r13d, Xbyak::util::cl);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_SHR_U: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::rcx, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->shr(Xbyak::util::r13d, Xbyak::util::cl);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_ROTL: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::rcx, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->rol(Xbyak::util::r13d, Xbyak::util::cl);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_ROTR: {
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::rcx, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->ror(Xbyak::util::r13d, Xbyak::util::cl);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_EQ: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmove(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_EQZ: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->cmove(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_NE: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovne(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LT_S: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovl(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LT_U: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovb(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_GT_S: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovg(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_GT_U: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmova(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LE_S: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovle(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_LE_U: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovbe(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_GE_S: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovge(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_GE_U: {
        fn_asm->mov(Xbyak::util::r14, 0);
        fn_asm->mov(Xbyak::util::r15, 1);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->cmp(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->cmovae(Xbyak::util::r14, Xbyak::util::r15);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r14);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_CLZ: {
        fn_asm->lzcnt(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_CTZ: {
        fn_asm->tzcnt(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_POPCNT: {
        fn_asm->popcnt(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_EXTEND16_S: {
        fn_asm->mov(Xbyak::util::r13w, Xbyak::util::word [Xbyak::util::rbx + 8]);
        fn_asm->movsx(Xbyak::util::r13d, Xbyak::util::r13w);
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::r13d);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_EXTEND8_S: {
        fn_asm->mov(Xbyak::util::r13b, Xbyak::util::byte [Xbyak::util::rbx + 8]);
        fn_asm->movsx(Xbyak::util::r13d, Xbyak::util::r13b);
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::r13d);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_CONST: {
        uint64_t bits = RD_U64_RAW();            
        fn_asm->mov(Xbyak::util::r13, bits);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_TRUNC_F64_S: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->cvttsd2si(Xbyak::util::rax, Xbyak::util::xmm0);
        fn_asm->cmp(Xbyak::util::rax, 2147483647);
        fn_asm->jg(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->cmp(Xbyak::util::rax, -2147483648);
        fn_asm->jl(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::rax);
        break;
      }
      case WASM_OP_I32_TRUNC_F64_U: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->cvttsd2si(Xbyak::util::rax, Xbyak::util::xmm0);
        fn_asm->test(Xbyak::util::rax, Xbyak::util::rax);
        fn_asm->js(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->cmp(Xbyak::util::rax, 0xFFFFFFFF);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::rax);
        break;
      }
      case WASM_OP_F64_CONVERT_I32_S: {
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->movsxd(Xbyak::util::r13, Xbyak::util::r13d);
        fn_asm->cvtsi2sd(Xbyak::util::xmm0, Xbyak::util::r13);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_CONVERT_I32_U: {
        fn_asm->mov(Xbyak::util::r13d, Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->cvtsi2sd(Xbyak::util::xmm0, Xbyak::util::r13);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_ADD: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->addsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_MUL: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mulsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_DIV: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->divsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_SUB: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->subsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      } 
      case WASM_OP_F64_ABS: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->mov(Xbyak::util::r13, 0x7FFFFFFFFFFFFFFF);
        fn_asm->movq(Xbyak::util::xmm2, Xbyak::util::r13);
        fn_asm->andpd(Xbyak::util::xmm0, Xbyak::util::xmm2);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_NEG: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->mov(Xbyak::util::r13, 0x8000000000000000);
        fn_asm->movq(Xbyak::util::xmm2, Xbyak::util::r13);
        fn_asm->xorpd(Xbyak::util::xmm0, Xbyak::util::xmm2);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_CEIL: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->roundsd(Xbyak::util::xmm0, Xbyak::util::xmm0, 2); 
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_FLOOR: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->roundsd(Xbyak::util::xmm0, Xbyak::util::xmm0, 9); 
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_TRUNC: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->roundsd(Xbyak::util::xmm0, Xbyak::util::xmm0, 3); 
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_NEAREST: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->roundsd(Xbyak::util::xmm0, Xbyak::util::xmm0, 0); 
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_SQRT: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->sqrtsd(Xbyak::util::xmm0, Xbyak::util::xmm0);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx + 8], Xbyak::util::xmm0);
        break;
      }
      case WASM_OP_F64_COPYSIGN: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::r13, 0x8000000000000000);
        fn_asm->movq(Xbyak::util::xmm2, Xbyak::util::r13);
        fn_asm->mov(Xbyak::util::r13, 0x7FFFFFFFFFFFFFFF);
        fn_asm->movq(Xbyak::util::xmm3, Xbyak::util::r13);
        fn_asm->andpd(Xbyak::util::xmm0, Xbyak::util::xmm2);
        fn_asm->andpd(Xbyak::util::xmm1, Xbyak::util::xmm3);
        fn_asm->orpd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_MAX: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->maxsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_MIN: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->minsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movsd(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::xmm0);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_EQ: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmpeqsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_NE: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmpneqsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_LE: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmplesd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_LT: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmpltsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_GE: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmpnltsd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_GT: {
        fn_asm->movsd(Xbyak::util::xmm0, Xbyak::util::qword [Xbyak::util::rbx + 16]);
        fn_asm->movsd(Xbyak::util::xmm1, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->cmpnlesd(Xbyak::util::xmm0, Xbyak::util::xmm1);
        fn_asm->movq(Xbyak::util::r13, Xbyak::util::xmm0);
        fn_asm->mov(Xbyak::util::r14, 1);
        fn_asm->and_(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_F64_STORE: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 16]);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 8);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index], fn_asm->T_NEAR);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::ptr [Xbyak::util::rbx + 8]); // Value
        fn_asm->add(Xbyak::util::rbx, 16); 
        fn_asm->mov(Xbyak::util::qword[Xbyak::util::r13], Xbyak::util::r15);
        break;
      } 
      case WASM_OP_F64_LOAD: {
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        fn_asm->mov(Xbyak::util::r14, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->add(Xbyak::util::r14d, offset);
        fn_asm->jc(error_labels[function_index]);
        fn_asm->mov(Xbyak::util::r15, (uintptr_t)mem_size);
        fn_asm->mov(Xbyak::util::r15, Xbyak::util::qword [Xbyak::util::r15]);
        fn_asm->sub(Xbyak::util::r15, 8);
        fn_asm->cmp(Xbyak::util::r14d, Xbyak::util::r15d);
        fn_asm->ja(error_labels[function_index]);
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)mem_base_ptr);
        fn_asm->add(Xbyak::util::r13, Xbyak::util::r14);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::qword [Xbyak::util::r13]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_GLOBAL_GET: {
        uint32_t idx = RD_U32();
        fn_asm->mov(Xbyak::util::r13, (uintptr_t)globals);
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::qword[Xbyak::util::r13 + idx * 8]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_GLOBAL_SET: {
        uint32_t idx = RD_U32();
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::qword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->mov(Xbyak::util::r14, (uintptr_t)globals);
        fn_asm->lea(Xbyak::util::r14, Xbyak::util::qword [Xbyak::util::r14 + idx * 8]);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::r14], Xbyak::util::r13);
        break;
      }
      case WASM_OP_DROP: {
        fn_asm->add(Xbyak::util::rbx, 8);
        break;
      }
      default: {
        break;
      }
    }
  }
}

static JitEntry compile_function(bool is_main_fn, Code* cb, int function_index, WasmModule& module, std::vector<std::string>& args) {

  using namespace Xbyak::util;

  add_fn_prologue(cb, function_index, module);
  load_args(cb, function_index, module);
  wasm_to_x86_loop(cb, function_index, module);
  move_ret_val(cb, function_index, module);
  add_fn_epilogue(cb, function_index, module);

  FILE* f = fopen("jit.bin", "wb");
  fwrite(cb->getCode(), 1, cb->getSize(), f);
  fclose(f);

  return cb->getCode<JitEntry>();
}

uint64_t get_global_const(WasmModule& module, bytearr& global_bytes) {
  buffer_t buf{
    .start = global_bytes.data(),
    .ptr   = global_bytes.data(),
    .end   = global_bytes.data() + global_bytes.size(),
  };

  buf.ptr = buf.start;

  while (buf.ptr != buf.end) {
    auto opcode = RD_OPCODE();
    switch (opcode) {
      case WASM_OP_I32_CONST: {
        uint64_t global = (uint64_t)RD_I32();
        return global;
      }
      case WASM_OP_F64_CONST: {
        uint64_t bits = RD_U64_RAW();            
        double global;
        memcpy(&global, &bits, sizeof(global));
        return std::bit_cast<uint64_t>(global);
      }
      default: {
        break;
      }
    }
  }
}

void jit(WasmModule& module, std::vector<std::string>& args) {
    using namespace Xbyak::util;
    auto cb = new Code(1<<15);

    FuncDecl* main_fn = find_main_function(module);
    int main_fn_idx = module.getFuncIdx(main_fn);

    mem_size = (uint32_t*)calloc(1, sizeof(int));

    if (module.getMemorySize() > 0) {
      auto mem_list = module.getMemory(0);
      mem_base_ptr = calloc(static_cast<size_t>(mem_list->limits.initial) * 65536, sizeof(char));
      *mem_size = mem_list->limits.initial * 65536;
    } 

    if (module.getDataSize() > 0) {
    for (int j = 0; j < module.getDataSize(); j++) {
      auto data_list = module.getData(j);
      for (int i = 0; i < data_list->bytes.size(); i++) {
          char* mem_arr = static_cast<char*>(mem_base_ptr);
          mem_arr[data_list->mem_offset + i] = data_list->bytes[i];
        }
      }
    }

    if (module.getTableSize() > 0) {
      auto data_list = module.getTable(0);
      jit_table.num_entries = data_list->limits.initial;
      jit_table.func_refs = (int*)calloc(jit_table.num_entries, sizeof(int));
      for(int i = 0; i < jit_table.num_entries; i++) {
        jit_table.func_refs[i] = -1;
      }
    }

    if (module.getElemsSize() > 0) {
      for (int i = 0; i < module.getElemsSize(); i++) {
        auto elem_list = module.getElems(i);
        auto it = elem_list->func_indices.begin();
        for (int j = 0; j < elem_list->func_indices.size(); j++) {
          jit_table.func_refs[elem_list->table_offset + j] = module.getFuncIdx(*it);
          it++;
        }
      }
    }

    for (int i = 0; i < module.Funcs().size(); i++) {
      Xbyak::Label new_label;
      function_header_labels.push_back(new_label);
      Xbyak::Label new_error_label;
      error_labels.push_back(new_error_label); 
    }

    fn_sig_id = (int*)calloc(module.Funcs().size(), sizeof(int));
    fn_entry_ptr = (const void**)calloc(module.Funcs().size(), sizeof(void*));
    globals = (uint64_t*)calloc(module.Globals().size(), 8);

    for (int i = 0; i < module.Globals().size(); i++) {
      globals[i] = get_global_const(module, module.Globals()[i].init_expr_bytes);
    }

    store_args(cb, main_fn_idx, module, args);

    JitEntry fn = compile_function(true, cb, main_fn_idx, module, args);

    for (int i = 0; i < module.Funcs().size(); i++) {
      if (i != main_fn_idx) {
        auto compiled_fn = compile_function(false, cb, i, module, args);
      }
    }

    for (int i = 0; i < module.Funcs().size(); i++) {
      setup_error_function(cb, i, module);
    }

    for (int i = 0; i < (int)module.Funcs().size(); i++) {
      fn_sig_id[i] = module.getSigIdx(module.getFunc(i)->sig);
    }

    for (int i = 0; i < (int)module.Funcs().size(); i++) {
      const void* label_address = function_header_labels[i].getAddress();
      fn_entry_ptr[i] = label_address;
    }

    uint64_t result;

    try {
      result = fn();                          
    } catch (...) {
      std::cerr << "!trap" << std::endl;
      return;
    }

    if(error_condition == 1) {
      std::cout << "!trap" << std::endl;
      return;
    }

    auto ret_type = module.getFunc(main_fn_idx)->sig->results;
    auto num_ret_vals = module.getFunc(main_fn_idx)->sig->num_results;

    if (num_ret_vals) {
      switch (*(ret_type.begin())) {
        case WASM_TYPE_I32: {
          std::cout << static_cast<int>(result) << "\n"; 
          return;
        }
        case WASM_TYPE_F64: {
          std::cout << std::fixed << std::setprecision(6) << std::bit_cast<double>(result) << "\n";
          return;
        }
      }
    }
}
