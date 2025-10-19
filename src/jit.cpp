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

extern FuncDecl* find_main_function(WasmModule& module);

using JitEntry = int (*)();
using DoubleJitEntry = double (*)();
using VoidJitEntry = void (*)();

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
      case WASM_OP_LOCAL_SET: {
        RD_U32();
        break;
      }
      case WASM_OP_I32_CONST: {
        RD_I32();
        stack_size++;
        break;
      }
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
  TRACE("Stack size of function %d is %d!\n", function_index, stack_size);
  fn_asm->L(function_header_labels[function_index]);
  fn_asm->push(rbp); 
  fn_asm->mov(rbp, rsp);
  fn_asm->push(rbx); 
  fn_asm->push(r12); 
  fn_asm->push(r13); 
  fn_asm->push(r14); 
  fn_asm->push(r15);
  fn_asm->sub(rsp, (stack_size + params + num_locals) * 8);
  fn_asm->lea(rbx, ptr[rsp + ((stack_size + params + num_locals) * 8) - 8]);
  fn_asm->lea(r12, ptr[rsp + ((stack_size + params + num_locals) * 8) - 8]);
  return;
}

void add_fn_epilogue(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;
  auto params = module.getFunc(function_index)->sig->num_params;
  auto num_locals = module.getFunc(function_index)->num_pure_locals;
  auto stack_size = get_func_stack_size(function_index, module);
  fn_asm->add(rsp, (stack_size + params + num_locals) * 8);
  fn_asm->pop(r15); 
  fn_asm->pop(r14); 
  fn_asm->pop(r13); 
  fn_asm->pop(r12); 
  fn_asm->pop(rbx);
  fn_asm->pop(rbp);
  fn_asm->ret();
  return;
}

int store_args_to_call(Code* fn_asm, int called_function_index, WasmModule& module) {
  int called_fn_num_params = module.getFunc(called_function_index)->sig->num_params;
  std::vector<Xbyak::Operand> arg_regs = {Xbyak::util::rdi, Xbyak::util::rsi, Xbyak::util::rdx, Xbyak::util::rcx, Xbyak::util::r8, Xbyak::util::r9};
  for (int i = 0; i < called_fn_num_params; i++) {
    if (i < 6) {
      fn_asm->mov(arg_regs[i], Xbyak::util::ptr [Xbyak::util::rbx+(called_fn_num_params-i)*8]);
    } else {
      fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx+(i-5)*8]);
      fn_asm->push(Xbyak::util::r13);
    }
  }
  fn_asm->add(Xbyak::util::rbx, called_fn_num_params*8);
  return (std::max(0, called_fn_num_params - 6));
}

void load_args(Code* fn_asm, int function_index, WasmModule& module) {
  int fn_num_params = module.getFunc(function_index)->sig->num_params;
  std::vector<Xbyak::Operand> arg_regs = {Xbyak::util::rdi, Xbyak::util::rsi, Xbyak::util::rdx, Xbyak::util::rcx, Xbyak::util::r8, Xbyak::util::r9};
  for (int i = 0; i < fn_num_params; i++) {
    if (i < 6) {
      fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], arg_regs[i]);
      fn_asm->sub(Xbyak::util::rbx, 8);
    } else {
      fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbp + 16 + (i - 6) * 8]);
      fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::r13);
      fn_asm->sub(Xbyak::util::rbx, 8);
    } 
  }
}

void store_args(Code* fn_asm, int function_index, WasmModule& module, std::vector<std::string>& args) {
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
          fn_asm->mov(arg_regs[i], stod(args[i]));
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
          fn_asm->mov(Xbyak::util::r13, stod(args[i]));
          fn_asm->push(Xbyak::util::r13);
          break;
        }
      }
    }
  }
  fn_asm->call(function_header_labels[function_index]);
  fn_asm->add(Xbyak::util::rsp, std::max(0, static_cast<int>(args.size())- 6) * 8);
  fn_asm->pop(r15); 
  fn_asm->pop(r14); 
  fn_asm->pop(r13); 
  fn_asm->pop(r12); 
  fn_asm->pop(rbx);
  fn_asm->pop(rbp);
  fn_asm->ret();
}

void move_ret_val(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;
  auto ret_vals = module.getFunc(function_index)->sig->results;
  std::vector<wasm_type_t> ret_vec(ret_vals.begin(), ret_vals.end());
  if (ret_vec.size()) {
    TRACE("Moving return value!\n");
    fn_asm->mov(eax, dword [rbx + 8]);
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
  Xbyak::Label label;
  ctrl_flow_block_t block_type; 
} control_flow_label_t;

void wasm_to_x86_loop(Code* fn_asm, int function_index, WasmModule& module) {
  auto label_stack = std::deque<control_flow_label_t>();
  auto code = module.getFunc(function_index)->code_bytes;

  control_flow_label_t fn_label;
  Xbyak::Label base_fn_label;
  fn_label.block_type = FUNCTION;
  fn_label.label = base_fn_label;
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
      case WASM_OP_RETURN: {
        move_ret_val(fn_asm, function_index, module);
        add_fn_epilogue(fn_asm, function_index, module);
        fn_asm->ret();
        break;
      }
      case WASM_OP_BLOCK: {
        RD_U32();
        control_flow_label_t new_label;
        new_label.block_type = BLOCK;
        Xbyak::Label new_block_label;
        new_label.label = new_block_label;
        label_stack.push_front(new_label);
        break;
      }
      case WASM_OP_CALL: {
        uint32_t called_function_idx = RD_U32(); 
        const auto& called_label = function_header_labels[called_function_idx];
        int num_spilled_args = store_args_to_call(fn_asm, called_function_idx, module);
        fn_asm->call(called_label);
        fn_asm->add(Xbyak::util::rsp, num_spilled_args * 8);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::rax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_LOOP: {
        RD_U32();
        control_flow_label_t new_label;
        Xbyak::Label new_loop_label;

        new_label.block_type = LOOP;
        new_label.label = new_loop_label;

        fn_asm->L(new_label.label);
        label_stack.push_front(new_label);
        break;
      }
      case WASM_OP_BR: {
        uint32_t label = RD_U32();
        const auto& jump_label = label_stack[label];
        fn_asm->jmp(jump_label.label);
        break;
      }
      case WASM_OP_BR_IF: {
        uint32_t label = RD_U32();
        const auto& jump_label = label_stack[label];
        fn_asm->mov(Xbyak::util::r13, Xbyak::util::ptr [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 8);
        fn_asm->cmp(Xbyak::util::r13, 0);
        fn_asm->jne(jump_label.label, fn_asm->T_NEAR);
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
          fn_asm->cmp(Xbyak::util::r13, i); fn_asm->je(label_stack[table_labels[i]].label, fn_asm->T_NEAR);
        }
        fn_asm->jmp(label_stack[default_label].label, fn_asm->T_NEAR);
        break;
      }
      case WASM_OP_END: {
        control_flow_label_t patched_label = label_stack.front();
        if (patched_label.block_type != LOOP) {
          fn_asm->L(patched_label.label);
        }
        label_stack.pop_front();
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
        fn_asm->idiv(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::eax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_DIV_U: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::edx, 0);
        fn_asm->div(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::eax);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_REM_S: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->cdq();
        fn_asm->idiv(Xbyak::util::dword [Xbyak::util::rbx + 8]);
        fn_asm->add(Xbyak::util::rbx, 16);
        fn_asm->mov(Xbyak::util::qword [Xbyak::util::rbx], Xbyak::util::edx);
        fn_asm->sub(Xbyak::util::rbx, 8);
        break;
      }
      case WASM_OP_I32_REM_U: {
        fn_asm->mov(Xbyak::util::eax, Xbyak::util::dword [Xbyak::util::rbx + 16]);
        fn_asm->mov(Xbyak::util::edx, 0);
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
      default: {
        break;
      }
    }
  }
}

// RBX will store VFP. We will increment the VFP and load/store from there to push/pop off the stack. 
// R12 will store the base of the local/argument area, and we will dynamically load from this address based on local.get constant. 
// R13 is an intermediate register to take a local and then put it on the operand stack on VFP.
static JitEntry compile_function(bool is_main_fn, Code* cb, int function_index, WasmModule& module, std::vector<std::string>& args) {

  using namespace Xbyak::util;

  add_fn_prologue(cb, function_index, module);
  // if (is_main_fn) {
    // store_args(cb, function_index, module, args);
  // } else {
    // load_args(cb, function_index, module);
  // }
  load_args(cb, function_index, module);
  wasm_to_x86_loop(cb, function_index, module);
  move_ret_val(cb, function_index, module);
  add_fn_epilogue(cb, function_index, module);

  FILE* f = fopen("jit.bin", "wb");
  fwrite(cb->getCode(), 1, cb->getSize(), f);
  fclose(f);
  TRACE("HERE!");

  return cb->getCode<JitEntry>();
}

void jit(WasmModule& module, std::vector<std::string>& args) {
    using namespace Xbyak::util;
    auto cb = new Code(1<<15);

    FuncDecl* main_fn = find_main_function(module);
    int main_fn_idx = module.getFuncIdx(main_fn);

    for (int i = 0; i < module.Funcs().size(); i++) {
      Xbyak::Label new_label;
      function_header_labels.push_back(new_label);
    }

    store_args(cb, main_fn_idx, module, args);
    JitEntry fn = compile_function(true, cb, main_fn_idx, module, args);

    for (int i = 0; i < module.Funcs().size(); i++) {
      if (i != main_fn_idx) {
        auto compiled_fn = compile_function(false, cb, i, module, args);
      }
    }
    TRACE("End of jitting!\n");
    int result;

    try {
      result = fn();                          
    } catch (const Xbyak::Error& e) {
      return;
    } catch (...) {
      std::cerr << "Caught an unknown exception." << std::endl;
    }
    std::cout << result << "\n"; 
}