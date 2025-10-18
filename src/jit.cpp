#include <sstream>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cstring>
#include <getopt.h>
#include <numeric>

#include "wasmdefs.h"
#include "common.h"
#include "parse.h"
#include "ir.h"
#include "xbyak/xbyak.h"
#include "xbyak/xbyak_util.h"

struct Code : Xbyak::CodeGenerator {
  Code(size_t cap=1<<16) : Xbyak::CodeGenerator(cap) {}
};

extern FuncDecl* find_main_function(WasmModule& module);

using JitEntry = int (*)();

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
      case WASM_OP_I32_GE_U: 
      case WASM_OP_LOCAL_SET: {
        stack_size--;
        break;
      }
      case WASM_OP_NOP:
      case WASM_OP_I32_CLZ:
      case WASM_OP_I32_CTZ: 
      case WASM_OP_I32_POPCNT: {
        break;
      } 
      case WASM_OP_I32_CONST:
      case WASM_OP_LOCAL_GET: {
        RD_U32();
        stack_size++;
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
  fn_asm->push(rbp); 
  fn_asm->mov(rbp, rsp);
  fn_asm->push(rbx); 
  fn_asm->push(r12); 
  fn_asm->push(r13); 
  fn_asm->push(r14); 
  fn_asm->push(r15);
  fn_asm->mov(rbx, rsp);
  fn_asm->mov(r12, rsp);
  fn_asm->sub(rsp, (stack_size + params + num_locals) * 8);
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

void store_args(Code* fn_asm, int function_index, WasmModule& module, std::vector<std::string>& args) {
  using namespace Xbyak::util;
  auto params = module.getFunc(function_index)->sig->params;
  std::vector<wasm_type_t> param_vec(params.begin(), params.end());
  for (int i = 0; i < args.size(); i++) {
    switch (param_vec[i]) {
      case WASM_TYPE_I32: {
        fn_asm->mov(qword [rbx], stoi(args[i]));
        fn_asm->sub(rbx, 8);
        break;
      }
      case WASM_TYPE_F64: {
        fn_asm->mov(qword [rbx], stod(args[i]));
        fn_asm->sub(rbx, 8);
        break;
      }
    }
  }
}

void wasm_to_x86_loop(Code* fn_asm, int function_index, WasmModule& module) {
  auto code = module.getFunc(function_index)->code_bytes;

  buffer_t buf{
    .start = code.data(),
    .ptr   = code.data(),
    .end   = code.data() + code.size(),
  };

  buf.ptr = buf.start;
  while (buf.ptr != buf.end) {
    auto opcode = RD_OPCODE();
    switch (opcode) {
      case WASM_OP_I32_CONST: {
        int const_arg = RD_U32(); 
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

void move_ret_val(Code* fn_asm, int function_index, WasmModule& module) {
  using namespace Xbyak::util;
  auto ret_vals = module.getFunc(function_index)->sig->results;
  std::vector<wasm_type_t> ret_vec(ret_vals.begin(), ret_vals.end());
  if (ret_vec.size()) {
    TRACE("Moving return value!\n");
    fn_asm->mov(eax, dword [rbx + 8]);
  }
}

// RBX will store VFP. We will increment the VFP and load/store from there to push/pop off the stack. 
// R12 will store the base of the local/argument area, and we will dynamically load from this address based on local.get constant. 
// R13 is an intermediate register to take a local and then put it on the operand stack on VFP.
static JitEntry compile_function(int function_index, WasmModule& module, std::vector<std::string>& args) {

  using namespace Xbyak::util;
  auto cb = new Code(1<<15);

  add_fn_prologue(cb, function_index, module);
  store_args(cb, function_index, module, args);
  wasm_to_x86_loop(cb, function_index, module);
  move_ret_val(cb, function_index, module);
  // cb->mov(rax, 5);
  add_fn_epilogue(cb, function_index, module);

  FILE* f = fopen("jit.bin", "wb");
  fwrite(cb->getCode(), 1, cb->getSize(), f);
  fclose(f);

  return cb->getCode<JitEntry>();
}

void jit(WasmModule& module, std::vector<std::string>& args) {
    FuncDecl* main_fn = find_main_function(module);
    int main_fn_idx = module.getFuncIdx(main_fn);
    JitEntry fn = compile_function(main_fn_idx, module, args);
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