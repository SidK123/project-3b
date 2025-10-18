#include <sstream>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cstring>
#include <getopt.h>
#include <numeric>
#include <stack>
#include <variant>
#include <math.h>
#include <bit>

#include "jit.h"
#include "common.h"
#include "parse.h"
#include "ir.h"

static struct option long_options[] = {
  {"jit", no_argument, nullptr, 'j'},
  {"trace", no_argument,  &g_trace, 1},
  {"args", optional_argument, NULL, 'a'},
  {"help", no_argument, NULL, 'h'}
};

typedef struct args_t {
  std::string infile;
  std::vector<std::string> mainargs;
  bool jit_compiled;
} args_t;

typedef struct Table {
  int num_entries;
  std::vector<FuncDecl*> func_refs;
} Table;

typedef enum ctrl_flow_block_t {
  BLOCK, 
  LOOP,
  IF,
  IF_WITH_ELSE, 
  IF_NO_ELSE,
  ELSE,
  FN_END
} ctrl_flow_block_t; 

typedef struct Memory {
  bool has_max;
  int max; 
  int num_pages;
  std::vector<byte> memory_array;
} Memory;

std::stack<std::variant<int32_t, double>> value_stack;
std::stack<std::unordered_map<uint32_t, std::pair<wasm_type_t, std::variant<int32_t, double>>>> execution_stack;
std::unordered_map<uint32_t, std::unordered_map<uint32_t, std::pair<wasm_type_t, std::variant<int32_t, double>>>> var_to_value_map;  // Maps function to a map of var index to value.
std::unordered_map<uint32_t, std::tuple<bool, wasm_type_t, std::variant<int32_t, double>>> global_to_value_map;
std::unordered_map<uint32_t, std::unordered_map<long, std::pair<long, ctrl_flow_block_t>>> block_or_loop_target; // These are a list of targets for branches within a block, loop, or if/else.
std::unordered_map<uint32_t, std::unordered_map<long, long>> if_target; // These are targets for the if statements to go if they fail.
uint32_t glob_main_idx;
Memory memory; 
Table table;

args_t parse_args(int argc, char* argv[]) {
  int opt;
  args_t args;
  optind = 0;
  while ((opt = getopt_long_only(argc, argv, ":j:a:h", long_options, NULL)) != -1) {
    switch(opt) {
      case 0: break;
      case 'j': 
        args.jit_compiled = true; 
        break;
      case 'a':
        args.mainargs.push_back(optarg);
        while ((optind < (argc - 1))) {
          args.mainargs.push_back(argv[optind++]);
        }
        break;
      case 'h':
      default:
        ERR("Usage: %s [--trace (optional)] [-a <space-separated args>] <input-file>\n", argv[0]);
        exit(opt != 'h');
    }
  }

  if ( ((optind + 1) != argc)) {
    ERR("Executable takes one positional argument \"filename\"\n");
    exit(1);
  }

  args.infile = std::string(argv[optind]);
  return args;
}

void initialize_memory(WasmModule& module) {
  if (module.getMemorySize() > 0) {
    auto mem_list = module.getMemory(0);
    TRACE("Memory initial: %d!\n", mem_list->limits.initial);
    TRACE("Memory max: %d!\n", mem_list->limits.max);
    memory.memory_array.resize(mem_list->limits.initial * 65536);
    memory.num_pages = mem_list->limits.initial;
    memory.has_max = mem_list->limits.has_max;
    memory.max = mem_list->limits.max;
  } 
}

void initialize_data(WasmModule& module) {
  if (module.getDataSize() > 0) {
    for (int j = 0; j < module.getDataSize(); j++) {
      auto data_list = module.getData(j);
      for (int i = 0; i < data_list->bytes.size(); i++) {
        TRACE("Initializing byte %x in address %d!\n", data_list->bytes[i], data_list->mem_offset + i);
        memory.memory_array[data_list->mem_offset + i] = data_list->bytes[i];
      }
    }
  }
  return;
}

void initialize_table(WasmModule& module) {
  if (module.getTableSize() > 0) {
    auto data_list = module.getTable(0);
    table.num_entries = data_list->limits.initial;
    table.func_refs.resize(table.num_entries);
  }
}

void initialize_elems(WasmModule& module) {
  if (module.getElemsSize() > 0) {
    for (int i = 0; i < module.getElemsSize(); i++) {
      auto elem_list = module.getElems(i);
      auto it = elem_list->func_indices.begin();
      for (int j = 0; j < elem_list->func_indices.size(); j++) {
        table.func_refs[elem_list->table_offset + j] = *it;
        it++;
      }
    }
  }
}

int32_t grow_memory(uint32_t new_pages) {
  int old_pages = memory.num_pages;
  if (memory.has_max) {
    if (new_pages > memory.max || memory.num_pages + new_pages > memory.max) {
      return -1;
    }
  } 
  try {
    memory.memory_array.resize((memory.num_pages + new_pages) * 65536);
  } catch (const std::exception& e) {
      return -1;
  } catch (...) {
      std::cerr << "Caught an unknown exception." << std::endl;
  }
  memory.num_pages = memory.num_pages + new_pages;
  return old_pages;
}

int32_t get_mem_size() {
  return (memory.num_pages);
}

void check_out_of_bounds_access_two (uint32_t offset, uint32_t base_address) {
  if (offset > (memory.memory_array.size()) || base_address > (memory.memory_array.size())) {
    throw std::runtime_error("Out of bounds access!");
  }
}

void check_out_of_bounds_access (uint32_t address, int32_t num_bytes) {
  if (address > (memory.memory_array.size() - num_bytes)
      || address < 0) {
    throw std::runtime_error("Out of bounds access!");
  } 
}

int32_t load_i8(uint32_t address, bool signedness) { // True if signed, false if unsigned.
  check_out_of_bounds_access(address, 1);
  return (signedness ? static_cast<int8_t>(memory.memory_array[address]) : static_cast<uint32_t>(memory.memory_array[address]));
}

int32_t load_i16(uint32_t address, bool signedness) { // Sign extends the 16 bit int to int.
  check_out_of_bounds_access(address, 2);
  uint16_t result = 0; 
  for (int i = 0; i < 2; i++) {
    result |= ((memory.memory_array[address + i]) << (8 * i));
  }
  return (signedness ? static_cast<int16_t>(result) : static_cast<uint32_t>(result));
}

int32_t load_i32(uint32_t address) {
  check_out_of_bounds_access(address, 4);
  int32_t result = 0; 
  for (int i = 0; i < 4; i++) {
    result |= (memory.memory_array[address + i]) << (8 * i);
  }
  return result;
}

double load_f64(uint32_t address) {
  check_out_of_bounds_access(address, 8);
  uint64_t int_result = 0;
  for (int i = 0; i < 8; i++) {
    int_result |= (static_cast<uint64_t>(memory.memory_array[address + i]) << (8 * i));
  }
  double result = std::bit_cast<double>(int_result);
  return result;
}

int32_t store_i8(uint32_t address, int32_t store_value) {
  check_out_of_bounds_access(address, 1);
  memory.memory_array[address] = static_cast<uint8_t>(store_value);
  return 0;
}

int32_t store_i16(uint32_t address, int32_t store_value) {
  check_out_of_bounds_access(address, 2);
  for (int i = 0; i < 2; i++) {
    memory.memory_array[address + i] = static_cast<uint8_t>((store_value & (0xFF << (i * 8))) >> (8 * i));
  }
  return 0;
}

int32_t store_i32(uint32_t address, int32_t store_value) {
  check_out_of_bounds_access(address, 4);
  TRACE("Store value is %d!\n", store_value);
  for (int i = 0; i < 4; i++) {
    memory.memory_array[address + i] = (store_value & (0xFF << (i * 8))) >> (8 * i);
  }
  return 0;
}

int32_t store_f64(uint32_t address, double store_value) {
  check_out_of_bounds_access(address, 8);
  for (int i = 0; i < 8; i++) {
    memory.memory_array[address + i] = static_cast<uint8_t>(((std::bit_cast<uint64_t>(store_value)) & (0xFFL << (i * 8))) >> (8 * i));
  }
  return 0;
}

void execute_i32_casts(byte opcode) {
  TRACE("Executing i32 casts!\n");
  switch (opcode) {
    case WASM_OP_I32_TRUNC_F64_S: {
      auto operand = std::get<double>(value_stack.top());
      if (!std::isfinite(operand)|| operand <= (static_cast<double>(INT_MIN) - 1L) || operand >= (static_cast<double>(INT_MAX) + 1L)) {
        throw std::runtime_error("Float is unrepresentable as a signed int!");
      } 
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(std::trunc(operand)));
      break;
    }
    case WASM_OP_I32_TRUNC_F64_U: {
      auto operand = std::get<double>(value_stack.top());
      if (!std::isfinite(operand) || operand <= -1 || operand >= (static_cast<double>(UINT_MAX) + 1L)) {
        throw std::runtime_error("Float is unrepresentable as an unsigned int!");
      } 
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(static_cast<uint32_t>(std::trunc(operand))));
      break;
    } 
    case WASM_OP_I32_EXTEND8_S: {
      int8_t operand = static_cast<int8_t>(std::get<int32_t>(value_stack.top()));
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand));
      break;
    }
    case WASM_OP_I32_EXTEND16_S: {
      int16_t operand = static_cast<int16_t>(std::get<int32_t>(value_stack.top()));
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand));
      break;
    }
  }
}

void execute_i32_arithmetic(byte opcode) {
  TRACE("Executing i32 arithmetic!\n");
  auto operand1 = std::get<int32_t>(value_stack.top());
  value_stack.pop();
  auto u_operand1 = static_cast<uint32_t>(operand1);
  switch(opcode) {
    case WASM_OP_I32_CLZ: {
      for (int i = 31; i >= 0; i--) {
        if (operand1 & (0x1 << i)) {
          value_stack.push(31-i);
          break;
        } else if (i == 0) {
          value_stack.push(32);
        }
      } 
      return;
    }
    case WASM_OP_I32_CTZ: {
      for (int i = 0; i < 32; i++) {
        if (operand1 & (0x1 << i)) {
          value_stack.push(i);
          break;
        } else if (i == 31) {
          value_stack.push(32);
        }
      } 
      return;
    }
    case WASM_OP_I32_POPCNT: {
      int num_ones = 0;
      for (int i = 0; i < 32; i++) {
        if (operand1 & (0x1 << i)) {
          num_ones++;
        }
      }
      value_stack.push(num_ones);
      return;
    }
    default: {
      break;
    }
  }
  auto operand2 = std::get<int32_t>(value_stack.top());
  auto u_operand2 = static_cast<uint32_t>(operand2);
  value_stack.pop();
  switch(opcode) {
    case WASM_OP_I32_ADD: {
      TRACE("Pushing %d onto the stack.\n", (operand1 + operand2));
      value_stack.push(operand1 + operand2);
      break;
    }
    case WASM_OP_I32_SUB: {
      value_stack.push(operand2 - operand1);
      break;
    }
    case WASM_OP_I32_MUL: {
      value_stack.push(operand2 * operand1);
      break;
    }
    case WASM_OP_I32_DIV_S: {
      if (u_operand1 == 0) {
        throw std::runtime_error("Trying to divide by 0!");
      } else if (u_operand1 == -1 && u_operand2 == INT_MIN) {
        throw std::runtime_error("Trying to divide int min by -1!");
      }
      value_stack.push(operand2 / operand1);
      break;
    }
    case WASM_OP_I32_DIV_U: {
      if (u_operand1 == 0) {
        throw std::runtime_error("Trying to divide by 0!");
      }
      value_stack.push(static_cast<int32_t>(u_operand2 / u_operand1));
      break;
    }
    case WASM_OP_I32_REM_S: {
      if (operand1 == 0) {
        throw std::runtime_error("Trying to do remainder by 0!");
      } else if (operand2 == INT_MIN && operand1 == -1) {
        value_stack.push(0);
      } else {
        value_stack.push(operand2 % operand1);
      }
      break;
    }
    case WASM_OP_I32_REM_U: {
      if (u_operand1 == 0) {
        throw std::runtime_error("Trying to do remainder by 0!");
      }
      value_stack.push(static_cast<int32_t>(u_operand2 % u_operand1));
      break;
    }
    case WASM_OP_I32_AND: {
      value_stack.push(operand2 & operand1);
      break;
    }
    case WASM_OP_I32_OR: {
      value_stack.push(operand2 | operand1);
      break;
    }
    case WASM_OP_I32_XOR: {
      value_stack.push(operand2 ^ operand1);
      break;
    }
    case WASM_OP_I32_SHL: {
      value_stack.push(operand2 << (operand1 % 32));
      break;
    }
    case WASM_OP_I32_SHR_S: {
      value_stack.push(operand2 >> (operand1 % 32));
      break;
    }
    case WASM_OP_I32_SHR_U: {
      value_stack.push(static_cast<int32_t>(u_operand2 >> (u_operand1 % 32)));
      break;
    }
    case WASM_OP_I32_ROTR: {
      int32_t final_result = (static_cast<uint32_t>(operand2) >> (operand1 % 32)) | (operand2 << (32 - (operand1 % 32)));
      value_stack.push(final_result);
      break;
    }
    case WASM_OP_I32_ROTL: {
      int32_t final_result = (operand2 << (operand1 % 32)) | (static_cast<uint32_t>(operand2) >> (32 - (operand1 % 32)));
      value_stack.push(final_result);
      break;
    }
  }
} 

void execute_i32_comparison(byte opcode) {
  TRACE("Executing i32 comparison!\n");
  auto operand1 = std::get<int32_t>(value_stack.top());
  value_stack.pop();
  auto u_operand1 = static_cast<uint32_t>(operand1);
  switch(opcode) {
    case WASM_OP_I32_EQZ: {
      value_stack.push(static_cast<int32_t>(operand1 == 0));
      break;
    }
    default: {
      break;
    }
  }
  auto operand2 = std::get<int32_t>(value_stack.top());
  auto u_operand2 = static_cast<uint32_t>(operand2);
  switch(opcode) {
    case WASM_OP_I32_EQ: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand1 == operand2));
      break;
    }
    case WASM_OP_I32_NE: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand1 != operand2));
      break;
    }
    case WASM_OP_I32_LT_S: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand2 < operand1));
      break;
    }
    case WASM_OP_I32_LT_U: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(u_operand2 < u_operand1));
      break;
    }
    case WASM_OP_I32_GT_S: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand2 > operand1)); 
      break;
    }
    case WASM_OP_I32_GT_U: {
      value_stack.pop();
      TRACE("Comparing value %d > %d!", u_operand2, u_operand1);
      value_stack.push(static_cast<int32_t>(u_operand2 > u_operand1)); 
      break;
    }
    case WASM_OP_I32_LE_S: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand2 <= operand1)); 
      break;
    }
    case WASM_OP_I32_LE_U: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(u_operand2 <= u_operand1)); 
      break;
    }
    case WASM_OP_I32_GE_S: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(operand2 >= operand1));
      break;
    }
    case WASM_OP_I32_GE_U: {
      value_stack.pop();
      value_stack.push(static_cast<int32_t>(u_operand2 >= u_operand1));
      break;
    }
  }
} 

void execute_f64_arithmetic(byte opcode) {
  TRACE("Executing f64 arithmetic!\n");
  auto operand1 = std::get<double>(value_stack.top());
  value_stack.pop();
  switch(opcode) {
    case WASM_OP_F64_ABS: {
      value_stack.push(abs(operand1));
      break;
    }
    case WASM_OP_F64_NEG: {
      value_stack.push(-operand1);
      break;
    }
    case WASM_OP_F64_CEIL: {
      value_stack.push(ceil(operand1));
      break;
    }
    case WASM_OP_F64_FLOOR: {
      value_stack.push(floor(operand1));
      break;
    }
    case WASM_OP_F64_TRUNC: {
      value_stack.push(std::trunc(operand1));
      break;
    }
    case WASM_OP_F64_NEAREST: {
      value_stack.push(std::round(operand1));
      break;
    }
    case WASM_OP_F64_SQRT: {
      value_stack.push(sqrt(operand1));
      break;
    }
    case WASM_OP_F64_ADD: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(operand2 + operand1);
      break;
    }
    case WASM_OP_F64_SUB: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(operand2 - operand1);
      break;
    }
    case WASM_OP_F64_MUL: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(operand2 * operand1);
      break;
    }
    case WASM_OP_F64_DIV: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(operand2 / operand1);
      break;
    }
    case WASM_OP_F64_MIN: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(std::min(operand2, operand1));
      break;
    }
    case WASM_OP_F64_MAX: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      value_stack.push(std::max(operand2, operand1));
      break;
    }
    case WASM_OP_F64_COPYSIGN: {
      auto operand2 = std::get<double>(value_stack.top());
      value_stack.pop();
      if (operand1 < 0) {
        value_stack.push(-std::abs(operand2));
      } else {
        value_stack.push(std::abs(operand2));
      }
      break;
    }
  }
}

void execute_f64_casts(byte opcode) { 
  auto operand = std::get<int32_t>(value_stack.top());
  value_stack.pop();
  switch (opcode) {
    case WASM_OP_F64_CONVERT_I32_S: {
      value_stack.push(static_cast<double>(operand));
      break;
    }
    case WASM_OP_F64_CONVERT_I32_U: {
      value_stack.push(static_cast<double>(static_cast<uint32_t>(operand)));
      break;
    }
  } 
}

void execute_f64_comparison(byte opcode){
  TRACE("Executing f64 comparison!\n");
  auto operand1 = std::get<double>(value_stack.top());
  value_stack.pop();
  auto operand2 = std::get<double>(value_stack.top());
  value_stack.pop();
  switch(opcode) {
    case WASM_OP_F64_EQ: {
      value_stack.push(static_cast<int32_t>(operand1 == operand2));
      break;
    }
    case WASM_OP_F64_NE: { 
      value_stack.push(static_cast<int32_t>(operand1 != operand2));
      break;
    }
    case WASM_OP_F64_LT: {
      value_stack.push(static_cast<int32_t>(operand2 < operand1));
      break;
    } 
    case WASM_OP_F64_GT: {
      value_stack.push(static_cast<int32_t>(operand2 > operand1));
      break;
    }
    case WASM_OP_F64_LE: {
      value_stack.push(static_cast<int32_t>(operand2 <= operand1));
      break;
    }
    case WASM_OP_F64_GE: {
      value_stack.push(static_cast<int32_t>(operand2 >= operand1));
      break;
    }
  }
}

void add_locals_to_map(int fn_idx, WasmModule& module) {
  FuncDecl* fn = module.getFunc(fn_idx);
  SigDecl* sig = module.getSig(fn_idx);
  int param_count = fn->sig->params.size();
  for (auto local = fn->pure_locals.begin(); local != fn->pure_locals.end(); ++local) {
    for (int i = 0; i < local->count; i++) {
      switch (local->type) { 
        case WASM_TYPE_I32: 
          TRACE("Setting local %d to type %d!\n", param_count, local->type);
          var_to_value_map[fn_idx][param_count] = std::pair(local->type, 0); 
          break;
        case WASM_TYPE_F64:
          var_to_value_map[fn_idx][param_count] = std::pair(local->type, 0.0);
          break;
        default:
          throw std::runtime_error("Unimplemented types for pure locals!");
        }
      param_count++;
    }
  }
}

void set_arbitrary_function_args(WasmModule& module, int function_index) {
  if (value_stack.empty()) {
    return;
  }
  typelist params = module.getFunc(function_index)->sig->params;
  std::stack<std::variant<int32_t, double>> reversed_stack;
  TRACE("Called function index is %d, number of params is %d!\n", function_index, module.getFunc(function_index)->sig->num_params);
  uint32_t param_index  = 0;
  uint32_t params_count = params.size(); 

  for (int i = 0; i < params_count; i++) {
    reversed_stack.push(value_stack.top());
    value_stack.pop();
  }

  for (auto it = params.begin(); it != params.end(); ++it) {
    TRACE("Adding param %d to function value map, which is of type %x!\n", param_index, *it);
    var_to_value_map[function_index][param_index].first = *it;
    var_to_value_map[function_index][param_index].second = reversed_stack.top();
    reversed_stack.pop();
    param_index++; 
  }
}

void block_loop_analysis_pass(WasmModule& module, int function_index, std::vector<byte>& code) {
  TRACE("In block and loop analysis pass!\n");

  buffer_t buf {
    .start = code.data(),
    .ptr   = code.data(),
    .end   = code.data() + code.size(), 
  };

  std::deque<std::pair<long, ctrl_flow_block_t>> control_stack; // False for block, and true for loop. TODO: Should actually be an enum.

  while (buf.ptr && buf.ptr < buf.end) {
    Opcode_t curr_instr = static_cast<Opcode_t>(RD_BYTE());
    switch (curr_instr) {
      case WASM_OP_UNREACHABLE:
      case WASM_OP_NOP:
      case WASM_OP_RETURN:
      case WASM_OP_DROP:
      case WASM_OP_SELECT:
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
      case WASM_OP_I32_EQZ:
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
      case WASM_OP_I32_ROTL:
      case WASM_OP_I32_ROTR:
      case WASM_OP_I32_CLZ:
      case WASM_OP_I32_CTZ:
      case WASM_OP_I32_POPCNT:
      case WASM_OP_I32_TRUNC_F64_S:
      case WASM_OP_I32_TRUNC_F64_U:
      case WASM_OP_I32_EXTEND8_S:
      case WASM_OP_I32_EXTEND16_S: 
      case WASM_OP_F64_ABS:
      case WASM_OP_F64_NEG:
      case WASM_OP_F64_CEIL:
      case WASM_OP_F64_FLOOR:
      case WASM_OP_F64_TRUNC:
      case WASM_OP_F64_NEAREST:
      case WASM_OP_F64_SQRT:
      case WASM_OP_F64_ADD:
      case WASM_OP_F64_SUB:
      case WASM_OP_F64_MUL:
      case WASM_OP_F64_DIV:
      case WASM_OP_F64_MIN:
      case WASM_OP_F64_MAX:
      case WASM_OP_F64_COPYSIGN:
      case WASM_OP_F64_EQ:
      case WASM_OP_F64_NE:
      case WASM_OP_F64_LT:
      case WASM_OP_F64_GT:
      case WASM_OP_F64_LE:
      case WASM_OP_F64_GE: 
      case WASM_OP_F64_CONVERT_I32_S: 
      case WASM_OP_F64_CONVERT_I32_U: {
        break;
      }

      case WASM_OP_LOCAL_GET: 
      case WASM_OP_LOCAL_SET: 
      case WASM_OP_LOCAL_TEE: 
      case WASM_OP_GLOBAL_GET: 
      case WASM_OP_GLOBAL_SET:
      case WASM_OP_BR:
      case WASM_OP_BR_IF:
      case WASM_OP_CALL: { 
        RD_U32();
        break;
      }

      case WASM_OP_MEMORY_GROW:
      case WASM_OP_MEMORY_SIZE: {
        RD_BYTE();
        break;
      }

      case WASM_OP_CALL_INDIRECT: {
        RD_U32();
        RD_BYTE();
        break;
      }

      case WASM_OP_BR_TABLE: {
        uint32_t number_of_labels = RD_U32();
        for (int i = 0; i < number_of_labels; i++) {
          RD_U32();
        }
        RD_U32();
        break;
      }

      case WASM_OP_I32_CONST: {
        RD_I32();
        break;
      }

      case WASM_OP_F64_CONST: {
        RD_U64_RAW();
        break;
      }

      case WASM_OP_I32_LOAD8_S:
      case WASM_OP_I32_LOAD8_U:
      case WASM_OP_I32_LOAD16_S:
      case WASM_OP_I32_LOAD16_U:
      case WASM_OP_I32_LOAD:
      case WASM_OP_I32_STORE:
      case WASM_OP_I32_STORE8:
      case WASM_OP_I32_STORE16: 
      case WASM_OP_F64_LOAD:
      case WASM_OP_F64_STORE: {
        RD_U32();
        RD_U32();
        break;
      }

      case WASM_OP_BLOCK: {
        RD_U32();
        control_stack.push_front(std::make_pair(buf.ptr - buf.start, BLOCK));
        TRACE("New block added, its address is %p.\n", buf.ptr);
        break;
      }
      case WASM_OP_LOOP: {
        RD_U32();
        control_stack.push_front(std::make_pair(buf.ptr - buf.start, LOOP));
        block_or_loop_target[function_index][buf.ptr - buf.start] = std::make_pair(buf.ptr - buf.start, LOOP);
        TRACE("New loop added, its address is %p.\n", buf.ptr);
        break;
      }
      case WASM_OP_IF: {
        RD_U32();
        control_stack.push_front(std::make_pair(buf.ptr - buf.start, IF));
        TRACE("New if added, its address is %p.\n", buf.ptr);
        break;
      } 
      case WASM_OP_ELSE: {
        auto corresponding_if = control_stack.front().first; 
        if_target[function_index][corresponding_if] = buf.ptr - buf.start;
        TRACE("Setting target of if in the case condition is not satisfied to be %p!\n", buf.ptr);
        control_stack.push_front(std::make_pair(buf.ptr - buf.start, ELSE));
        TRACE("New else added, its address is %p.\n", buf.ptr);
        break;
      }
      case WASM_OP_END: {
        if (control_stack.empty()) {
          block_or_loop_target[function_index][0] = std::make_pair(buf.ptr - buf.start, FN_END);
          return;
        }
        auto stack_top = control_stack.front();
        if (stack_top.second == BLOCK) {
          TRACE("Setting target of block at %p equal to %p!\n", (stack_top.first + buf.start), (buf.ptr));
          block_or_loop_target[function_index][stack_top.first] = std::make_pair(buf.ptr - buf.start, stack_top.second);
        } else if (stack_top.second == IF) {
          TRACE("Setting target of if at %p equal to %p!\n", (stack_top.first + buf.start), (buf.ptr));
          block_or_loop_target[function_index][stack_top.first] = std::make_pair(buf.ptr - buf.start, IF_NO_ELSE);
          auto corresponding_if = control_stack.front().first; 
          if_target[function_index][corresponding_if] = buf.ptr - buf.start;
        } else if (stack_top.second == ELSE) {
          TRACE("Setting target of else at %p equal to %p!\n", (stack_top.first + buf.start), (buf.ptr)); // For a well formed program, the END of an ELSE should be the END of the IF which should be right above the else on the stack.
          block_or_loop_target[function_index][stack_top.first] = std::make_pair(buf.ptr - buf.start, stack_top.second); 
          control_stack.pop_front();
          stack_top = control_stack.front();
          TRACE("Setting target of if at %p equal to %p!\n", (stack_top.first + buf.start), (buf.ptr)); // For a well formed program, the END of an ELSE should be the END of the IF which should be right above the else on the stack.
          block_or_loop_target[function_index][stack_top.first] = std::make_pair(buf.ptr - buf.start, IF_WITH_ELSE);
        }
        control_stack.pop_front();
        break;
      }
      default:
        break;
    }
  }
  TRACE("At the end of the function!");
}

void execute_puti() {
  int value_to_print = std::get<int>(value_stack.top());
  value_stack.pop();
  std::cout << value_to_print;
}

void execute_putd() {
  double value_to_print = std::get<double>(value_stack.top());
  value_stack.pop();
  std::cout << std::fixed << std::setprecision(6) << value_to_print;
}

void execute_put() {
  int string_length = std::get<int>(value_stack.top());
  value_stack.pop();
  int base_address = std::get<int>(value_stack.top());
  value_stack.pop();
  check_out_of_bounds_access(base_address, string_length);
  char string_to_print[string_length];
  for (int i = 0; i < string_length; i++) {
    string_to_print[i] = memory.memory_array[base_address + i];
  }
  std::cout << string_to_print;
}

void execute_weewasm_functions(WasmModule& module, std::string& fn_name) {
  if (fn_name == "puti") {
    execute_puti();
  } else if (fn_name == "putd") {
    execute_putd();
  } else if (fn_name == "put") {
    execute_put();
  } 
}

void call_imported_function(WasmModule& module, int function_index) {
  auto imports = module.Imports();
  for (auto it = imports.list.begin(); it != imports.list.end(); ++it) {
    auto import = *it;
    if (module.getFunc(function_index) == import.desc.func && (import.mod_name == "weewasm")) {
      execute_weewasm_functions(module, import.member_name);
    } 
  }
}

void instruction_execution(WasmModule& module, int function_index, std::vector<byte>& code) {
  TRACE("Currently executing code for function index %d!\n", function_index);
  std::deque<long> control_stack; // False for block, and true for loop. TODO: Should actually be an enum.
  uint32_t curr_virtual_pc = 0;
  if (function_index != -1) {
    set_arbitrary_function_args(module, function_index);
    add_locals_to_map(function_index, module);
  }

  for (auto& byte : code) {
    TRACE("Looking at byte: %x!\n", byte);
  }

  block_loop_analysis_pass(module, function_index, code);

  buffer_t buf{
    .start = code.data(),
    .ptr   = code.data(),
    .end   = code.data() + code.size(),
  };

  buf.ptr = buf.start;

  control_stack.push_front(buf.ptr - buf.start); // Initial block, as if we see an end, we should quit.

  while (buf.ptr && buf.ptr < buf.end) {
    Opcode_t curr_instr = RD_OPCODE();
    switch (curr_instr) {
      case WASM_OP_NOP: {
        TRACE("Looking at a nop! \n");
        break;
      }
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
      case WASM_OP_I32_CLZ:
      case WASM_OP_I32_CTZ:
      case WASM_OP_I32_POPCNT:
      { 
        execute_i32_arithmetic(static_cast<byte>(curr_instr));
        break;
      }

      case WASM_OP_I32_TRUNC_F64_S:
      case WASM_OP_I32_TRUNC_F64_U:
      case WASM_OP_I32_EXTEND8_S:
      case WASM_OP_I32_EXTEND16_S:
      {
        execute_i32_casts(static_cast<byte>(curr_instr));
        break;
      } 

      case WASM_OP_I32_EQZ:
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
        execute_i32_comparison(static_cast<byte>(curr_instr));
        break;
      }

      case WASM_OP_F64_ABS:
      case WASM_OP_F64_NEG:
      case WASM_OP_F64_CEIL:
      case WASM_OP_F64_FLOOR:
      case WASM_OP_F64_TRUNC:
      case WASM_OP_F64_NEAREST:
      case WASM_OP_F64_SQRT:
      case WASM_OP_F64_ADD:
      case WASM_OP_F64_SUB:
      case WASM_OP_F64_MUL:
      case WASM_OP_F64_DIV:
      case WASM_OP_F64_MIN:
      case WASM_OP_F64_MAX:
      case WASM_OP_F64_COPYSIGN: {
        execute_f64_arithmetic(static_cast<byte>(curr_instr));
        break;
      }

      case WASM_OP_F64_CONVERT_I32_S: 
      case WASM_OP_F64_CONVERT_I32_U: {
        execute_f64_casts(static_cast<byte>(curr_instr));
        break;
      }

      case WASM_OP_F64_EQ:
      case WASM_OP_F64_NE:
      case WASM_OP_F64_LT:
      case WASM_OP_F64_GT:
      case WASM_OP_F64_LE:
      case WASM_OP_F64_GE: {
        execute_f64_comparison(static_cast<byte>(curr_instr));
        break;
      }

      case WASM_OP_LOCAL_GET: {
        TRACE("Looking at a local_get!\n");
        uint32_t idx = RD_U32();
        switch (var_to_value_map[function_index][idx].first) {
          case WASM_TYPE_I32:
            value_stack.push(std::get<int32_t>(var_to_value_map[function_index][idx].second));
            break;
          case WASM_TYPE_F64:
            value_stack.push(std::get<double>(var_to_value_map[function_index][idx].second));
            break;
          default:
            throw std::runtime_error("Trying to local.set on a variable of an unsupported type!");
        }
        break;
      } 

      case WASM_OP_LOCAL_SET: {
        TRACE("Looking at a local set!\n");
        uint32_t idx = RD_U32();                
        switch (var_to_value_map[function_index][idx].first) {
          case WASM_TYPE_I32:
            var_to_value_map[function_index][idx].second = std::get<int32_t>(value_stack.top());
            break;
          case WASM_TYPE_F64:
            var_to_value_map[function_index][idx].second = std::get<double>(value_stack.top());
            break;
          default:
            throw std::runtime_error("Trying to local.set on a variable of an unsupported type!");
        }
        value_stack.pop();
        break;
      }

      case WASM_OP_LOCAL_TEE: {
        TRACE("Looking at a local tee!\n");
        uint32_t idx = RD_U32();                
        switch (var_to_value_map[function_index][idx].first) {
          case WASM_TYPE_I32:
            var_to_value_map[function_index][idx].second = std::get<int32_t>(value_stack.top());
            break;
          case WASM_TYPE_F64:
            var_to_value_map[function_index][idx].second = std::get<double>(value_stack.top());
            break;
          default:
            throw std::runtime_error("Trying to local.set on a variable of an unsupported type!"); 
        }
        break;
      }

      case WASM_OP_GLOBAL_GET: {
        TRACE("Looking at a global get!\n");
        uint32_t idx = RD_U32();
        value_stack.push(std::get<2>(global_to_value_map[idx]));
        break;
      }

      case WASM_OP_GLOBAL_SET: {
        uint32_t idx = RD_U32();
        std::get<2>(global_to_value_map[idx]) = value_stack.top();
        value_stack.pop();
        break;
      }

      case WASM_OP_I32_CONST: {
        int32_t constant = RD_I32();                 
        TRACE("Looking at an i32 const: %d!\n", constant);
        value_stack.push(constant);
        break;
      }

      case WASM_OP_F64_CONST: {
        TRACE("Looking at an f64 const!\n");
        uint64_t bits = RD_U64_RAW();            
        double d;
        memcpy(&d, &bits, sizeof(d));            
        value_stack.push(d);
        break;
      }

      case WASM_OP_I32_LOAD8_S: {
        TRACE("Looking at an i32.i8_s load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        int32_t loaded_int = load_i8(offset+base_address, true);
        TRACE("Loaded value %d in i8_s!\n", loaded_int);
        value_stack.push(loaded_int);
        break;
      }

      case WASM_OP_I32_LOAD8_U: {
        TRACE("Looking at an i32.i8_u load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        int32_t loaded_int = load_i8(offset+base_address, false);
        TRACE("Loaded value %d in i8_u!\n", loaded_int);
        value_stack.push(loaded_int);
        break;
      }

      case WASM_OP_I32_LOAD16_S: {
        TRACE("Looking at an i32.i16_s load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        int32_t loaded_int = load_i16(offset+base_address, true);
        TRACE("Loaded value %d in i16_s!\n", loaded_int);
        value_stack.push(loaded_int);
        break;
      }

      case WASM_OP_I32_LOAD16_U: {
        TRACE("Looking at an i32.i16_u load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        int32_t loaded_int = load_i16(offset+base_address, false);
        TRACE("Loaded value %d in i16_u!\n", loaded_int);
        value_stack.push(loaded_int);
        break;
      }

      case WASM_OP_I32_LOAD: {
        TRACE("Looking at an i32 load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        TRACE("Loading from address: %d!\n", (offset + base_address));
        check_out_of_bounds_access_two(offset, base_address);
        int32_t loaded_int = load_i32(offset+base_address);
        value_stack.push(loaded_int);
        break;
      }

      case WASM_OP_I32_STORE: {
        TRACE("Looking at an i32 store!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        int32_t value = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        uint32_t address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top())); 
        value_stack.pop();
        TRACE("Storing value %d to address %d.\n", value, address);
        store_i32(address + offset, value);
        break;
      }

      case WASM_OP_I32_STORE8: {
        TRACE("Looking at an i32 store 8!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        int32_t value = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        uint32_t address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop(); 
        TRACE("Storing value %d to address %d as one byte.\n", static_cast<uint8_t>(value), address); 
        store_i8(address + offset, value);
        break;
      }

      case WASM_OP_I32_STORE16: {
        TRACE("Looking at an i32 store 16!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        int32_t value = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        uint32_t address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop(); 
        TRACE("Storing value %d to address %d as two bytes.\n", static_cast<uint8_t>(value), address); 
        store_i16(address + offset, value);
        break;
      }

      case WASM_OP_F64_LOAD: {
        TRACE("Looking at an f64 load!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        uint32_t base_address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop();
        double loaded_double = load_f64(offset+base_address);
        value_stack.push(loaded_double);
        break;
      }

      case WASM_OP_F64_STORE: {
        TRACE("Looking at an f64 store!\n");
        uint32_t align = RD_U32();
        uint32_t offset = RD_U32();
        double value = std::get<double>(value_stack.top()); 
        value_stack.pop();
        uint32_t address = static_cast<uint32_t>(std::get<int32_t>(value_stack.top())); 
        value_stack.pop();
        TRACE("Storing value %f to address %d.\n", value, address);
        store_f64(address + offset, value);
        break;
      }

      case WASM_OP_MEMORY_SIZE: {
        int32_t mem_size = get_mem_size();
        value_stack.push(mem_size);
        RD_BYTE();
        break;
      } 

      case WASM_OP_MEMORY_GROW: {
        uint32_t delta_size = static_cast<uint32_t>(std::get<int32_t>(value_stack.top()));
        value_stack.pop(); 
        value_stack.push(grow_memory(delta_size));
        RD_BYTE();
        break;
      }

      case WASM_OP_SELECT: {
        int32_t select = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        auto operand1 = value_stack.top();
        value_stack.pop();
        auto operand2 = value_stack.top(); 
        value_stack.pop();
        (select == 0) ? value_stack.push(operand1) : value_stack.push(operand2);
        break;
      }

      case WASM_OP_DROP: {
        value_stack.pop();
        break;
      }

      case WASM_OP_UNREACHABLE: {
        throw std::runtime_error("Should not be executing code that is unreachable!");
        break;
      } 

      case WASM_OP_RETURN: {
        return;
      }
      
      case WASM_OP_CALL_INDIRECT: {
        int32_t table_index = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        if (table.num_entries <= table_index || table_index < 0) {
          TRACE("Index was out of bounds, number of entries was %d, table index was %d!\n", table.num_entries, table_index);
          throw std::runtime_error("Index out of bounds!");
        }
        auto called_function = table.func_refs[table_index];
        uint32_t type_index = RD_U32();
        RD_BYTE(); // 0 byte
        if (called_function == NULL) {
          TRACE("Called function is NULL!\n");
          throw std::runtime_error("Called function does not have the same type as type index indicates!");
        } else if (module.getSig(type_index) != called_function->sig) {
          TRACE("Signature does not match!\n");
          throw std::runtime_error("Called function does not have the same type as type index indicates!");
        } 
        execution_stack.push(var_to_value_map[function_index]);
        if (module.isImport(called_function)) {
          call_imported_function(module, module.getFuncIdx(called_function));
        } else {
          instruction_execution(module, module.getFuncIdx(called_function), called_function->code_bytes);
        }
        var_to_value_map[function_index] = execution_stack.top();
        execution_stack.pop();
        break;
      } 

      case WASM_OP_CALL: {
        uint32_t called_function_idx = RD_U32();
        TRACE("Calling function with index %d!\n", called_function_idx);
        execution_stack.push(var_to_value_map[function_index]);
        if (module.isImport(module.getFunc(called_function_idx))) {
          call_imported_function(module, called_function_idx);
        } else {
          instruction_execution(module, called_function_idx, module.getFunc(called_function_idx)->code_bytes);
        }
        var_to_value_map[function_index] = execution_stack.top();
        execution_stack.pop();
        break;
      }

      case WASM_OP_LOOP:
      case WASM_OP_BLOCK: {
        RD_U32(); // Shouldn't matter all that much, as the block type is not being used here.
        TRACE("Looking at a BLOCK at address %p!\n", buf.ptr);
        control_stack.push_front(buf.ptr - buf.start);
        break;
      }

      case WASM_OP_IF: {
        RD_U32(); // Shouldn't matter all that much, as the block type is not being used here.
        TRACE("Looking at an IF at address %p!\n", (buf.ptr));
        int32_t condition = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        long offset = if_target[function_index][buf.ptr - buf.start];
        ctrl_flow_block_t if_type = block_or_loop_target[function_index][buf.ptr-buf.start].second;
        if (condition == 0) {
          buf.ptr = buf.start + offset;
          TRACE("Pushing buf ptr %p!\n", buf.ptr);
          if (if_type == IF_WITH_ELSE) {
            control_stack.push_front(buf.ptr - buf.start); // Pushing the ELSE to the stack. 
          }  
        } else {
          TRACE("Pushing buf ptr %p!\n", buf.ptr);
          control_stack.push_front(buf.ptr - buf.start); // Pushing the IF to the stack. 
        }
        break;
      }

      case WASM_OP_ELSE: { // Will never be seen unless the IF case was executed, as we always jump to the instruction right after the else, so we can safely ignore this and jump to the end.
        long if_pc = control_stack.front();
        control_stack.pop_front();
        TRACE("Looking up the offset of %ld!\n", if_pc);
        long offset = block_or_loop_target[function_index][if_pc].first; // The END label should be the same for the IF and the ELSE.
        buf.ptr = buf.start + offset; // Automatically go to instruction after END.
        TRACE("Setting buf ptr to be %p\n", buf.ptr);
        break;
      }

      case WASM_OP_END: {
        control_stack.pop_front();
        if (control_stack.empty()) {
          TRACE("Returning from function!\n");
          return;
        }
        break;
      }

      case WASM_OP_BR: {
        TRACE("Looking at a BR!\n");
        uint32_t label = RD_U32();
        long offset = block_or_loop_target[function_index][control_stack[label]].first;
        buf.ptr = buf.start + (offset);
        TRACE("We are setting the buffer pointer to %p.\n", buf.ptr);
        uint32_t pop_depth = (block_or_loop_target[function_index][control_stack[label]].second == LOOP) ? label : label + 1;
        for (int i = 0; i < control_stack.size(); i++) {
          TRACE("Offset in vector is %lu!\n", control_stack[i]);
        }
        for (int i = 0; i < pop_depth; i++) {
          TRACE("Popping off control flow block with address %p!\n", (control_stack.front() + buf.start));
          control_stack.pop_front();
        }
        break;
      }

      case WASM_OP_BR_IF: {
        uint32_t label = RD_U32();
        long offset = block_or_loop_target[function_index][control_stack[label]].first;
        bool condition = (std::get<int32_t>(value_stack.top()) != 0);
        value_stack.pop();
        if (condition) {
          uint32_t pop_depth = (block_or_loop_target[function_index][control_stack[label]].second == LOOP) ? label : label + 1;
          for (int i = 0; i < pop_depth; i++) {
            control_stack.pop_front();
          }
          buf.ptr = buf.start + (offset);
          TRACE("We are setting the buffer pointer to %p.\n", buf.ptr);
        }
        break;
      }

      case WASM_OP_BR_TABLE: {
        uint32_t number_of_labels = RD_U32();
        std::vector<uint32_t> table_labels;
        for (int i = 0; i < number_of_labels; i++) {
          uint32_t label = RD_U32();
          table_labels.push_back(label);
          TRACE("Pushing back label %d!\n", label);
        }
        uint32_t default_label = RD_U32(); 
        uint32_t final_label;
        int32_t index_into_table = std::get<int32_t>(value_stack.top());
        value_stack.pop();
        TRACE("Index into table is %d!\n", index_into_table);
        if (index_into_table >= number_of_labels || index_into_table < 0) {
          final_label = default_label;
        } else {
          final_label = table_labels[index_into_table];
        }
        TRACE("Final label is %d!\n", final_label);
        for (int i = 0; i < control_stack.size(); i++) {
          TRACE("Offset in vector is %lu!\n", control_stack[i]);
        }
        TRACE("Offset we are looking up is %lu!\n", control_stack[final_label]);
        long offset = block_or_loop_target[function_index][control_stack[final_label]].first;
        buf.ptr = buf.start + (offset);
        uint32_t pop_depth = (block_or_loop_target[function_index][control_stack[final_label]].second == LOOP) ? final_label : final_label + 1;
        for (int i = 0; i < pop_depth; i++) {
          control_stack.pop_front();
        }
        break;
      }

      default:
        break;
    }
    curr_virtual_pc++;
  }
}

FuncDecl* find_main_function(WasmModule& module) {
  auto& exported_functions = module.Exports();
  int main_index = 0;
  for (auto it = exported_functions.begin(); it != exported_functions.end(); ++it) {
    if(it->name == "main") {
      return (it->desc).func;
    }
    main_index++;
  }
  return NULL; //This should never happen.
}

int add_main_params_to_map(int main_fn_idx, WasmModule& module) {
  TRACE("Adding parameters for main to the var to value map!\n");
  int param_count = 0;
  TRACE("Index of main function is: %d!\n", main_fn_idx);
  TRACE("Number of params in main_fn is: %d!\n", module.getFunc(main_fn_idx)->sig->num_params);
  if (module.getFunc(main_fn_idx)->sig->num_params == 0) {
    return 0;
  }
  for (auto param = module.getFunc(main_fn_idx)->sig->params.begin(); param != module.getFunc(main_fn_idx)->sig->params.end(); ++param) {
    TRACE("Looking at parameter %d, which is %x!\n", param_count, *param);
    switch (*param) {
      case WASM_TYPE_I32: 
        var_to_value_map[main_fn_idx][param_count] = std::pair(*param, 0); 
        break;
      case WASM_TYPE_F64:
        var_to_value_map[main_fn_idx][param_count] = std::pair(*param, 0.0);
        break;
      default:
        TRACE("Param type is %x.\n", *param);
        throw std::runtime_error("Unimplemented types for params!");
    }
    param_count++;
  }
  return param_count;
}

void set_main_global_values(WasmModule& module) {
  auto globals = module.Globals();
  for (int i = 0; i < globals.size(); i++) {
    switch (globals[i].type) {
      case WASM_TYPE_I32: {
        instruction_execution(module, -1, globals[i].init_expr_bytes); // This function index shouldn't matter as global initializers are just constants.
        int32_t init_expr = std::get<int32_t>(value_stack.top());
        global_to_value_map[i] = std::make_tuple(static_cast<bool>(globals[i].is_mutable), WASM_TYPE_I32, init_expr);
        break;
      } 
      case WASM_TYPE_F64: {
        instruction_execution(module, -1, globals[i].init_expr_bytes); // This function index shouldn't matter as global initializers are just constants.
        double init_expr = std::get<double>(value_stack.top());
        global_to_value_map[i] = std::make_tuple(static_cast<bool>(globals[i].is_mutable), WASM_TYPE_F64, init_expr);
        break;
      }  
      default: 
        break;
    }
  }
  value_stack= std::stack<std::variant<int32_t, double>>();
}

void set_arg_values(int main_fn_idx, std::vector<std::string>& args) {
  TRACE("Number of arguments for main function is %zu!\n", args.size());
  for (int i = 0; i < args.size(); i++) {
    switch (var_to_value_map[main_fn_idx][i].first) {
      case WASM_TYPE_I32: {
        var_to_value_map[main_fn_idx][i].second = stoi(args[i]);
        TRACE("Setting i32 argument %d to %s.\n", static_cast<unsigned>(i), args[i].c_str());
        break;
      }
      case WASM_TYPE_F64: {
        TRACE("Setting f32 argument %d to %s.\n", static_cast<unsigned>(i), args[i].c_str());
        var_to_value_map[main_fn_idx][i].second = stod(args[i]); 
        break;
      }
      default: 
        throw std::runtime_error("Unimplemented type for arguments!");
    }
  }
}

void interpreter(WasmModule& module, std::vector<std::string>& args) {
  FuncDecl* main_fn = find_main_function(module);
  int main_fn_idx = module.getFuncIdx(main_fn);
  glob_main_idx = main_fn_idx;
  int num_params = add_main_params_to_map(main_fn_idx, module); 
  add_locals_to_map(main_fn_idx, module);
  set_arg_values(main_fn_idx, args);
  set_main_global_values(module);
  initialize_memory(module);
  initialize_data(module);
  initialize_table(module);
  initialize_elems(module);
  try {
    instruction_execution(module, main_fn_idx, main_fn->code_bytes); 
  } catch (const std::exception& e) {
      std::cout << "!trap" << std::endl;
      return;
  } catch (...) {
      std::cerr << "Caught an unknown exception." << std::endl;
      return;
  }

  if (main_fn->sig->results.size()) {
    switch (value_stack.top().index()) {
      case 0: 
        std::cout << std::get<int32_t>(value_stack.top());
        break;
      case 1: 
        std::cout << std::fixed << std::setprecision(6) << std::get<double>(value_stack.top());
        break;
    }
  }
}
 
// Main function.
// Parses arguments and either runs a file with arguments.
//  --trace: enable tracing to stderr
int main(int argc, char *argv[]) {
  args_t args = parse_args(argc, argv);
    
  TRACE("Number of arguments: %d\n", argc);

  for (int i = 0; i < argc; ++i) {
    TRACE("Argument %d: %s\n", i, (argv[i]));
  }

  byte* start = NULL;
  byte* end = NULL;

  const char *infile = args.infile.c_str();
  ssize_t r = load_file(infile, &start, &end);
  if (r < 0) {
    ERR("failed to load: %s\n", infile);
    return 1;
  }

  TRACE("loaded %s: %ld bytes\n", infile, r);
  WasmModule module = parse_bytecode(start, end);
  unload_file(&start, &end);
  
  /* Interpreter here */
  if (args.jit_compiled) {
    jit(module, args.mainargs);
  } else {
    interpreter(module, args.mainargs);
  }
  /* */
  return 0;
}