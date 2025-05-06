
/// Code and program counter
pub struct VirtualMachine {
  /// All instructions in order
  instructions: Vec<i32>,
  /// Program counter
  pc: CodeAddr
}

/// Address of a specific instruction
pub type CodeAddr = i32;

const MAX_STACK_MEM : usize = 20000;

fn to_instructions(bytes: Vec<u8>) -> Vec<i32> {
  let mut result : Vec<i32> = vec![];
  let mut i = 0;
  while (i < bytes.len()) {
      result.push(Into::<i32>::into(bytes[i]) << 0
                  | Into::<i32>::into(bytes[i+1]) << 8
                  | Into::<i32>::into(bytes[i+2]) << 16
                  | Into::<i32>::into(bytes[i+3]) << 24);
      i += 4;
  }
  result
}

impl VirtualMachine {
  /// Create new virtual machine from code file
  pub fn from_file(file_name : String) -> VirtualMachine {
    let f = to_instructions(std::fs::read(file_name).unwrap());
    VirtualMachine {
      instructions: f,
      pc: 0
    }
  }

  pub fn execute(&mut self) {
    // stack
    let mut s = [0 as i32; MAX_STACK_MEM/4];
    let mut pc = 0;
    let mut sp = 0;
    let mut gp  = 0;
    let mut fp = 1;
    let mut heap = crate::heap::Heap::create();

    let mkvec0 = || {
      let n = sp - fp;
      let vec = vec![0; n];
      sp = fp + 1;
      for i in 0..n {
        vec[i] = s[sp + i]
      };
      let vec_addr = heap.new_vector(&vec[..]);
      s[sp] = vec_addr;
    };

    let wrap = || {
      let fun_addr = heap.new_function(pc - 1, s[sp], gp);
      s[sp] = fun_addr;
    };

    let popenv = || {
      gp = s[fp - 2];
      pc = s[fp];
      s[fp - 2] = s[sp];
      sp = fp - 2;
      fp = s[fp - 1].try_into().unwrap();
    };

    let mark = |return_addr : CodeAddr| {
      s[sp + 1] = gp;
      s[sp + 2] = fp;
      s[sp + 3] = return_addr;
      fp = (sp + 3).try_into().unwrap();
      sp = sp + 3;
    };

    let apply = || {
      let (code_addr, args_addr, globals_addr) = heap.expect_function(s[sp]);
      let args = heap.expect_vector(args_addr);
      for i in 0..args.len() {
        s[sp + i] = args[i];
      };
      sp = sp + args.len() - 1;
      gp = globals_addr;
      pc = code_addr;
    };

    let apply0 = || {
      let (code_addr, globals_addr) = heap.expect_closure(s[sp]);
      gp = globals_addr;
      pc = code_addr;
      sp -= 1;
    };

    loop {
      let instr = self.instructions[pc];
        match (instr & 0x00000011) {
            0x00 => break, // halt
            0x01 => { // mul
              s[sp - 1] = s[sp - 1] * s[sp];
              sp -= 1;
              pc += 1;
            },
            0x02 => { // add
              s[sp - 1] = s[sp - 1] + s[sp];
              sp -= 1;
              pc += 1;
            },
            0x03 => { // sub
              s[sp - 1] = s[sp - 1] - s[sp];
              sp -= 1;
              pc += 1;
            },
            0x04 => { // leq
              s[sp - 1] = if s[sp - 1] <= s[sp] { 1 } else { 0 };
              sp -= 1;
              pc += 1;
            },
            0x05 => { // eq
              s[sp - 1] = if s[sp - 1] == s[sp] { 1 } else { 0 };
              sp -= 1;
              pc += 1;
            },
            0x06 => { // geq
              s[sp - 1] = if s[sp - 1] >= s[sp] { 1 } else { 0 };
              sp -= 1;
              pc += 1;
            },
            0x07 => { // gt
              s[sp - 1] = if s[sp - 1] > s[sp] { 1 } else { 0 };
              sp -= 1;
              pc += 1;
            },
            0x08 => { // lt
              s[sp - 1] = if s[sp - 1] < s[sp] { 1 } else { 0 };
              sp -= 1;
              pc += 1;
            },
            0x09 => { // neg
              s[sp] = -s[sp];
              pc += 1;
            },
            0x0A => { // MkSum
              let variant_id = instr.to_le_bytes()[1];
              heap.new_sum(variant_id, s[sp]);
              pc += 1;
            },
            0x0B => { //TSum
              let (variant_id, _) = heap.expect_sum(s[sp]);
              let instr_bytes = instr.to_le_bytes();
              let jump_table_addr = u16::from_le_bytes([instr_bytes[1], instr_bytes[2]]);
              pc = Into::<usize>::into(jump_table_addr) + Into::<usize>::into(variant_id);
            },
            0x0C => { // TGetConstructorArg
              let (_, args_vec_addr) = heap.expect_sum(s[sp]);
              sp += 1;
              s[sp] = args_vec_addr;
              pc += 1;
            },
            0x0D => { // Eval

            }


            _ => panic!("todo")
        }
    }
  }
}