
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

    let slide = |n : i32| {
      s[sp.try_into().unwrap() - n] = s[sp];
      sp = sp.try_into().unwrap() - n;
    };

    let rewrite = |n : i32| {
      heap.rewrite(s[sp.try_into().unwrap() - n],s[sp]);
      sp -= 1;
    };

    let pushloc = |n : i32| {
      s[sp + 1] = s[sp.try_into().unwrap() - n];
    };

    loop {
      let instr = self.instructions[pc];
        match instr & 0x000000FF {
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
              pc = Into::<i32>::into(jump_table_addr) + Into::<i32>::into(variant_id);
            },
            0x0C => { // TGetConstructorArg
              let (_, args_vec_addr) = heap.expect_sum(s[sp]);
              sp += 1;
              s[sp] = args_vec_addr;
              pc += 1;
            },
            0x0D => { // Pop
              sp -= 1;
              pc += 1;
            },
            0x0E => { // GetRef
              let n = heap.expect_ref(s[sp]);
              s[sp] = n;
              pc = pc + 1;
            },
            0x0F => { // MkRef
              s[sp] = heap.new_ref(s[sp]);
              pc += 1;
            },
            0x10 => { // RefAssign
              let _ = heap.expect_ref(s[sp]);
              // TODO TODO TODO !!! heap.new_ref()
            },
            0x11 => { // GetBasic
              let n = heap.expect_basic(s[sp]);
              s[sp] = n;
              pc += 1;
            },
            0x12 => { // MkBasic
              s[sp] = heap.new_basic(s[sp]);
              pc += 1;
            },
            0x13 => { // PushLoc(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              pushloc(n);
              pc += 1;
            },
            0x14 => { // PushGloba(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              let globals  = heap.expect_vector(gp);
              if n < globals.len() {
                s[sp + 1] = globals[n];
                sp += 1;
                pc += 1;
              } else {
                panic!("fewer than n globals");
              }
            },
            0x15 => { // Slide(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              slide(n);
              pc += 1;
            },
            0x16 => { // GetVec
              let elems = heap.expect_vector(s[sp]);
              for i in 0..elems.len() {
                s[sp + i] = elems[i];
              }
              sp = sp + elems.len() - 1;
              pc += 1;
            },
            0x17 => { // MkVec(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              let vec = vec![0; n];
              sp = sp - n + 1;
              for i in 0..n {
                vec[i] = s[sp + i];
              };
              s[sp] = heap.new_vector(&vec[..]);
              pc += 1;
            },
            0x18 => { // MkFunVal(addr)
              let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
              let args_addr = heap.new_vector(&[0;0]);
              s[sp] = heap.new_function(code_addr, args_addr, s[sp]);
              pc += 1;
            },
            0x19 => { // MkClos(addr)
              let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
              s[sp] = heap.new_closure(code_addr, s[sp]);
              pc += 1;
            },
            0x1A => { // Mark(return_addr)
              let return_addr : i32 = (instr & 0x00FFFF00) >> 8;
              mark(return_addr);
              pc += 1;
            },
            0x1B => { // Apply
              apply ()
            },
            0x1C => { // TArg(numFormals)
              let num_formals : i32 = (instr & 0x0000FF00) >> 8;
              if sp - fp < num_formals {
                mkvec0 ();
                wrap ();
                popenv ()
              } else {
                pc += 1;
              }
            },
            0x1D => { // Return(numFormals)
              let num_formals : i32 = (instr & 0x0000FF00) >> 8;
              if sp - fp - 1 == num_formals {
                popenv ()
              } else {
                slide(num_formals);
                apply();
              }
            },
            0x1E => { // Alloc(num_closures_to_alloc)
              let num_closures_to_alloc : i32 = (instr & 0x0000FF00) >> 8;
              for i in 1..(num_closures_to_alloc + 1) {
                s[sp + i] = heap.new_closure(-1, -1);
              }
              sp += num_closures_to_alloc;
              pc += 1;
            },
            0x1F => { // Rewrite(n)
              let n : i32 = (instr & 0x0000FF00) >> 8;
              heap.rewrite(s[sp], s[sp-n]);
              sp -= 1;
              pc += 1;
            },
            0x20 => { // Eval
              match heap.is_closure(s[sp]) {
                true => {
                  mark(pc + 1);
                  pushloc(3);
                  apply0();
                },
                false => {
                  pc = pc + 1;
                }
              }
            },
            0x21 => { // Update
              popenv();
              rewrite(1);
            },
            0x22 => { // Load(numWords)
              let num_words_to_load : i32 = (instr & 0x0000FF00) >> 8;
              for i in (0..num_words_to_load).rev() {
                s[sp + i] = s[s[sp].try_into().unwrap() + i];
              }
              sp = sp + num_words_to_load - 1;
              pc += 1;
            },
            0x23 => { // LoadC(constantToLoad)
              let constant_to_load : i32 = (instr & 0xFFFFFF00) >> 8;
              sp += 1;
              s[sp] = constant_to_load;
              pc += 1;
            },
            0x24 => { // Jump(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              pc = dest_addr;
            },
            0x25 => { // JumpZ(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              pc = if s[sp] == 0 { dest_addr } else { pc + 1 };
              sp -= 1;
            },
            0x26 => { // JumpNZ(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              let n = heap.expect_basic(s[sp]);
              pc = if n != 0 { dest_addr } else { pc + 1 };
              sp -= 1;
            },
            0x27 => { // JumpI(jump_offset)
              let jump_offset : i32 = (instr & 0x00FFFF00) >> 8;
              pc = s[sp] + jump_offset;
              sp -= 1;
            },
            _ => panic!("invalid instruction")
        }
    }
  }
}