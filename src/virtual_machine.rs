use crate::heap::{Heap, HeapAddr};

/// Code and program counter
pub struct VirtualMachine {
  /// All instructions in order
  instructions: Vec<i32>,
  /// Program counter
  pc: CodeAddr,
  /// Stack
  s: Vec<i32>,
  /// Stack pointer
  sp: usize,
  /// Shadow stack
  ss: Vec<HeapAddr>,
  /// Shadow stack pointer
  ssp: usize,
  /// Globals pointer
  gp: HeapAddr,
  /// Frame pointer
  fp: usize,
  /// Heap
  heap: Heap
}

/// Address of a specific instruction
pub type CodeAddr = i32;

const MAX_STACK_MEM : usize = 20000;

fn to_instructions(bytes: Vec<u8>) -> Vec<i32> {
  let mut result : Vec<i32> = vec![];
  let mut i = 0;
  while i < bytes.len() {
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
  pub fn from_file(file_name : &str) -> VirtualMachine {
    let f = to_instructions(std::fs::read(file_name).unwrap());
    VirtualMachine {
      s: Vec::from([0 as i32; MAX_STACK_MEM/4]),
      sp: 0,
      ss: Vec::from([0 as i32; MAX_STACK_MEM/4]),
      ssp: 0,
      gp: 0,
      fp: 0,
      instructions: f,
      pc: 0,
      heap: Heap::create()
    }
  }

  fn mkvec0(&mut self) {
    let n = self.ssp - self.fp;
    let mut vec = vec![0; n];
    self.ssp = self.fp + 1;
    for i in 0..n {
      vec[i] = self.ss[self.ssp + i]
    };
    let vec_addr = self.heap.new_vector(&vec[..]);
    self.ss[self.ssp] = vec_addr;
  }

  fn wrap(&mut self) {
    let fun_addr = self.heap.new_function(self.pc, self.ss[self.ssp], self.gp);
    self.ss[self.ssp] = fun_addr;
  }

  fn popenv(&mut self) {
    self.gp = self.s[self.sp - 2];
    self.pc = self.s[self.sp];
    self.ss[self.fp+1] = self.ss[self.ssp];
    self.ssp = self.fp + 1;
    self.fp = self.s[self.sp - 1].try_into().unwrap();
    self.sp -= 3;
  }

  fn mark(&mut self, return_addr: CodeAddr) {
    self.s[self.sp + 1] = self.gp;
    self.s[self.sp + 2] = self.fp.try_into().unwrap();
    self.s[self.sp + 3] = return_addr;
    self.fp = self.ssp;
    self.sp = self.sp + 3;
  }

  fn apply(&mut self) {
    let (code_addr, args_addr, globals_addr) = self.heap.expect_function(self.ss[self.ssp]);
    let args = self.heap.expect_vector(args_addr);
    for i in 0..args.len() {
      self.ss[self.ssp + i] = args[i];
    };
    self.ssp = self.ssp + args.len() - 1;
    self.gp = globals_addr;
    self.pc = code_addr;
  }

  fn apply0(&mut self) {
    let (code_addr, globals_addr) = self.heap.expect_closure(self.ss[self.ssp]);
    self.gp = globals_addr;
    self.pc = code_addr;
    self.ssp -= 1;
  }

  fn slide(&mut self, n: i32) {
    let n : usize = n.try_into().unwrap();
    self.ss[self.ssp - n] = self.ss[self.ssp];
    self.ssp = self.ssp - n;
  }

  fn rewrite(&mut self, n: i32) {
    let n : usize = n.try_into().unwrap();
    self.heap.rewrite(self.s[self.sp - n],self.s[self.sp]);
    self.sp -= 1;
  }

  fn pushloc(&mut self, n: i32) {
    let n : usize = n.try_into().unwrap();
    self.ss[self.ssp + 1] = self.ss[self.ssp - n];
    self.ssp += 1;
  }

  pub fn execute(&mut self) -> i32 {
    loop {
      let pc_ind : usize = self.pc.try_into().unwrap();
      let instr : i32 = self.instructions[pc_ind];
        match instr & 0x000000FF {
            0x00 => break, // halt
            0x01 => { // mul
              println!("mul");
              self.s[self.sp - 1] = self.s[self.sp - 1] * self.s[self.sp];
              self.sp -= 1;
              self.pc += 1;
            },
            0x02 => { // add
              println!("add");
              self.s[self.sp - 1] = self.s[self.sp - 1] + self.s[self.sp];
              self.sp -= 1;
              self.pc += 1;
            },
            0x03 => { // sub
              println!("sub");
              self.s[self.sp - 1] = self.s[self.sp - 1] - self.s[self.sp];
              self.sp -= 1;
              self.pc += 1;
            },
            0x04 => { // leq
              println!("leq");
              self.s[self.sp - 1] = if self.s[self.sp - 1] <= self.s[self.sp] { 1 } else { 0 };
              self.sp -= 1;
              self.pc += 1;
            },
            0x05 => { // eq
              println!("eq");
              self.s[self.sp - 1] = if self.s[self.sp - 1] == self.s[self.sp] { 1 } else { 0 };
              self.sp -= 1;
              self.pc += 1;
            },
            0x06 => { // geq
              println!("geq");
              self.s[self.sp - 1] = if self.s[self.sp - 1] >= self.s[self.sp] { 1 } else { 0 };
              self.sp -= 1;
              self.pc += 1;
            },
            0x07 => { // gt
              println!("gt");
              self.s[self.sp - 1] = if self.s[self.sp - 1] > self.s[self.sp] { 1 } else { 0 };
              self.sp -= 1;
              self.pc += 1;
            },
            0x08 => { // lt
              println!("lt");
              self.s[self.sp - 1] = if self.s[self.sp - 1] < self.s[self.sp] { 1 } else { 0 };
              self.sp -= 1;
              self.pc += 1;
            },
            0x09 => { // neg
              println!("neg");
              self.s[self.sp] = -self.s[self.sp];
              self.pc += 1;
            },
            0x0A => { // MkSum (variant_id)
              println!("MkSum");
              let variant_id = instr.to_le_bytes()[1];
              let sum_addr = self.heap.new_sum(variant_id, self.ss[self.ssp]);
              self.ss[self.ssp] = sum_addr;
              self.pc += 1;
            },
            0x0B => { //TSum
              println!("TSum");
              let (variant_id, _) = self.heap.expect_sum(self.ss[self.ssp]);
              let instr_bytes = instr.to_le_bytes();
              let jump_table_addr = u16::from_le_bytes([instr_bytes[1], instr_bytes[2]]);
              self.pc = Into::<i32>::into(jump_table_addr) + Into::<i32>::into(variant_id);
            },
            0x0C => { // TGetConstructorArg
              println!("TGetConstructorArg");
              let (_, args_vec_addr) = self.heap.expect_sum(self.ss[self.ssp]);
              self.ssp += 1;
              self.ss[self.ssp] = args_vec_addr;
              self.pc += 1;
            },
            0x0D => { // Pop
              println!("pop");
              self.ssp -= 1;
              self.pc += 1;
            },
            0x0E => { // GetRef
              let n = self.heap.expect_ref(self.ss[self.ssp]);
              self.ss[self.ssp] = n;
              self.pc = self.pc + 1;
            },
            0x0F => { // MkRef
              println!("MkRef");
              self.ss[self.ssp] = self.heap.new_ref(self.ss[self.ssp]);
              self.pc += 1;
            },
            0x10 => { // RefAssign
              println!("RefAssign");
              self.heap.assign_ref(self.ss[self.ssp], self.ss[self.ssp - 1]);
              self.ss[self.ssp-1] = self.ss[self.ssp];
              self.ssp -= 1;
              self.pc += 1;
            },
            0x11 => { // GetBasic
              println!("GetBasic");
              let n = self.heap.expect_basic(self.ss[self.ssp]);
              self.ssp -= 1;
              self.sp += 1;
              self.s[self.sp] = n;
              self.pc += 1;
            },
            0x12 => { // MkBasic
              println!("MkBasic");
              self.ssp += 1;
              self.ss[self.ssp] = self.heap.new_basic(self.s[self.sp]);
              self.sp -= 1;
              self.pc += 1;
            },
            0x13 => { // PushLoc(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              println!("PushLoc {n}");
              self.pushloc(n);
              self.pc += 1;
            },
            0x14 => { // PushGloba(n)
              let n : usize = ((instr & 0x00FFFF00) >> 8).try_into().unwrap();
              println!("PushGlobal {n}");
              let globals  = self.heap.expect_vector(self.gp);
              if n < globals.len() {
                self.ss[self.ssp + 1] = globals[n];
                self.ssp += 1;
                self.pc += 1;
              } else {
                panic!("fewer than n globals");
              }
            },
            0x15 => { // Slide(n)
              let n : i32 = (instr & 0x00FFFF00) >> 8;
              println!("Slide {}",n);
              self.slide(n);
              self.pc += 1;
            },
            0x16 => { // GetVec
              let elems = self.heap.expect_vector(self.ss[self.ssp]);
              println!("GetVec");
              for i in 0..elems.len() {
                self.ss[self.ssp + i] = elems[i];
              }
              self.ssp = self.ssp + elems.len() - 1;
              self.pc += 1;
            },
            0x17 => { // MkVec(n)
              let n : usize = ((instr & 0x00FFFF00) >> 8).try_into().unwrap();
              println!("MkVec {n}");
              let mut vec = vec![0; n.try_into().unwrap()];
              self.ssp = self.ssp - n + 1;
              for i in 0..n {
                vec[i] = self.ss[self.ssp + i];
              };
              self.ss[self.ssp] = self.heap.new_vector(&vec[..]);
              self.pc += 1;
            },
            0x18 => { // MkFunVal(addr)
              let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("MkFunVal {code_addr}");
              let args_addr = self.heap.new_vector(&[0;0]);
              self.ss[self.ssp] = self.heap.new_function(code_addr, args_addr, self.ss[self.ssp]);
              self.pc += 1;
            },
            0x19 => { // MkClos(addr)
              let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("MkClos {code_addr}");
              self.ss[self.ssp] = self.heap.new_closure(code_addr, self.ss[self.ssp]);
              self.pc += 1;
            },
            0x1A => { // Mark(return_addr)
              let return_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("Mark {return_addr}");
              self.mark(return_addr);
              self.pc += 1;
            },
            0x1B => { // Apply
              println!("Apply");
              self.apply ()
            },
            0x1C => { // TArg(numFormals)
              let num_formals : i32 = (instr & 0x0000FF00) >> 8;
              println!("TArg {num_formals}");
              if self.ssp - self.fp < num_formals.try_into().unwrap() {
                self.mkvec0 ();
                self.wrap ();
                self.popenv ()
              } else {
                self.pc += 1;
              }
            },
            0x1D => { // Return(numFormals)
              let num_formals : i32 = (instr & 0x0000FF00) >> 8;
              println!("Return {num_formals}");
              if self.ssp - self.fp - 1 == num_formals.try_into().unwrap() {
                self.popenv ()
              } else {
                self.slide(num_formals);
                self.apply();
              }
            },
            0x1E => { // Alloc(num_closures_to_alloc)
              let num_closures_to_alloc : usize = ((instr & 0x0000FF00) >> 8).try_into().unwrap();
              println!("Return {num_closures_to_alloc}");
              for i in 1..(num_closures_to_alloc + 1) {
                self.ss[self.ssp + i] = self.heap.new_closure(-1, -1);
              }
              self.ssp += num_closures_to_alloc;
              self.pc += 1;
            },
            0x1F => { // Rewrite(n)
              let n : usize = ((instr & 0x0000FF00) >> 8).try_into().unwrap();
              println!("Rewrite {n}");
              self.heap.rewrite(self.ss[self.ssp], self.ss[self.ssp - n]);
              self.ssp -= 1;
              self.pc += 1;
            },
            0x20 => { // Eval
              println!("Eval");
              match self.heap.is_closure(self.ss[self.ssp]) {
                true => {
                  self.mark(self.pc + 1);
                  self.pushloc(3);
                  self.apply0();
                },
                false => {
                  self.pc = self.pc + 1;
                }
              }
            },
            0x21 => { // Update
              println!("Update");
              self.popenv();
              self.rewrite(1);
            },
            0x22 => { // Load(numWords)
              panic!("unused") // TODO: remove this instruction
            },
            0x23 => { // LoadC(constantToLoad)
              let constant_to_load : i32 = (instr & 0x7FFFFF00) >> 8;
              println!("LoadC {constant_to_load}");
              self.sp += 1;
              self.s[self.sp] = constant_to_load;
              self.pc += 1;
            },
            0x24 => { // Jump(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("Jump {dest_addr}");
              self.pc = dest_addr;
            },
            0x25 => { // JumpZ(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("JumpZ {dest_addr}");
              self.pc = if self.s[self.sp] == 0 { dest_addr } else { self.pc + 1 };
              self.sp -= 1;
            },
            0x26 => { // JumpNZ(destAddr)
              let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
              println!("JumpNZ {dest_addr}");
              let n = self.heap.expect_basic(self.ss[self.ssp]);
              self.pc = if n != 0 { dest_addr } else { self.pc + 1 };
              self.ssp -= 1;
            },
            0x27 => { // JumpI(jump_offset)
              let jump_offset : i32 = (instr & 0x00FFFF00) >> 8;
              println!("JumpI {jump_offset}");
              self.pc = self.s[self.sp] + jump_offset;
              self.sp -= 1;
            },
            0x28 => { //MkTuple
              let tuple_addr = self.heap.new_tuple(self.ss[self.ssp]);
              self.ss[self.ssp] = tuple_addr;
              self.pc += 1;
            },
            0x29 => { //GetTuple
              let elems_addr = self.heap.expect_tuple(self.ss[self.ssp]);
              let elems = self.heap.expect_vector(elems_addr);
              for i in 0..elems.len() {
                self.ss[self.ssp + i] = elems[i];
              }
              self.ssp = self.ssp + elems.len() - 1;
              self.pc += 1;
            },
            _ => panic!("invalid instruction")
        }
    }
    self.heap.expect_basic(self.ss[self.ssp])
  }
}