use crate::heap::{Heap, HeapAddr};

pub type CodeAddr = i32;

pub struct VirtualMachine {
  /// All instructions in order
  pub instructions: Vec<i32>,
  /// Program counter
  pub pc: CodeAddr,
  /// Stack
  pub s: Vec<i32>,
  /// Stack pointer
  pub sp: usize,
  /// Shadow stack
  pub ss: Vec<HeapAddr>,
  /// Shadow stack pointer
  pub ssp: usize,
  /// Globals pointer
  pub gp: HeapAddr,
  /// Frame pointer
  pub fp: usize
}

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

/// Create new virtual machine from code file
pub fn from_file(file_name : &str) -> VirtualMachine {
  let f = to_instructions(std::fs::read(file_name).unwrap());
  VirtualMachine {
    s: Vec::from([0 as i32; MAX_STACK_MEM/4]),
    sp: 0,
    ss: Vec::from([0 as u32; MAX_STACK_MEM/4]),
    ssp: 0,
    gp: 0,
    fp: 0,
    instructions: f,
    pc: 0
  }
}

impl VirtualMachine {
  pub fn roots(&mut self) -> impl Iterator<Item = &mut HeapAddr> {
    self.ss[0..self.ssp+1].iter_mut().chain([&mut self.gp])
  }
}