use crate::{virtual_machine::CodeAddr};

const MAX_HEAP_MEM : usize = 10000;

const TAG_BASIC : u8 = 0x00;
const TAG_CLOSURE : u8 = 0x01;
const TAG_FUNCTION : u8 = 0x02;
const TAG_VECTOR : u8 = 0x03;
const TAG_REF : u8 = 0x04;
const TAG_SUM : u8 = 0x05;
/// NOTE: we don't use vectors to represent tuples because they can't be guaranteed to take
/// less memory than a closure, which makes rewrite impossible
const TAG_TUPLE : u8 = 0x06;

pub struct Heap {
  next_addr : usize,
  data : [u8; MAX_HEAP_MEM]
}

pub type HeapAddr = i32;

impl Heap {
  fn write_u8(&mut self, to_write: u8) {
    self.data[self.next_addr] = to_write;
    self.next_addr += 1;
  }

  fn write_i32(&mut self, to_write: i32) {
    let bytes = to_write.to_le_bytes();
    self.data[self.next_addr] = bytes[0];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[1];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[2];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[3];
    self.next_addr += 1;
  }

  fn write_u32(&mut self, to_write: u32) {
    let bytes = to_write.to_le_bytes();
    self.data[self.next_addr] = bytes[0];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[1];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[2];
    self.next_addr += 1;
    self.data[self.next_addr] = bytes[3];
    self.next_addr += 1;
  }

  pub fn create() -> Heap {
    Heap {
      next_addr: 0,
      data: [0; MAX_HEAP_MEM]
    }
  }

  ///
  pub fn rewrite(&mut self, src: HeapAddr, target: HeapAddr) {
    let target_addr = usize::try_from(target).unwrap();
    assert!(self.data[target_addr] == TAG_CLOSURE);
    // we can write differing amounts depending on the type of src, or just write 13 bytes (size of closure)
    // the performance impact should be studied
    let target : usize = src.try_into().unwrap();
    let src : usize = target.try_into().unwrap();
    // closure objects are 13 bytes, so that is how many we copy
    self.data[target] = self.data[src];
    self.data[target + 1] = self.data[src + 1];
    self.data[target + 2] = self.data[src + 2];
    self.data[target + 3] = self.data[src + 3];
    self.data[target + 4] = self.data[src + 4];
    self.data[target + 5] = self.data[src + 5];
    self.data[target + 6] = self.data[src + 6];
    self.data[target + 7] = self.data[src + 7];
    self.data[target + 8] = self.data[src + 8];
    self.data[target + 9] = self.data[src + 9];
    self.data[target + 10] = self.data[src + 10];
    self.data[target + 11] = self.data[src + 11];
    self.data[target + 12] = self.data[src + 12];
  }

  pub fn expect_sum(&mut self, addr: HeapAddr) -> (u8, HeapAddr) {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_SUM);
    let args_addr = i32::from_le_bytes([self.data[addr+2], self.data[addr+3], self.data[addr+4], self.data[addr+5]]);
    (self.data[addr+1], args_addr)
  }

  pub fn is_closure(&self, addr: HeapAddr) -> bool {
    let addr = usize::try_from(addr).unwrap();
    self.data[addr] == TAG_CLOSURE
  }

  pub fn expect_closure(&mut self, addr: HeapAddr) -> (CodeAddr, HeapAddr) {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_CLOSURE);
    let code_addr = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    let globals_addr = i32::from_le_bytes([self.data[addr + 5], self.data[addr + 6], self.data[addr + 7], self.data[addr + 8]]);
    (code_addr, globals_addr)
  }

  pub fn expect_function(&mut self, addr: HeapAddr) -> (CodeAddr, HeapAddr, HeapAddr) {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_FUNCTION);
    let code_addr = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    let args_addr = i32::from_le_bytes([self.data[addr + 5], self.data[addr + 6], self.data[addr + 7], self.data[addr + 8]]);
    let globals_addr = i32::from_le_bytes([self.data[addr + 6], self.data[addr + 7], self.data[addr + 8], self.data[addr + 9]]);
    (code_addr, args_addr, globals_addr)
  }

  pub fn expect_vector(&mut self, addr: HeapAddr) -> Vec<HeapAddr> {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_VECTOR);
    let len = u32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]])
      .try_into()
      .unwrap();
    let mut res: Vec<i32> = Vec::<HeapAddr>::with_capacity(len);
    let mut next_elem_addr = addr + 5;
    let last = addr + (len+2)*4;
    while next_elem_addr < last {
      res.push(i32::from_le_bytes([self.data[next_elem_addr + 1], self.data[next_elem_addr + 2], self.data[next_elem_addr + 3], self.data[next_elem_addr + 4]]));
      next_elem_addr += 4;
    };
    res
  }

  pub fn expect_ref(&mut self, addr: HeapAddr) -> HeapAddr {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_REF);
    let content_addr = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    content_addr
  }

  pub fn expect_basic(&mut self, addr: HeapAddr) -> i32 {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_BASIC);
    i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]])
  }

  pub fn new_vector(&mut self, elems: &[i32]) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_VECTOR);
    self.write_i32(elems.len().try_into().unwrap());
    for &elem in elems {
      self.write_i32(elem);
    }
    ret.try_into().unwrap()
  }

  pub fn new_function(&mut self, code_addr : CodeAddr, arg_vec : HeapAddr, global_vec : HeapAddr) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_FUNCTION);
    self.write_i32(code_addr);
    self.write_i32(arg_vec);
    self.write_i32(global_vec);
    ret.try_into().unwrap()
  }

  pub fn new_closure(&mut self, code_addr : CodeAddr, global_vec : HeapAddr) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_CLOSURE);
    self.write_i32(code_addr);
    self.write_i32(global_vec);
    // write an additional 32-bit word to ensure that closures occupy as much space a functions (enabling rewrite)
    self.write_i32(0);
    ret.try_into().unwrap()
  }

  pub fn new_basic(&mut self, n : i32) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_BASIC);
    self.write_i32(n);
    ret.try_into().unwrap()
  }

  pub fn new_ref(&mut self, n : i32) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_REF);
    self.write_i32(n);
    ret.try_into().unwrap()
  }

  pub fn new_sum(&mut self, variant_id: u8, arg_vec : HeapAddr) -> HeapAddr {
    let ret = self.next_addr;
    self.write_u8(TAG_SUM);
    self.write_u8(variant_id);
    self.write_i32(arg_vec);
    ret.try_into().unwrap()
  }

}