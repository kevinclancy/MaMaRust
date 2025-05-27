use std::{mem::swap, slice};

use crate::{virtual_machine::CodeAddr, virtual_machine::VirtualMachine};

const MAX_HEAP_MEM : usize = 10000;

const TAG_FORWARDING_PTR : u8 = 0x00;
const TAG_BASIC : u8 = 0x01;
const TAG_CLOSURE : u8 = 0x02;
const TAG_FUNCTION : u8 = 0x03;
const TAG_VECTOR : u8 = 0x04;
const TAG_REF : u8 = 0x05;
const TAG_SUM : u8 = 0x06;

/// NOTE: we don't use vectors to represent tuples because they can't be guaranteed to take
/// less memory than a closure, which makes rewrite impossible
const TAG_TUPLE : u8 = 0x07;

pub struct Heap {
  next_addr : usize,
  data : Vec<u8>,
  copy : Vec<u8>
}

pub type HeapAddr = u32;

impl Heap {
  fn write_u8(&mut self, to_write: u8) {
    self.data[self.next_addr] = to_write;
    self.next_addr += 1;
  }

  fn write_i32(&mut self, to_write: i32) {
    let bytes = to_write.to_le_bytes();
    self.data[self.next_addr..self.next_addr+4].copy_from_slice(&bytes);
    self.next_addr += 4;
  }

  fn write_u32(&mut self, to_write: u32) {
    let bytes = to_write.to_le_bytes();
    self.data[self.next_addr..self.next_addr+4].copy_from_slice(&bytes);
    self.next_addr += 4;
  }

  pub fn create() -> Heap {
    Heap {
      next_addr: 0,
      data: Vec::from([0; MAX_HEAP_MEM]),
      copy: Vec::from([0; MAX_HEAP_MEM])
    }
  }

  /// Collects garbage and sets global pointer and all addresses in the shadow stack
  /// to the corresponding addresses in the post-garbage-collected heap
  pub fn collect(&mut self, vm: &mut VirtualMachine) {
    println!("collecting");

    let mut scan_ptr : usize = 0;
    let mut free_ptr : usize = 0;

    for i in 0..(vm.ssp+1) {
      let new_addr = free_ptr.try_into().unwrap();
      self.copy(vm.ss[i].try_into().unwrap(), &mut free_ptr);
      vm.ss[i] = new_addr;
    }

    let new_gp_addr = free_ptr.try_into().unwrap();
    self.copy(vm.gp.try_into().unwrap(), &mut free_ptr);
    vm.gp = new_gp_addr;

    while scan_ptr != free_ptr {
      // examine object at scan ptr
      // redirect all references, copying any encountered references that haven't yet been copied
      self.update(&mut scan_ptr, &mut free_ptr);
    }

    swap(&mut self.data, &mut self.copy);

    self.next_addr = scan_ptr;
    println!("finished collecting");
  }

  /// * obj_ptr - object address in 'data' heap
  /// * free_ptr - free pointer in 'copy' heap
  ///
  /// Given a 'data' heap address *obj_ptr*, either return the forwarding pointer if it has one,
  /// or otherwise copy it to the 'copy' heap at *free_ptr*, change it to a forwarding pointer in the 'data' heap,
  /// increment *free_ptr* to directly after the newly copied object, and return the copy-heap address of the newly copied object.
  fn update_obj(&mut self, obj_ptr: usize, free_ptr : &mut usize) -> u32 {
    match self.data[obj_ptr] {
      TAG_FORWARDING_PTR => {
        let forwarding_addr = u32::from_le_bytes([self.data[obj_ptr + 1], self.data[obj_ptr + 2], self.data[obj_ptr + 3], self.data[obj_ptr + 4]]);
        forwarding_addr
      },
      _ => {
        let result_addr = *free_ptr;
        self.copy( obj_ptr, free_ptr);

        self.data[obj_ptr] = TAG_FORWARDING_PTR;
        let result_bytes = TryInto::<u32>::try_into(result_addr).unwrap().to_le_bytes();
        self.data[obj_ptr + 1] = result_bytes[0];
        self.data[obj_ptr + 2] = result_bytes[1];
        self.data[obj_ptr + 3] = result_bytes[2];
        self.data[obj_ptr + 4] = result_bytes[3];

        result_addr.try_into().unwrap()
      }
    }
  }

  fn update(&mut self, scan_ptr : &mut usize, free_ptr : &mut usize) {
    match self.copy[*scan_ptr] {
      TAG_BASIC => { *scan_ptr += 5 }, // no pointers to update
      TAG_CLOSURE => {
        let globals_addr : usize = u32::from_le_bytes([self.copy[*scan_ptr + 5], self.copy[*scan_ptr + 6], self.copy[*scan_ptr + 7], self.copy[*scan_ptr + 8]]).try_into().unwrap();
        let new_globals_addr = self.update_obj(globals_addr, free_ptr);
        self.copy[(*scan_ptr + 5)..(*scan_ptr + 8)].copy_from_slice(&new_globals_addr.to_le_bytes());
        *scan_ptr += 13;
      },
      TAG_FUNCTION => {
        let args_addr : usize = u32::from_le_bytes([self.copy[*scan_ptr + 5], self.copy[*scan_ptr + 6], self.copy[*scan_ptr + 7], self.copy[*scan_ptr + 8]]).try_into().unwrap();
        let globals_addr : usize = u32::from_le_bytes([self.copy[*scan_ptr + 9], self.copy[*scan_ptr + 10], self.copy[*scan_ptr + 11], self.copy[*scan_ptr + 12]]).try_into().unwrap();

        let new_args_addr = self.update_obj(args_addr, free_ptr);
        let new_globals_addr = self.update_obj(globals_addr, free_ptr);

        self.copy[*scan_ptr+5 .. *scan_ptr+9].copy_from_slice(&new_args_addr.to_le_bytes());
        self.copy[*scan_ptr+9 .. *scan_ptr+13].copy_from_slice(&new_globals_addr.to_le_bytes());

        *scan_ptr += 13;
      },
      TAG_VECTOR => {
        // TODO: change i32 below to u32
        let num_elems : usize = i32::from_le_bytes([self.copy[*scan_ptr + 1], self.copy[*scan_ptr + 2], self.copy[*scan_ptr + 3], self.copy[*scan_ptr + 4]]).try_into().unwrap();
        let mut i = *scan_ptr + 5;
        let after = *scan_ptr + 5 + num_elems*4;
        while i < after {
          let addr : usize = u32::from_le_bytes([self.copy[i + 0], self.copy[i + 1], self.copy[i + 2], self.copy[i + 3]]).try_into().unwrap();
          let new_addr = self.update_obj(addr, free_ptr);
          self.copy[i+0..i+4].copy_from_slice(&new_addr.to_le_bytes());
          i += 4;
        }
        *scan_ptr = after;
      },
      TAG_REF => {
        let content_addr : usize = u32::from_le_bytes([self.copy[*scan_ptr + 1], self.copy[*scan_ptr + 2], self.copy[*scan_ptr + 3], self.copy[*scan_ptr + 4]]).try_into().unwrap();
        let new_content_addr = self.update_obj(content_addr, free_ptr);
        self.copy[*scan_ptr+1..*scan_ptr+5].copy_from_slice(&new_content_addr.to_le_bytes());
        *scan_ptr += 5;
      },
      TAG_TUPLE => {
        let vec_addr : usize = u32::from_le_bytes([self.copy[*scan_ptr + 1], self.copy[*scan_ptr + 2], self.copy[*scan_ptr + 3], self.copy[*scan_ptr + 4]]).try_into().unwrap();
        let new_vec_addr = self.update_obj(vec_addr, free_ptr);
        self.copy[*scan_ptr+1..*scan_ptr+5].copy_from_slice(&new_vec_addr.to_le_bytes());
        *scan_ptr += 5;
      },
      _ => {
        panic!("invalid tag");
      }
    }
  }

  fn copy(&mut self, data_ind : usize, copy_ind : &mut usize) {
    match self.data[data_ind] {
      TAG_BASIC => {
        self.copy[*copy_ind..*copy_ind+5].copy_from_slice(&self.data[data_ind..data_ind+5]);
        *copy_ind += 5;
      },
      TAG_CLOSURE => {
        self.copy[*copy_ind..*copy_ind+13].copy_from_slice(&self.data[data_ind..data_ind+13]);
        *copy_ind += 13;
      },
      TAG_FUNCTION => {
        self.copy[*copy_ind..*copy_ind+13].copy_from_slice(&self.data[data_ind..data_ind+13]);
        *copy_ind += 13;
      },
      TAG_VECTOR => {
        let length = i32::from_le_bytes([self.data[data_ind + 1], self.data[data_ind + 2], self.data[data_ind + 3], self.data[data_ind + 4]]);
        let num_bytes = TryInto::<usize>::try_into(length).unwrap() * 4;
        self.copy[*copy_ind..*copy_ind+5+num_bytes].copy_from_slice(&self.data[data_ind..data_ind+5+num_bytes]);
        *copy_ind += 5 + num_bytes;
      },
      TAG_REF => {
        self.copy[*copy_ind..*copy_ind+5].copy_from_slice(&self.data[data_ind..data_ind+5]);
        *copy_ind += 5;
      },
      TAG_SUM => {
        self.copy[*copy_ind..*copy_ind+6].copy_from_slice(&self.data[data_ind..data_ind+6]);
        *copy_ind += 6;
      },
      TAG_TUPLE => {
        self.copy[*copy_ind..*copy_ind+5].copy_from_slice(&self.data[data_ind..data_ind+5]);
        *copy_ind += 5;
      },
      _ => {
        panic!("invalid heap object tag");
      }
    }
  }

  ///
  pub fn rewrite(&mut self, src: HeapAddr, target: HeapAddr) {
    let target_addr = usize::try_from(target).unwrap();
    assert!(self.data[target_addr] == TAG_CLOSURE);
    // we can write differing amounts depending on the type of src, or just write 13 bytes (size of closure)
    // the performance impact should be studied
    let target : usize = target.try_into().unwrap();
    let src : usize = src.try_into().unwrap();
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
    let args_addr = u32::from_le_bytes([self.data[addr+2], self.data[addr+3], self.data[addr+4], self.data[addr+5]]);
    (self.data[addr+1], args_addr)
  }

  pub fn is_closure(&self, addr: HeapAddr) -> bool {
    let addr = usize::try_from(addr).unwrap();
    self.data[addr] == TAG_CLOSURE
  }

  pub fn expect_closure(&self, addr: HeapAddr) -> (CodeAddr, HeapAddr) {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_CLOSURE);
    let code_addr = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    let globals_addr = u32::from_le_bytes([self.data[addr + 5], self.data[addr + 6], self.data[addr + 7], self.data[addr + 8]]);
    (code_addr, globals_addr)
  }

  pub fn expect_function(&self, addr: HeapAddr) -> (CodeAddr, HeapAddr, HeapAddr) {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_FUNCTION);
    let code_addr = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    let args_addr = u32::from_le_bytes([self.data[addr + 5], self.data[addr + 6], self.data[addr + 7], self.data[addr + 8]]);
    let globals_addr = u32::from_le_bytes([self.data[addr + 9], self.data[addr + 10], self.data[addr + 11], self.data[addr + 12]]);
    (code_addr, args_addr, globals_addr)
  }

  pub fn expect_vector(&self, addr: HeapAddr) -> Vec<HeapAddr> {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_VECTOR);
    let len = u32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]])
      .try_into()
      .unwrap();
    let mut res: Vec<HeapAddr> = Vec::<HeapAddr>::with_capacity(len);
    let mut next_elem_addr = addr + 5;
    let last = addr + 1 + (len+1)*4;
    while next_elem_addr < last {
      let addr = u32::from_le_bytes([self.data[next_elem_addr + 0], self.data[next_elem_addr + 1], self.data[next_elem_addr + 2], self.data[next_elem_addr + 3]]);
      res.push(addr);
      next_elem_addr += 4;
    };
    res
  }

  pub fn expect_ref(&self, addr: HeapAddr) -> HeapAddr {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_REF);
    let content_addr = u32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    content_addr
  }

  /// Set the reference cell contents at *ref_addr* equal to *val_addr*
  pub fn assign_ref(&mut self, ref_addr: HeapAddr, val_addr: HeapAddr) {
    let ref_addr = usize::try_from(ref_addr).unwrap();
    assert!(self.data[ref_addr] == TAG_REF);
    let bytes = val_addr.to_le_bytes();
    self.data[ref_addr + 1] = bytes[0];
    self.data[ref_addr + 2] = bytes[1];
    self.data[ref_addr + 3] = bytes[2];
    self.data[ref_addr + 4] = bytes[3];
  }

  pub fn expect_basic(&self, addr: HeapAddr) -> i32 {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_BASIC);
    let val = i32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    val
  }

  /// Asserts the existence of tuple at addr. Returns the heap address of the tuple's element vector.
  pub fn expect_tuple(&self, addr: HeapAddr) -> HeapAddr {
    let addr = usize::try_from(addr).unwrap();
    assert!(self.data[addr] == TAG_TUPLE);
    let val = u32::from_le_bytes([self.data[addr + 1], self.data[addr + 2], self.data[addr + 3], self.data[addr + 4]]);
    val
  }

  pub fn new_vector(&mut self, elems: &[HeapAddr], vm : &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 5 + elems.len() >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 5 + elems.len() >= self.data.len() {
      panic!("Out of memory!")
    }
    let ret = self.next_addr;
    self.write_u8(TAG_VECTOR);
    self.write_i32(elems.len().try_into().unwrap());
    for &elem in elems {
      self.write_u32(elem.try_into().unwrap());
    }
    ret.try_into().unwrap()
  }

  pub fn new_tuple(&mut self, elems_addr: HeapAddr, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 5 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 5 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_TUPLE);
    self.write_u32(elems_addr.try_into().unwrap());
    ret.try_into().unwrap()
  }

  pub fn new_function(&mut self, code_addr : CodeAddr, arg_vec : HeapAddr, global_vec : HeapAddr, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 13 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 13 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_FUNCTION);
    self.write_i32(code_addr);
    self.write_u32(arg_vec.try_into().unwrap());
    self.write_u32(global_vec.try_into().unwrap());
    println!("new function at {ret}");
    ret.try_into().unwrap()
  }

  pub fn new_closure(&mut self, code_addr : CodeAddr, global_vec : HeapAddr, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 13 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 13 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_CLOSURE);
    self.write_i32(code_addr);
    self.write_u32(global_vec);
    // write an additional 32-bit word to ensure that closures occupy as much space a functions (enabling rewrite)
    self.write_i32(0);
    ret.try_into().unwrap()
  }

  pub fn new_basic(&mut self, n : i32, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 5 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 5 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_BASIC);
    self.write_i32(n);
    let b = self.expect_basic(ret.try_into().unwrap());
    println!("new basic {b} at {ret}");
    ret.try_into().unwrap()
  }

  pub fn new_ref(&mut self, n : HeapAddr, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 5 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 5 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_REF);
    self.write_u32(n.try_into().unwrap());
    ret.try_into().unwrap()
  }

  pub fn new_sum(&mut self, variant_id: u8, arg_vec : HeapAddr, vm: &mut VirtualMachine) -> HeapAddr {
    if self.next_addr + 6 >= self.data.len() {
      self.collect(vm);
    }

    if self.next_addr + 6 >= self.data.len() {
      panic!("Out of memory!")
    }

    let ret = self.next_addr;
    self.write_u8(TAG_SUM);
    self.write_u8(variant_id);
    self.write_u32(arg_vec.try_into().unwrap());
    ret.try_into().unwrap()
  }
}