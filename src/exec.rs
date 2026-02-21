use crate::heap::{Heap};
use crate::virtual_machine::{VirtualMachine, CodeAddr};

/// Pop all of the values from the shadow stack pointer (inclusive) to direcly above
/// the frame pointer, moving them into a newly allocated vector object `v`, pushing a
/// reference to `v` onto the shadow stack.
fn mkvec0(vm : &mut VirtualMachine, heap: &mut Heap) {
  let n = vm.ssp - vm.fp;
  let mut vec = vec![0; n];

  vm.ssp = vm.fp + 1;
  for i in 0..n {
    vec[i] = vm.ss[vm.ssp + i]
  };
  let vec_addr = heap.new_vector(&vec[..], vm.roots());
  vm.ss[vm.ssp] = vec_addr;
}

/// Allocate a new function-object, using the current PC for its code address, the reference on top of
/// the shadow stack as its argument vector address, and the current GP as its global vector address.
///
/// Then push the new function-object onto the shadow stack.
fn wrap(vm: &mut VirtualMachine, heap: &mut Heap) {
  let fun_addr = heap.new_function(vm.pc, vm.ss[vm.ssp], vm.gp, vm.roots());
  vm.ss[vm.ssp] = fun_addr;
}

/// Restore the global pointer from the current frame's saved GP (at the shadow stack location pointed to by FP).
/// The value at the top of the shadow stack is preserved by sliding it down to FP, discarding everything
/// in between (let-bound values, arguments). FP then refers to the new top of the shadow stack.
///
/// Pop a saved PC and FP from the top of the basic stack, restoring their values to the PC and FP registers.
fn popenv(vm: &mut VirtualMachine) {
  vm.gp = vm.ss[vm.fp];
  vm.pc = vm.s[vm.sp];
  vm.ss[vm.fp] = vm.ss[vm.ssp];
  vm.ssp = vm.fp;
  vm.fp = vm.s[vm.sp - 1].try_into().unwrap();
  vm.sp -= 2;
}

/// Save the current GP onto the shadow stack and push the current FP and the given return address
/// onto the basic stack, establishing a new call frame. FP is set to the new top of the shadow stack,
/// which points to the saved GP.
fn mark(vm: &mut VirtualMachine, return_addr: CodeAddr) {
  vm.ss[vm.ssp + 1] = vm.gp.try_into().unwrap();
  vm.s[vm.sp + 1] = vm.fp.try_into().unwrap();
  vm.s[vm.sp + 2] = return_addr;
  vm.ssp += 1;
  vm.sp += 2;
  vm.fp = vm.ssp;
}

/// Expect a function object at the top of the shadow stack. Replace it with the function's stored
/// arguments (unpacked from its argument vector), set GP to the function's globals pointer,
/// and jump to the function's code address.
fn apply(vm: &mut VirtualMachine, heap: &Heap) {
  let (code_addr, args_addr, globals_addr) = heap.expect_function(vm.ss[vm.ssp]);
  let args = heap.expect_vector(args_addr);
  for i in 0..args.len() {
    vm.ss[vm.ssp + i] = args[i];
  };
  vm.ssp = vm.ssp + args.len() - 1;
  vm.gp = globals_addr;
  vm.pc = code_addr;
}

/// Expect a closure at the top of the shadow stack. Pop it, set GP to the closure's globals
/// pointer, and jump to the closure's code address.
fn apply0(vm: &mut VirtualMachine, heap: &Heap) {
  let (code_addr, globals_addr) = heap.expect_closure(vm.ss[vm.ssp]);
  vm.gp = globals_addr;
  vm.pc = code_addr;
  vm.ssp -= 1;
}

/// Remove `slide_distance` elements from the shadow stack by sliding the top `num_elems_to_slide`
/// elements downward, overwriting the elements beneath them.
fn slide(vm: &mut VirtualMachine, slide_distance: usize, num_elems_to_slide: usize) {
  match slide_distance {
    0 => { },
    _ => {
      if num_elems_to_slide == 0 {
        vm.ssp = vm.ssp - slide_distance
      } else {
        vm.ssp = vm.ssp - slide_distance - num_elems_to_slide;
        for _ in 0..num_elems_to_slide {
          vm.ssp = vm.ssp + 1;
          vm.ss[vm.ssp] = vm.ss[vm.ssp + slide_distance]
        }
      }
    }
  }
}

/// Overwrite the heap object referenced `n` positions below the top of the shadow stack
/// with the heap object referenced at the top of the shadow stack. Used to fill in
/// placeholder closures allocated by ALLOC with their actual values.
fn rewrite(vm: &mut VirtualMachine, heap:&mut Heap, n: i32) {
  let n : usize = n.try_into().unwrap();
  heap.rewrite(vm.ss[vm.ssp], vm.ss[vm.ssp - n]);
  vm.sp -= 1;
}

/// Push a copy of the shadow stack value `n` positions below the top onto the shadow stack.
fn pushloc(vm: &mut VirtualMachine, n: i32) {
  let n : usize = n.try_into().unwrap();
  vm.ss[vm.ssp + 1] = vm.ss[vm.ssp - n];
  vm.ssp += 1;
}

/// Execute the program, returning the result of the program.
pub fn execute(vm: &mut VirtualMachine) -> i32 {
  let mut heap = Heap::create();
  loop {
    let pc_ind : usize = vm.pc.try_into().unwrap();
    let instr : i32 = vm.instructions[pc_ind];
      match instr & 0x000000FF {
          0x00 => break, // halt
          0x01 => { // mul
            println!("mul");
            vm.s[vm.sp - 1] = vm.s[vm.sp - 1] * vm.s[vm.sp];
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x02 => { // add
            println!("add");
            vm.s[vm.sp - 1] = vm.s[vm.sp - 1] + vm.s[vm.sp];
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x03 => { // sub
            println!("sub");
            vm.s[vm.sp - 1] = vm.s[vm.sp - 1] - vm.s[vm.sp];
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x04 => { // leq
            println!("leq");
            vm.s[vm.sp - 1] = if vm.s[vm.sp - 1] <= vm.s[vm.sp] { 1 } else { 0 };
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x05 => { // eq
            println!("eq");
            vm.s[vm.sp - 1] = if vm.s[vm.sp - 1] == vm.s[vm.sp] { 1 } else { 0 };
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x06 => { // geq
            println!("geq");
            vm.s[vm.sp - 1] = if vm.s[vm.sp - 1] >= vm.s[vm.sp] { 1 } else { 0 };
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x07 => { // gt
            println!("gt");
            vm.s[vm.sp - 1] = if vm.s[vm.sp - 1] > vm.s[vm.sp] { 1 } else { 0 };
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x08 => { // lt
            println!("lt");
            vm.s[vm.sp - 1] = if vm.s[vm.sp - 1] < vm.s[vm.sp] { 1 } else { 0 };
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x09 => { // neg
            println!("neg");
            vm.s[vm.sp] = -vm.s[vm.sp];
            vm.pc += 1;
          },
          0x0A => { // MkSum (variant_id)
            println!("MkSum");
            let variant_id = instr.to_le_bytes()[1];
            let sum_addr = heap.new_sum(variant_id, vm.ss[vm.ssp], vm.ss[0..vm.ssp+1].iter_mut().chain([&mut vm.gp]));
            vm.ss[vm.ssp] = sum_addr;
            vm.pc += 1;
          },
          0x0B => { //TSum
            println!("TSum");
            let (variant_id, _) = heap.expect_sum(vm.ss[vm.ssp]);
            let instr_bytes = instr.to_le_bytes();
            let jump_table_addr = u16::from_le_bytes([instr_bytes[1], instr_bytes[2]]);
            vm.pc = Into::<i32>::into(jump_table_addr) + Into::<i32>::into(variant_id);
          },
          0x0C => { // TGetConstructorArg
            println!("TGetConstructorArg");
            let (_, args_vec_addr) = heap.expect_sum(vm.ss[vm.ssp]);
            vm.ssp += 1;
            vm.ss[vm.ssp] = args_vec_addr;
            vm.pc += 1;
          },
          0x0D => { // Pop
            println!("pop");
            vm.ssp -= 1;
            vm.pc += 1;
          },
          0x0E => { // GetRef
            let n = heap.expect_ref(vm.ss[vm.ssp]);
            vm.ss[vm.ssp] = n;
            vm.pc = vm.pc + 1;
          },
          0x0F => { // MkRef
            println!("MkRef");
            vm.ss[vm.ssp] = heap.new_ref(vm.ss[vm.ssp], vm.roots());
            vm.pc += 1;
          },
          0x10 => { // RefAssign
            println!("RefAssign");
            heap.assign_ref(vm.ss[vm.ssp], vm.ss[vm.ssp - 1]);
            vm.ss[vm.ssp-1] = vm.ss[vm.ssp];
            vm.ssp -= 1;
            vm.pc += 1;
          },
          0x11 => { // GetBasic
            println!("GetBasic");
            let n = heap.expect_basic(vm.ss[vm.ssp]);
            vm.ssp -= 1;
            vm.sp += 1;
            vm.s[vm.sp] = n;
            vm.pc += 1;
          },
          0x12 => { // MkBasic
            println!("MkBasic");
            vm.ssp += 1;
            vm.ss[vm.ssp] = heap.new_basic(vm.s[vm.sp], vm.roots());
            vm.sp -= 1;
            vm.pc += 1;
          },
          0x13 => { // PushLoc(n)
            let n : i32 = (instr & 0x00FFFF00) >> 8;
            println!("PushLoc {n}");
            pushloc(vm, n);
            vm.pc += 1;
          },
          0x14 => { // PushGloba(n)
            let n : usize = ((instr & 0x00FFFF00) >> 8).try_into().unwrap();
            println!("PushGlobal {n}");
            let globals  = heap.expect_vector(vm.gp);
            if n < globals.len() {
              vm.ss[vm.ssp + 1] = globals[n];
              vm.ssp += 1;
              vm.pc += 1;
            } else {
              panic!("fewer than n globals");
            }
          },
          0x15 => { // Slide(n,m)
            let n : i32 = (instr & 0x0000FF00) >> 8;
            let m : i32 = (instr & 0x00FF0000) >> 16;
            println!("Slide {}",n);
            slide(vm,n.try_into().unwrap(), m.try_into().unwrap());
            vm.pc += 1;
          },
          0x16 => { // GetVec
            let elems = heap.expect_vector(vm.ss[vm.ssp]);
            println!("GetVec");
            for i in 0..elems.len() {
              vm.ss[vm.ssp + i] = elems[i];
            }
            vm.ssp = vm.ssp + elems.len() - 1;
            vm.pc += 1;
          },
          0x17 => { // MkVec(n)
            let n : usize = ((instr & 0x00FFFF00) >> 8).try_into().unwrap();
            println!("MkVec {n}");
            let mut vec = vec![0; n.try_into().unwrap()];
            vm.ssp = vm.ssp - n + 1;
            for i in 0..n {
              vec[i] = vm.ss[vm.ssp + i];
            };
            vm.ss[vm.ssp] = heap.new_vector(&vec[..], vm.roots());
            vm.pc += 1;
          },
          0x18 => { // MkFunVal(addr)
            let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("MkFunVal {code_addr}");
            let args_addr = heap.new_vector(&[0;0], vm.roots());
            vm.ss[vm.ssp] = heap.new_function(code_addr, args_addr, vm.ss[vm.ssp], vm.roots());
            vm.pc += 1;
          },
          0x19 => { // MkClos(addr)
            let code_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("MkClos {code_addr}");
            vm.ss[vm.ssp] = heap.new_closure(code_addr, vm.ss[vm.ssp], vm.roots());
            vm.pc += 1;
          },
          0x1A => { // Mark(return_addr)
            let return_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("Mark {return_addr}");
            mark(vm, return_addr);
            vm.pc += 1;
          },
          0x1B => { // Apply
            println!("Apply");
            apply(vm, &heap)
          },
          0x1C => { // TArg(numFormals)
            let num_formals : i32 = (instr & 0x0000FF00) >> 8;
            println!("TArg {num_formals}");
            if vm.ssp - vm.fp < num_formals.try_into().unwrap() {
              mkvec0(vm, &mut heap);
              wrap(vm, &mut heap);
              popenv(vm)
            } else {
              vm.pc += 1;
            }
          },
          0x1D => { // Return(numFormals)
            let num_formals : i32 = (instr & 0x0000FF00) >> 8;
            println!("Return {num_formals}");
            if vm.ssp - vm.fp - 1 == num_formals.try_into().unwrap() {
              popenv(vm)
            } else {
              slide(vm, num_formals.try_into().unwrap(), 1);
              apply(vm, &heap);
            }
          },
          0x1E => { // Alloc(num_closures_to_alloc)
            let num_closures_to_alloc : usize = ((instr & 0x0000FF00) >> 8).try_into().unwrap();
            println!("Return {num_closures_to_alloc}");
            for i in 1..(num_closures_to_alloc + 1) {
              vm.ss[vm.ssp + i] = heap.new_closure(0, 0, vm.roots());
            }
            vm.ssp += num_closures_to_alloc;
            vm.pc += 1;
          },
          0x1F => { // Rewrite(n)
            let n : usize = ((instr & 0x0000FF00) >> 8).try_into().unwrap();
            println!("Rewrite {n}");
            heap.rewrite(vm.ss[vm.ssp], vm.ss[vm.ssp - n]);
            vm.ssp -= 1;
            vm.pc += 1;
          },
          0x20 => { // Eval
            println!("Eval");
            match heap.is_closure(vm.ss[vm.ssp]) {
              true => {
                mark(vm, vm.pc + 1);
                pushloc(vm, 3);
                apply0(vm, &heap);
              },
              false => {
                vm.pc = vm.pc + 1;
              }
            }
          },
          0x21 => { // Update
            println!("Update");
            popenv(vm);
            rewrite(vm, &mut heap, 1);
          },
          0x22 => { // Load(numWords)
            panic!("unused") // TODO: remove this instruction
          },
          0x23 => { // LoadC(constantToLoad)
            let constant_to_load : i32 = (instr & 0x7FFFFF00) >> 8;
            println!("LoadC {constant_to_load}");
            vm.sp += 1;
            vm.s[vm.sp] = constant_to_load;
            vm.pc += 1;
          },
          0x24 => { // Jump(destAddr)
            let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("Jump {dest_addr}");
            vm.pc = dest_addr;
          },
          0x25 => { // JumpZ(destAddr)
            let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("JumpZ {dest_addr}");
            vm.pc = if vm.s[vm.sp] == 0 { dest_addr } else { vm.pc + 1 };
            vm.sp -= 1;
          },
          0x26 => { // JumpNZ(destAddr)
            let dest_addr : i32 = (instr & 0x00FFFF00) >> 8;
            println!("JumpNZ {dest_addr}");
            vm.pc = if vm.s[vm.sp] != 0 { dest_addr } else { vm.pc + 1 };
            vm.sp -= 1;
          },
          0x27 => { // JumpI(jump_offset)
            let jump_offset : i32 = (instr & 0x00FFFF00) >> 8;
            println!("JumpI {jump_offset}");
            vm.pc = vm.s[vm.sp] + jump_offset;
            vm.sp -= 1;
          },
          0x28 => { //MkTuple
            let tuple_addr = heap.new_tuple(vm.ss[vm.ssp], vm.roots());
            vm.ss[vm.ssp] = tuple_addr;
            vm.pc += 1;
          },
          0x29 => { //GetTuple
            let elems_addr = heap.expect_tuple(vm.ss[vm.ssp]);
            let elems = heap.expect_vector(elems_addr);
            for i in 0..elems.len() {
              vm.ss[vm.ssp + i] = elems[i];
            }
            vm.ssp = vm.ssp + elems.len() - 1;
            vm.pc += 1;
          },
          0x2A => { // GetTag
            println!("GetTag");
            let (variant_id, _) = heap.expect_sum(vm.ss[vm.ssp]);
            vm.sp += 1;
            vm.s[vm.sp] = variant_id as i32;
            vm.pc += 1;
          },
          _ => panic!("invalid instruction")
      }
  }
  heap.expect_basic(vm.ss[vm.ssp])
}