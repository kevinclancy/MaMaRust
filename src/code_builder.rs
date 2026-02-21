pub fn halt() -> i32 {
    0x00
}

pub fn mul() -> i32 {
    0x01
}

pub fn add() -> i32 {
    0x02
}

pub fn sub() -> i32 {
    0x03
}

pub fn leq() -> i32 {
    0x04
}

pub fn eq() -> i32 {
    0x05
}

pub fn geq() -> i32 {
    0x06
}

pub fn gt() -> i32 {
    0x07
}

pub fn lt() -> i32 {
    0x08
}

pub fn neg() -> i32 {
    0x09
}

pub fn mk_sum(n: u16) -> i32 {
    let op_id = 0x0A;
    op_id | ((n as i32) << 8)
}

pub fn tsum(jump_table_addr: u16) -> i32 {
    let op_id = 0x0B;
    op_id | ((jump_table_addr as i32) << 8)
}

pub fn tget_constructor_arg() -> i32 {
    0x0C
}

pub fn pop() -> i32 {
    0x0D
}

pub fn get_ref() -> i32 {
    0x0E
}

pub fn mk_ref() -> i32 {
    0x0F
}

pub fn ref_assign() -> i32 {
    0x10
}

pub fn get_basic() -> i32 {
    0x11
}

pub fn mk_basic() -> i32 {
    0x12
}

pub fn push_loc(n: i16) -> i32 {
    let op_id = 0x13;
    let n = n & 0xFFFFu16 as i16;
    op_id | ((n as i32) << 8)
}

pub fn push_global(n: u16) -> i32 {
    let op_id = 0x14;
    let n = n & 0xFFFF;
    op_id | ((n as i32) << 8)
}

pub fn slide(n: u8, m: u8) -> i32 {
    let op_id = 0x15;
    let n = n & 0xFF;
    let m = m & 0xFF;
    op_id | ((n as i32) << 8) | ((m as i32) << 16)
}

pub fn get_vec() -> i32 {
    0x16
}

pub fn mk_vec(n: u16) -> i32 {
    let op_id = 0x17;
    op_id | ((n as i32) << 8)
}

pub fn mk_fun_val(addr: u16) -> i32 {
    let op_id = 0x18;
    op_id | ((addr as i32) << 8)
}

pub fn mk_clos(addr: u16) -> i32 {
    let op_id = 0x19;
    op_id | ((addr as i32) << 8)
}

pub fn mark(addr: u16) -> i32 {
    let op_id = 0x1A;
    op_id | ((addr as i32) << 8)
}

pub fn apply() -> i32 {
    0x1B
}

pub fn targ(num_formals: u8) -> i32 {
    let op_id = 0x1C;
    op_id | ((num_formals as i32) << 8)
}

pub fn return_(num_formals: u8) -> i32 {
    let op_id = 0x1D;
    op_id | ((num_formals as i32) << 8)
}

pub fn alloc(n: u8) -> i32 {
    let op_id = 0x1E;
    op_id | ((n as i32) << 8)
}

pub fn rewrite(n: u8) -> i32 {
    let op_id = 0x1F;
    op_id | ((n as i32) << 8)
}

pub fn eval() -> i32 {
    0x20
}

pub fn update() -> i32 {
    0x21
}

pub fn load_c(constant: i32) -> i32 {
    let op_id = 0x23;
    let constant = constant & 0x7FFFFF;
    op_id | (constant << 8)
}

pub fn jump(dest_addr: u16) -> i32 {
    let op_id = 0x24;
    op_id | ((dest_addr as i32) << 8)
}

pub fn jump_z(dest_addr: u16) -> i32 {
    let op_id = 0x25;
    op_id | ((dest_addr as i32) << 8)
}

pub fn jump_nz(dest_addr: u16) -> i32 {
    let op_id = 0x26;
    op_id | ((dest_addr as i32) << 8)
}

pub fn jump_i(jump_offset: u16) -> i32 {
    let op_id = 0x27;
    op_id | ((jump_offset as i32) << 8)
}

pub fn mk_tuple() -> i32 {
    0x28
}

pub fn get_tuple() -> i32 {
    0x29
}

/// Reads the variant tag from the sum value at the top of the shadow stack
/// and pushes it as an integer onto the basic stack
pub fn get_tag() -> i32 {
    0x2A
}

pub fn symbolic_addr(addr: u16) -> i32 {
    (0xFFu32 as i32) | ((addr as i32) << 8)
}