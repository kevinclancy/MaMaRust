
const MAX_STACK_MEM : usize = 20000;
const MAX_HEAP_MEM : usize = 10000;

fn toInstructions(bytes : Vec<u8>) -> Vec<u32> {
    let mut result : Vec<u32> = vec![];
    let mut i = 0;
    while (i < bytes.len()) {
        result.push(Into::<u32>::into(bytes[i]) << 0
                    | Into::<u32>::into(bytes[i+1]) << 8
                    | Into::<u32>::into(bytes[i+2]) << 16
                    | Into::<u32>::into(bytes[i+3]) << 24);
        i += 4;
    }
    result
}

fn main() {
    let f = toInstructions(std::fs::read("prog.bin").unwrap());
    // program counter
    let mut pc = 0;
    // stack pointer
    let mut sp = 0;
    // global pointer
    let mut gp = 0;
    // frame pointer
    let mut fp = 1;

    // Stack
    let s = [0 as u32; MAX_STACK_MEM/4];
    // Heap
    let h = [0 as u8; MAX_HEAP_MEM];


    while (true) {
        match (f[pc] & 0x00000011) {
            0x00 => break,
            0x01 => // mul

            _ => panic!("todo")
        }
    }
}
