use mama_rust::virtual_machine::{VirtualMachine};
use std::env;

fn main() {
    let args : Vec<String> = env::args().collect();
    let mut vm = VirtualMachine::from_file(&args[1]);
    let res = vm.execute();
    println!("result: {res}")
}
