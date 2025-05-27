use mama_rust::{exec::execute, virtual_machine::from_file};
use std::env;

fn main() {
    let args : Vec<String> = env::args().collect();
    let mut vm = from_file(&args[1]);
    let res = execute(&mut vm);
    println!("result: {res}")
}
