use std::collections::HashMap;

/// Resolves symbolic addresses in a sequence of i32 instructions.
/// Symbolic addresses begin with byte 0xFF and contain a 24-bit address in the lower bits.
pub fn resolve(instructions: &[i32]) -> Vec<i32> {
    // First pass: build address map from symbolic addresses to absolute positions
    let mut address_map = HashMap::new();
    let mut absolute_pos = 0;

    for &instruction in instructions {
        if is_symbolic_address(instruction) {
            let symbolic_addr = extract_symbolic_address(instruction);
            address_map.insert(symbolic_addr, absolute_pos);
        } else {
            absolute_pos += 1;
        }
    }

    let mut resolved = Vec::new();
    for &instruction in instructions {
        if is_symbolic_address(instruction) {
            continue;
        }

        let resolved_instruction = resolve_instruction_addresses(instruction, &address_map);
        resolved.push(resolved_instruction);
    }

    resolved
}

/// Checks if an instruction is a symbolic address marker (begins with 0xFF)
fn is_symbolic_address(instruction: i32) -> bool {
    (instruction & 0xFF) == 0xFF
}

/// Extracts the 16-bit symbolic address from a symbolic address marker
fn extract_symbolic_address(instruction: i32) -> u16 {
    ((instruction >> 8) & 0xFFFF) as u16
}

/// Resolves symbolic address references within an instruction
fn resolve_instruction_addresses(instruction: i32, address_map: &HashMap<u16, usize>) -> i32 {
    let opcode = instruction & 0xFF;

    match opcode {
        0x0B | // tsum
        0x18 | // mk_fun_val
        0x19 | // mk_clos
        0x1A | // mark
        0x24 | // jump
        0x25 | // jump_z
        0x26 | // jump_nz
        0x27 => { // jump_i
            let addr_arg = ((instruction >> 8) & 0xFFFF) as u16;
            if let Some(&resolved_addr) = address_map.get(&addr_arg) {
                (instruction & 0xFF) | ((resolved_addr as i32) << 8)
            } else {
                instruction
            }
        }
        _ => instruction
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code_builder::{symbolic_addr, jump, load_c};

    #[test]
    fn test_resolve_simple_jump() {
        let instructions = vec![
            load_c(42),
            jump(100),
            load_c(1),
            symbolic_addr(100),
            load_c(2),
        ];

        let resolved = resolve(&instructions);

        // Expected: load_c(42), jump(3), load_c(1), load_c(2)
        assert_eq!(resolved.len(), 4);
        assert_eq!(resolved[1] & 0xFF, jump(3) & 0xFF); // same opcode
        assert_eq!((resolved[1] >> 8) & 0xFFFF, 3); // resolved address
    }

    #[test]
    fn test_extract_symbolic_address() {
        let symbolic = symbolic_addr(123);
        assert!(is_symbolic_address(symbolic));
        assert_eq!(extract_symbolic_address(symbolic), 123);
    }
}