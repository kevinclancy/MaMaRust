# Mama Rust 2 Project

## Code Style Preferences

- When using `assert!()` macros, omit the second argument (error message) as the assertion condition is self-documenting.

## Comment Policy

- Avoid obvious comments inside function bodies. Code should be self-explanatory.
- Add comments for function interfaces that:
  - Connect the code to the application domain
  - Compensate for shortcomings in the type system
- Comment individual components of data definitions:
  - Each field of a struct/record should be commented
  - Each variant of an enum should be commented