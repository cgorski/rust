//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// Simple test to examine MIR structure for view-typed calls

struct S {
    field_a: u32,
    field_b: String,
}

impl S {
    // Method with view type - only accesses field_a
    fn increment(&{mut field_a} mut self) -> u32 {
        self.field_a += 1;
        self.field_a
    }

    // Caller that doesn't create conflicts
    fn test(&mut self) -> u32 {
        // This should work - we're not borrowing anything else
        self.increment()
    }
}

fn main() {
    let mut s = S {
        field_a: 0,
        field_b: String::from("hello"),
    };

    let result = s.test();
    println!("Result: {}", result);
}
