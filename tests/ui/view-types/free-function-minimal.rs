#![feature(view_types)]
#![allow(incomplete_features, unused)]

// V1 RESTRICTION TEST: Free functions with view types are not supported
// This test verifies that the compiler emits a clear error message

struct Data {
    a: i32,
    b: i32,
}

// Free function with view type - V1 restriction: not supported
fn update_a(d: &{mut a} mut Data) { //~ ERROR view types are not supported on free functions
    d.a += 1;
}

// Method version with view type - for comparison
impl Data {
    fn update_a_method(&{mut a} mut self) {
        self.a += 1;
    }
}

// V1: The free function definition above is rejected with a clear error.
// No need to test calling it - the definition itself is the error point.

fn test_method_works() {
    let mut data = Data { a: 0, b: 0 };

    // Borrow field b immutably
    let _b_ref = &data.b;

    // This WORKS: method with view type properly borrows only field a
    data.update_a_method();  // ✅ Works in V1!

    // Both borrows coexist
    println!("{}", _b_ref);
}

fn main() {
    // Demonstrate that methods with view types work correctly in V1
    test_method_works();

    println!("Method version works! Free functions not supported in V1.");
}
