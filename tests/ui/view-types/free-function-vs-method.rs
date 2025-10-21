//@ check-pass
#![feature(view_types)]
#![allow(incomplete_features, unused)]

// Comparison: Method with view type (WORKS) vs Free function with view type (FAILS)

struct Data {
    a: i32,
    b: i32,
}

// Method version with view type - THIS WORKS
impl Data {
    fn update_a_method(&{mut a} mut self) {
        self.a += 1;
    }
}

fn test_method_works() {
    let mut data = Data { a: 0, b: 0 };

    // Borrow field b immutably
    let _b_ref = &data.b;

    // This WORKS: method with view type properly borrows only field a
    data.update_a_method();  // ✅ Compiles!

    // Both borrows coexist
    assert_eq!(*_b_ref, 0);
    assert_eq!(data.a, 1);
}

fn main() {
    test_method_works();
    println!("Method with view type works correctly!");
}
