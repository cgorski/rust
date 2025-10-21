#![feature(view_types)]
#![allow(incomplete_features)]

// RESTRICTION TEST: Trait methods with view types are not supported
// This test verifies that both trait definitions and trait impls with view types
// are properly rejected with clear error messages (not ICE)

// Test 1: Simplest possible trait with view type
trait Counter {
    fn increment(&{mut count} mut self); //~ ERROR patterns aren't allowed in functions without bodies
    //~| WARN this was previously accepted by the compiler but is being phased out
}

struct MyCounter {
    count: usize,
    name: String,
}

impl Counter for MyCounter {
    fn increment(&{mut count} mut self) { //~ ERROR view types are not supported on trait method implementations
        self.count += 1;
    }
}

fn main() {
    let mut counter = MyCounter {
        count: 0,
        name: String::from("test"),
    };

    // Call trait method directly
    counter.increment();

    println!("Count: {}", counter.count);
}
