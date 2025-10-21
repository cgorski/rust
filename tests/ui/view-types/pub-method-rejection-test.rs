//@ check-fail
#![feature(view_types)]
#![allow(incomplete_features)]

// Test: Public Methods with View Types Should Be Rejected
//
// This test verifies that the encapsulation restriction is enforced:
// - pub methods with view types should be rejected
// - pub(crate) and pub(super) should work (internal to crate/module)
// - private methods should work
//
// Rationale: View types expose field names in the signature, which would
// break encapsulation if allowed on truly public (cross-crate) APIs.

mod inner {
    pub struct Counter {
        pub(super) count: usize,
        pub(super) data: Vec<i32>,
    }

    impl Counter {
        // Should FAIL: pub method with view type breaks encapsulation
        pub fn increment(&{mut count} mut self) {
            //~^ ERROR view types are not allowed on public functions
            self.count += 1;
        }

        // Should WORK: pub(crate) is internal to crate
        pub(crate) fn decrement(&{mut count} mut self) {
            self.count -= 1;
        }

        // Should WORK: pub(super) is internal to parent module
        pub(super) fn reset(&{mut count} mut self) {
            self.count = 0;
        }

        // Should WORK: private method
        fn add(&{mut count} mut self, val: usize) {
            self.count += val;
        }
    }
}

// Test with generic struct
pub struct Container<T> {
    meta: usize,
    data: T,
}

impl<T> Container<T> {
    // Should FAIL: pub method with view type on generic struct
    pub fn update_meta(&{mut meta} mut self) {
        //~^ ERROR view types are not allowed on public functions
        self.meta += 1;
    }

    // Should WORK: pub(crate) with generics
    pub(crate) fn update_meta_internal(&{mut meta} mut self) {
        self.meta += 1;
    }
}

// Test with trait implementation
pub trait Processor {
    fn process(&{mut state} self);
}

fn main() {
    let mut counter = inner::Counter {
        count: 0,
        data: vec![],
    };

    // These should work (internal methods)
    counter.decrement();
    counter.reset();

    println!("Counter: {}", counter.count);
}
