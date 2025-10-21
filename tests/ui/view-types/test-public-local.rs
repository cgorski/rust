//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// Test that pub(crate) view-typed methods work within the same crate
// V1 restricts view types to pub(crate) or private functions (matching the paper's recommendation)

pub mod library {
    pub struct Counter {
        pub count: usize,
        pub data: Vec<i32>,
    }

    impl Counter {
        pub fn new() -> Self {
            Counter {
                count: 0,
                data: Vec::new(),
            }
        }

        // pub(crate) method with view type (V1 restriction)
        pub(crate) fn increment(&{mut count} mut self) -> usize {
            self.count += 1;
            self.count
        }

        // Another pub(crate) view-typed method
        pub(crate) fn add_data(&{mut data} mut self, item: i32) {
            self.data.push(item);
        }

        // Public method that uses view-typed helpers (allowed)
        pub fn process_all(&mut self) {
            for item in &mut self.data {
                let id = self.increment(); // pub(crate) view-typed call in same crate
                *item = id as i32;
            }
        }
    }
}

// Use the public API from another module in same crate
fn test_public_methods() {
    let mut counter = library::Counter::new();
    counter.data = vec![0, 0, 0]; // Initialize data

    // Can we call public view-typed methods?
    // If serialization worked, this would work across crates too
    for item in &mut counter.data {
        let id = counter.increment(); // Calling public view-typed method
        *item = id as i32;
    }

    assert_eq!(counter.count, 3);
    assert_eq!(counter.data, vec![1, 2, 3]);
}

// Test calling public methods via re-export
pub use library::Counter as ExportedCounter;

fn test_reexported() {
    let mut c = ExportedCounter::new();
    c.process_all();
}

fn main() {
    test_public_methods();
    test_reexported();
    println!("Public view-typed methods work in same crate!");
}
