//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// This test demonstrates the core pattern that view types should enable.
// If our implementation is working correctly, this should compile without errors.

struct Counter {
    count: usize,
    data: Vec<i32>,
}

impl Counter {
    // View type: only accesses the count field
    fn increment(&{mut count} mut self) -> usize {
        self.count += 1;
        self.count
    }

    // This should compile because:
    // 1. We mutably borrow self.data in the loop
    // 2. We call increment() which only borrows self.count (per view type)
    // 3. count and data are disjoint fields (proven in Core_Proven.v)
    // 4. Therefore no conflict exists
    fn process_all(&mut self) {
        for item in &mut self.data {
            let current_count = self.increment();
            *item = current_count as i32;
        }
    }
}

fn main() {
    let mut c = Counter {
        count: 0,
        data: vec![0, 0, 0],
    };

    c.process_all();

    // After processing, data should be [1, 2, 3] and count should be 3
    assert_eq!(c.data, vec![1, 2, 3]);
    assert_eq!(c.count, 3);

    println!("Success! View types enabled disjoint field borrowing!");
}
