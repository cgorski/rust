//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TDD TEST: pub(super) visibility with view types
//
// Current Status: RED (will fail - only pub(crate) and private allowed)
// Target Status: GREEN (should pass once pub(super) support added)
//
// This test validates that view types work with pub(super) visibility.
// pub(super) is more restrictive than pub(crate) but less than private,
// so it should be allowed under our restriction policy.

mod parent {
    pub(super) struct Counter {
        pub(super) count: usize,
        pub(super) data: Vec<i32>,
    }

    impl Counter {
        pub(super) fn new() -> Self {
            Counter {
                count: 0,
                data: Vec::new(),
            }
        }

        // pub(super) function with view type - should be ALLOWED
        pub(super) fn increment(&{mut count} mut self) -> usize {
            self.count += 1;
            self.count
        }

        // Another pub(super) view-typed method
        pub(super) fn add_data(&{mut data} mut self, item: i32) {
            self.data.push(item);
        }

        // pub(super) using disjoint fields
        pub(super) fn process(&mut self) {
            for item in &mut self.data {
                let id = self.increment(); // Disjoint: count vs data
                *item = id as i32;
            }
        }
    }

    // Can call pub(super) methods from same module
    pub(super) fn same_module_usage() {
        let mut counter = Counter::new();
        counter.add_data(1);
        counter.add_data(2);

        // Disjoint borrowing works
        for item in &mut counter.data {
            let id = counter.increment();
            *item = id as i32;
        }
    }
}

// Can call pub(super) methods from the parent's scope
fn parent_scope_usage() {
    let mut counter = parent::Counter::new();

    // All these should work - we're in the parent scope
    counter.increment();
    counter.add_data(5);
    counter.process();

    // Disjoint borrowing works at this visibility level
    for item in &mut counter.data {
        let id = counter.increment();
        *item = id as i32;
    }
}

// =============================================================================
// Test pub(super) with nested modules
// =============================================================================

mod outer {
    pub(super) struct Data {
        pub(super) value: i32,
        pub(super) metadata: String,
    }

    pub(super) mod inner {
        use super::Data;

        impl Data {
            // pub(super) within nested module
            // This is pub(super) relative to 'inner', so visible in 'outer'
            pub(super) fn update_value(&{mut value} mut self, val: i32) {
                self.value = val;
            }

            pub(super) fn update_metadata(&{mut metadata} mut self, meta: String) {
                self.metadata = meta;
            }
        }

        // Can call from same module
        pub(super) fn inner_usage() {
            let mut data = Data { value: 0, metadata: String::new() };

            let _meta_ref = &mut data.metadata;
            data.update_value(42); // Disjoint from metadata
        }
    }

    // Can call from parent module (outer)
    pub(super) fn outer_usage() {
        let mut data = Data { value: 0, metadata: String::new() };

        // These methods are pub(super) from inner's perspective,
        // which makes them visible in outer (the parent)
        data.update_value(100);
        data.update_metadata(String::from("test"));

        // Disjoint borrowing
        let _value_ref = &data.value;
        data.update_metadata(String::from("changed")); // OK - disjoint
    }
}

// =============================================================================
// Test pub(in path) syntax (bonus - should also be allowed)
// =============================================================================

mod container {
    pub(super) struct Item {
        pub(super) field_a: i32,
        pub(super) field_b: String,
    }

    impl Item {
        // pub(in crate) is same as pub(crate), should work
        pub(in crate) fn method_pub_in_crate(&{mut field_a} mut self) {
            self.field_a = 1;
        }

        // pub(in container) means pub within 'container' module
        pub(in container) fn method_pub_in_container(&{mut field_b} mut self) {
            self.field_b = String::from("test");
        }
    }
}

fn test_pub_in_path() {
    let mut item = container::Item { field_a: 0, field_b: String::new() };
    item.method_pub_in_crate();
    // method_pub_in_container might not be visible here depending on path
}

// =============================================================================
// Verification: The restriction still blocks unqualified pub
// =============================================================================

mod restricted {
    pub(super) struct S {
        pub(super) field: i32,
    }

    impl S {
        // This should STILL be rejected (unqualified pub)
        // Uncomment to verify restriction still works:
        // pub fn not_allowed(&{mut field} mut self) {}
    }
}

// =============================================================================
// Main test execution
// =============================================================================

fn main() {
    parent::same_module_usage();
    parent_scope_usage();
    // Note: inner_usage is pub(super) within inner module,
    // so it's visible to outer module but not to root
    outer::outer_usage();
    test_pub_in_path();

    println!("SUCCESS: pub(super) visibility works with view types!");
}
