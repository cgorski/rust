#![feature(view_types)]
#![allow(unused, incomplete_features)]

// Auxiliary crate for testing cross-crate view types usage

// =============================================================================
// Basic struct with view-typed methods
// =============================================================================

pub struct Counter {
    pub count: usize,
    pub data: Vec<i32>,
}

impl Counter {
    pub(crate) fn new() -> Self {
        Counter {
            count: 0,
            data: Vec::new(),
        }
    }

    // View-typed method: only accesses count
    pub(crate) fn increment(&{mut count} mut self) -> usize {
        self.count += 1;
        self.count
    }

    // View-typed method: only accesses data
    pub(crate) fn add_item(&{mut data} mut self, item: i32) {
        self.data.push(item);
    }

    // This demonstrates the key benefit across crates:
    // External crates can call increment while data is borrowed
    pub(crate) fn process(&mut self) {
        for item in &mut self.data {
            let id = self.increment();
            *item = id as i32;
        }
    }
}

// =============================================================================
// Generic struct with view types
// =============================================================================

pub struct Wrapper<T> {
    pub inner: T,
    pub metadata: usize,
}

impl<T> Wrapper<T> {
    pub(crate) fn new(inner: T) -> Self {
        Wrapper { inner, metadata: 0 }
    }

    pub(crate) fn update_metadata(&{mut metadata} mut self, value: usize) {
        self.metadata = value;
    }

    pub(crate) fn get_inner(&{inner} self) -> &T {
        &self.inner
    }
}

// =============================================================================
// Struct with lifetime parameters
// =============================================================================

pub struct Borrowed<'a> {
    pub reference: &'a str,
    pub owned: String,
}

impl<'a> Borrowed<'a> {
    pub(crate) fn update_owned(&{mut owned} mut self, new_value: String) {
        self.owned = new_value;
    }
}

// =============================================================================
// Multiple view-typed methods on same struct
// =============================================================================

pub struct MultiView {
    pub field_a: i32,
    pub field_b: i32,
    pub field_c: String,
}

impl MultiView {
    pub(crate) fn inc_a(&{mut field_a} mut self) {
        self.field_a += 1;
    }

    pub(crate) fn inc_b(&{mut field_b} mut self) {
        self.field_b += 1;
    }

    pub(crate) fn update_c(&{mut field_c} mut self, val: String) {
        self.field_c = val;
    }

    // All immutable
    pub(crate) fn read_all(&{field_a, field_b, field_c} self) -> (i32, i32, &str) {
        (self.field_a, self.field_b, &self.field_c)
    }
}

// =============================================================================
// Nested generics
// =============================================================================

pub struct NestedGeneric<T> {
    pub outer: Vec<T>,
    pub counter: usize,
}

impl<T> NestedGeneric<T> {
    pub(crate) fn increment_counter(&{mut counter} mut self) {
        self.counter += 1;
    }
}

// =============================================================================
// Standalone functions (not methods)
// =============================================================================

pub struct External {
    pub value: i32,
}

// Free function with view type
pub(crate) fn update_value(s: &{mut value} mut External, new_val: i32) {
    s.value = new_val;
}
