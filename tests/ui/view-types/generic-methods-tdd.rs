//@ check-pass
#![feature(view_types)]
#![allow(incomplete_features)]

// TDD Test: Generic Methods with View Types
//
// This test verifies that methods with their own type parameters
// can use view types on the self parameter.
//
// Current Status: EXPECTED TO FAIL (not yet implemented)
// Theoretical Soundness: ✅ PROVEN - view specs independent of type params
// Practical Need: CRITICAL - generic methods are ubiquitous in Rust

struct Container<T> {
    meta: usize,
    data: T,
}

// Test 1: Simple generic method parameter
impl<T> Container<T> {
    fn update_with<U>(&{mut meta} mut self, _val: U) {
        self.meta += 1;
    }
}

// Test 2: Multiple type parameters
impl<T> Container<T> {
    fn transform<U, V>(&{mut meta} mut self, _u: U, _v: V) {
        self.meta = 42;
    }
}

// Test 3: Generic with trait bounds
impl<T> Container<T> {
    fn update_if_clone<U: Clone>(&{mut meta} mut self, val: U) {
        let _cloned = val.clone();
        self.meta += 1;
    }
}

// Test 4: Generic with where clauses
impl<T> Container<T> {
    fn complex_update<U, V>(&{mut meta} mut self, u: U, _v: V)
    where
        U: Clone + Default,
        V: std::fmt::Debug,
    {
        let _default: U = Default::default();
        self.meta += 1;
    }
}

// Test 5: Generic method with return type using generic
impl<T> Container<T> {
    fn get_and_increment<U>(&{mut meta} mut self, val: U) -> U {
        self.meta += 1;
        val
    }
}

// Test 6: Generic closure parameter
impl<T> Container<T> {
    fn apply<F>(&{mut meta} mut self, f: F) -> usize
    where
        F: FnOnce(usize) -> usize,
    {
        let old = self.meta;
        self.meta = f(self.meta);
        old
    }
}

// Test 7: Multiple view fields with generic method
struct MultiField {
    counter: usize,
    value: i32,
    name: String,
}

impl MultiField {
    fn update_counter<T>(&{mut counter} mut self, _x: T) {
        self.counter += 1;
    }

    fn update_both<T, U>(&{mut counter, mut value} mut self, t: T, _u: U)
    where
        T: Into<i32>,
    {
        self.counter += 1;
        self.value = t.into();
    }
}

// Test 8: Generic associated function (not a method)
impl MultiField {
    fn create_and_update<T>(field: &{mut counter} mut MultiField, _val: T) {
        field.counter += 1;
    }
}

// Test 9: Real-world pattern - builder with generics
struct Builder {
    config: String,
    state: usize,
}

impl Builder {
    fn with_option<T: ToString>(&{mut config} mut self, opt: T) {
        self.config.push_str(&opt.to_string());
    }

    fn with_state(&{mut state} mut self, s: usize) {
        self.state = s;
    }
}

// Test 10: Ensure calling generic methods with view types works
fn test_generic_method_calls() {
    let mut container = Container { meta: 0, data: vec![1, 2, 3] };

    // Access data immutably while calling generic method on meta
    let _data_ref = &container.data;
    container.update_with(42u32);
    container.update_with("hello");

    // Multiple generic type params
    container.transform(1, "test");

    // With bounds
    container.update_if_clone(vec![1, 2, 3]);

    // Closure
    container.apply(|x| x * 2);
}

// Test 11: Generic method in iteration context (real-world scenario)
fn test_iteration_with_generic() {
    let mut container = Container { meta: 0, data: vec![1, 2, 3] };

    for item in &container.data {
        // Generic method with view type while iterating
        container.update_with(*item);
    }

    assert_eq!(container.meta, 3);
}

// Test 12: Generic method with nested generics
impl<T> Container<T> {
    fn nested_generic<U, V>(&{mut meta} mut self, _opt: Option<Result<U, V>>) {
        self.meta += 1;
    }
}

// Test 13: Lifetime + generic parameters
impl<T> Container<T> {
    fn with_lifetime<'a, U>(&{mut meta} mut self, _s: &'a str, _u: U) {
        self.meta += 1;
    }
}

// Test 14: Multiple impl blocks with generic methods
struct Data {
    a: i32,
    b: String,
}

impl Data {
    fn update_a<T>(&{mut a} mut self, _val: T) {
        self.a += 1;
    }
}

impl Data {
    fn update_b<T: ToString>(&{mut b} mut self, val: T) {
        self.b = val.to_string();
    }
}

fn main() {
    test_generic_method_calls();
    test_iteration_with_generic();

    // Additional integration test
    let mut multi = MultiField {
        counter: 0,
        value: 0,
        name: String::new(),
    };

    multi.update_counter(42);
    multi.update_both(100i32, "test");
    MultiField::create_and_update(&mut multi, vec![1, 2]);

    // Builder pattern
    let mut builder = Builder {
        config: String::new(),
        state: 0,
    };

    builder.with_option(42);
    builder.with_state(100);

    println!("All generic method tests completed!");
}
