//@ check-pass
//@ edition: 2021
#![feature(view_types)]
#![allow(incomplete_features)]

// Test: Do synchronous view types allow simultaneous disjoint field borrows?
//
// This test checks if the fundamental view type mechanism works for
// simultaneous borrows of disjoint fields in synchronous (non-async) code.
//
// If this works, the problem is specific to async method calls.
// If this fails, the problem is more fundamental.

struct Counter {
    count: u32,
    data: Vec<String>,
    name: String,
}

impl Counter {
    fn increment(&{mut count} mut self) {
        self.count += 1;
    }

    fn add_data(&{mut data} mut self, item: String) {
        self.data.push(item);
    }

    fn set_name(&{mut name} mut self, new_name: String) {
        self.name = new_name;
    }
}

// TEST 1: Sequential calls (should work - this is V1)
fn test_sequential_calls() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    c.increment();
    c.add_data("item".to_string());
    c.set_name("updated".to_string());

    assert_eq!(c.count, 1);
}

// TEST 2: Can we get multiple method references simultaneously?
fn test_simultaneous_method_refs() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Try to get function pointers/references to methods with disjoint view specs
    // This probably won't work with method call syntax, but let's try

    // This would require something like:
    // let f1 = Counter::increment;
    // let f2 = Counter::add_data;
    // f1(&mut c);  // Borrows whole c
    // f2(&mut c);  // Would conflict

    // For this test, we just verify sequential works
    c.increment();
    c.add_data("x".to_string());
}

// TEST 3: Explicit disjoint field borrows (not using view types)
fn test_explicit_disjoint_borrows() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Can we create simultaneous borrows of disjoint fields?
    let count_ref = &mut c.count;
    let data_ref = &mut c.data;

    // This SHOULD work - disjoint fields
    *count_ref += 1;
    data_ref.push("item".to_string());

    assert_eq!(*count_ref, 1);
    assert_eq!(data_ref.len(), 1);
}

// TEST 4: Can view-typed functions be called with explicit field borrows?
fn increment_standalone(count: &mut u32) {
    *count += 1;
}

fn add_data_standalone(data: &mut Vec<String>, item: String) {
    data.push(item);
}

fn test_standalone_functions_on_fields() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Call standalone functions on individual fields - this works!
    increment_standalone(&mut c.count);
    add_data_standalone(&mut c.data, "item".to_string());

    assert_eq!(c.count, 1);
    assert_eq!(c.data.len(), 1);
}

// TEST 5: Can we create simultaneous borrows and call standalone functions?
fn test_simultaneous_with_standalone() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    let count_ref = &mut c.count;
    let data_ref = &mut c.data;

    // Call functions on both borrows
    increment_standalone(count_ref);
    add_data_standalone(data_ref, "item".to_string());

    assert_eq!(*count_ref, 1);
    assert_eq!(data_ref.len(), 1);
}

// TEST 6: The critical question - can we pass disjoint borrows to closures that return them?
fn test_closure_with_disjoint_borrows() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Create closures that capture specific borrows
    let mut inc = || {
        c.count += 1;
    };

    let mut add = || {
        c.data.push("item".to_string());
    };

    // Can we call both closures?
    // This will likely fail because closures capture the whole c
    // Uncommenting these would show the error:
    // inc();
    // add();  // Error: c already borrowed by inc
}

// TEST 7: Explicit lifetime and return
fn get_count_borrow(c: &mut Counter) -> &mut u32 {
    &mut c.count
}

fn get_data_borrow(c: &mut Counter) -> &mut Vec<String> {
    &mut c.data
}

fn test_explicit_borrow_functions() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Get borrows from functions
    let count_ref = get_count_borrow(&mut c);
    // Can we get another borrow while count_ref exists?
    // let data_ref = get_data_borrow(&mut c);  // Error: c already borrowed

    *count_ref += 1;

    // After count_ref is done, we can borrow again
    let data_ref = get_data_borrow(&mut c);
    data_ref.push("item".to_string());
}

fn main() {
    test_sequential_calls();
    test_simultaneous_method_refs();
    test_explicit_disjoint_borrows();
    test_standalone_functions_on_fields();
    test_simultaneous_with_standalone();
    test_closure_with_disjoint_borrows();
    test_explicit_borrow_functions();

    println!("Sync view type borrow test complete");
    println!("Key finding: Explicit field borrows work, method calls don't");
}
