//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// Edge cases test suite for view types
// Tests unusual but valid scenarios

// =============================================================================
// Edge Case 1: Single field struct
// =============================================================================

struct SingleField {
    only: i32,
}

impl SingleField {
    fn access_only(&{mut only} mut self) {
        self.only = 42;
    }
}

// =============================================================================
// Edge Case 2: Many fields (stress test field indexing)
// =============================================================================

struct ManyFields {
    f0: i32,
    f1: i32,
    f2: i32,
    f3: i32,
    f4: i32,
    f5: i32,
    f6: i32,
    f7: i32,
    f8: i32,
    f9: i32,
    f10: String,
}

impl ManyFields {
    fn access_last(&{mut f10} mut self) {
        self.f10 = String::from("last");
    }

    fn access_middle(&{mut f5} mut self) {
        self.f5 = 100;
    }

    fn disjoint_many(&mut self) {
        // Access f10 while f0 is borrowed
        let _first = &self.f0;
        self.access_last(); // Should work - f10 ⊥ f0
    }
}

// =============================================================================
// Edge Case 3: Generic struct with multiple type parameters
// =============================================================================

struct Generic<T, U> {
    first: T,
    second: U,
    metadata: usize,
}

impl<T, U> Generic<T, U> {
    fn update_metadata(&{mut metadata} mut self) {
        self.metadata += 1;
    }

    fn with_borrows(&mut self) {
        let _first = &self.first;
        let _second = &self.second;
        self.update_metadata(); // Works - metadata disjoint from first and second
    }
}

// =============================================================================
// Edge Case 4: Lifetime parameters in struct
// =============================================================================

struct WithLifetimes<'a, 'b> {
    first: &'a str,
    second: &'b str,
    counter: usize,
}

impl<'a, 'b> WithLifetimes<'a, 'b> {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn use_refs(&mut self) {
        let _f = self.first;
        let _s = self.second;
        self.increment(); // Works
    }
}

// =============================================================================
// Edge Case 5: Zero-sized types
// =============================================================================

struct WithZst {
    zst: (),
    data: Vec<i32>,
    marker: std::marker::PhantomData<String>,
}

impl WithZst {
    fn access_data(&{mut data} mut self) {
        self.data.push(42);
    }

    fn access_zst(&{mut zst} mut self) {
        self.zst = ();
    }
}

// =============================================================================
// Edge Case 6: repr(C) struct
// =============================================================================

#[repr(C)]
struct ReprC {
    x: i32,
    y: i32,
}

impl ReprC {
    fn access_x(&{mut x} mut self) {
        self.x = 10;
    }

    fn disjoint_reprc(&mut self) {
        let _y = &self.y;
        self.access_x(); // Should work even with repr(C)
    }
}

// =============================================================================
// Edge Case 7: Struct with references
// =============================================================================

struct ContainsRefs<'a> {
    reference: &'a i32,
    value: i32,
}

impl<'a> ContainsRefs<'a> {
    fn update_value(&{mut value} mut self) {
        self.value = 100;
    }

    fn access_both(&mut self) {
        let _r = self.reference;
        self.update_value(); // Works
    }
}

// =============================================================================
// Edge Case 8: Mutable and immutable view types
// =============================================================================

struct MixedAccess {
    read_only: i32,
    write_only: i32,
}

impl MixedAccess {
    fn read(&{read_only} self) -> i32 {
        self.read_only
    }

    fn write(&{mut write_only} mut self) {
        self.write_only = 10;
    }

    fn mixed_calls(&mut self) {
        let _r = self.read(); // Immutable borrow of read_only
        self.write();         // Mutable borrow of write_only - should work!
    }
}

// =============================================================================
// Edge Case 9: View types with const generics
// =============================================================================

struct WithConst<const N: usize> {
    array: [i32; N],
    counter: usize,
}

impl<const N: usize> WithConst<N> {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn use_array(&mut self) {
        let _arr = &self.array;
        self.increment(); // Works
    }
}

// =============================================================================
// Edge Case 10: Nested view-typed calls (same struct)
// =============================================================================

struct Nested {
    a: i32,
    b: i32,
    c: i32,
}

impl Nested {
    fn inc_a(&{mut a} mut self) {
        self.a += 1;
    }

    fn inc_b(&{mut b} mut self) {
        self.b += 1;
    }

    fn caller_ab(&mut self) {
        self.inc_a();
        self.inc_b();
        self.inc_a(); // Can call again
        self.inc_b(); // Multiple calls work
    }
}

// =============================================================================
// Edge Case 11: View types with Option and Result
// =============================================================================

struct WithOptions {
    maybe: Option<i32>,
    result: Result<String, String>,
    value: i32,
}

impl WithOptions {
    fn update_value(&{mut value} mut self) {
        self.value = 42;
    }

    fn access_options(&mut self) {
        let _m = &self.maybe;
        let _r = &self.result;
        self.update_value(); // Works - value disjoint from maybe and result
    }
}

// =============================================================================
// Edge Case 12: Empty struct (no fields)
// =============================================================================

struct Empty {}

// View types on empty struct don't make sense, but should parse
// (though there are no fields to specify)
// Actually, this should probably error, but test what happens
// fn view_on_empty(x: &{} Empty) {} // Would be empty view spec error

// =============================================================================
// Edge Case 13: Struct with only PhantomData
// =============================================================================

struct OnlyPhantom<T> {
    _marker: std::marker::PhantomData<T>,
}

// Can't create meaningful view types since PhantomData is ZST
// fn phantom_view(x: &{mut _marker} OnlyPhantom<i32>) {}

// =============================================================================
// Edge Case 14: Associated functions (not methods)
// =============================================================================

struct S14 {
    field: i32,
}

impl S14 {
    // Associated function with view-typed parameter
    fn associated(s: &{mut field} mut S14) {
        s.field = 10;
    }
}

fn test_associated() {
    let mut s = S14 { field: 0 };
    S14::associated(&mut s); // UFCS call
}

// =============================================================================
// Edge Case 15: Multiple borrows of different fields
// =============================================================================

struct S15 {
    a: i32,
    b: i32,
    c: i32,
}

fn multiple_disjoint_borrows(s: &mut S15) {
    let _a = &mut s.a;
    let _b = &mut s.b;
    let _c = &mut s.c;
    // All three can coexist - this already works in Rust
    // View types make it work through function calls too
}

// =============================================================================
// Edge Case 16: View types with immutable references
// =============================================================================

struct S16 {
    data: Vec<i32>,
    metadata: String,
}

impl S16 {
    fn read_metadata(&{metadata} self) -> String {
        self.metadata.clone()
    }

    fn iter_with_read(&self) {
        for _item in &self.data {
            let _m = self.read_metadata(); // Immutable view - should work
        }
    }
}

fn main() {
    // All edge cases compile successfully
    let mut s1 = SingleField { only: 0 };
    s1.access_only();

    let mut many = ManyFields {
        f0: 0, f1: 0, f2: 0, f3: 0, f4: 0,
        f5: 0, f6: 0, f7: 0, f8: 0, f9: 0,
        f10: String::new(),
    };
    many.disjoint_many();

    let mut gen = Generic { first: 1, second: "two", metadata: 0 };
    gen.with_borrows();

    let mut wl = WithLifetimes { first: "a", second: "b", counter: 0 };
    wl.use_refs();

    let mut rc = ReprC { x: 0, y: 0 };
    rc.disjoint_reprc();

    let value = 42;
    let mut cr = ContainsRefs { reference: &value, value: 0 };
    cr.access_both();

    let mut mix = MixedAccess { read_only: 1, write_only: 2 };
    mix.mixed_calls();

    let mut wc: WithConst<5> = WithConst { array: [0; 5], counter: 0 };
    wc.use_array();

    let mut nested = Nested { a: 0, b: 0, c: 0 };
    nested.caller_ab();

    let mut wo = WithOptions {
        maybe: Some(1),
        result: Ok(String::from("ok")),
        value: 0,
    };
    wo.access_options();

    test_associated();

    let s16 = S16 { data: vec![1, 2, 3], metadata: String::from("meta") };
    s16.iter_with_read();

    println!("All edge cases passed!");
}
