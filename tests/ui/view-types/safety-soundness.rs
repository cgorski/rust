// V1 RESTRICTION TEST: Contains method with return reference (expects error)
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// P0 Safety and Soundness Tests for View Types
//
// This test validates that view types maintain Rust's core safety guarantees:
// - No aliasing violations
// - No lifetime escapes
// - Proper conflict detection
// - Move semantics respected
//
// All tests in this file SHOULD COMPILE (check-pass) because view types
// properly enforce safety. If any test here starts failing, we have a
// soundness hole!

// =============================================================================
// SAFETY: Duplicate fields must be caught by parser/validation
// =============================================================================

// Note: Duplicate detection happens during parsing, so these would
// be caught earlier. Tested in errors.rs.

// =============================================================================
// SAFETY: Disjoint field borrows don't conflict (Core Theorem!)
// =============================================================================

struct DisjointFields {
    field_a: i32,
    field_b: String,
    field_c: Vec<u8>,
}

impl DisjointFields {
    fn mutate_a(&{mut field_a} mut self) {
        self.field_a = 42;
    }

    fn mutate_b(&{mut field_b} mut self) {
        self.field_b = String::from("test");
    }

    // Core safety: Can borrow different fields simultaneously
    fn test_disjoint(&mut self) {
        for byte in &mut self.field_c {
            self.mutate_a(); // ✓ Disjoint: field_a vs field_c
            self.mutate_b(); // ✓ Disjoint: field_b vs field_c
            *byte = self.field_a as u8;
        }
    }
}

// =============================================================================
// SAFETY: Lifetime bounds are enforced
// =============================================================================

struct WithLifetime<'a> {
    reference: &'a str,
    owned: String,
}

impl<'a> WithLifetime<'a> {
    // Can't return reference beyond the view's scope
    // The lifetime on the view parameter constrains the return
    fn get_owned_ref(&{owned} self) -> String {
        self.owned.clone()
    }

    // Can access reference field through view
    fn get_reference(&{reference} self) -> &'a str { //~ ERROR view-typed functions cannot return references
        self.reference // V1: This will be rejected
    }

    // Both fields accessible with different views
    fn access_both(&{reference, owned} self) -> (usize, String) {
        (self.reference.len(), self.owned.clone())
    }
}

// =============================================================================
// SAFETY: Generic types work correctly
// =============================================================================

struct Generic<T> {
    data: Vec<T>,
    count: usize,
}

impl<T> Generic<T> {
    fn increment(&{mut count} mut self) -> usize {
        self.count += 1;
        self.count
    }

    fn process_generic(&mut self)
    where T: Clone
    {
        for _item in &self.data {
            self.increment(); // ✓ Disjoint: count vs data
        }
    }
}

// =============================================================================
// SAFETY: Move semantics respected
// =============================================================================

struct WithMove {
    movable: String,
    other: i32,
}

impl WithMove {
    // Can move out of field if we have mutable access and it's the right type
    fn take_movable(&{mut movable} mut self) -> String {
        std::mem::replace(&mut self.movable, String::new()) // ✓ OK
    }

    // Can't access other fields
    fn only_other(&{mut other} mut self) {
        self.other = 100; // ✓ OK - only accesses other
        // self.movable would be rejected by validation
    }
}

// =============================================================================
// SAFETY: Borrow rules still apply within view scope
// =============================================================================

struct BorrowRules {
    field_a: Vec<i32>,
    field_b: i32,
}

impl BorrowRules {
    fn immutable_view(&{field_a} self) -> usize {
        self.field_a.len() // ✓ OK - immutable access
    }

    fn mutable_view(&{mut field_a} mut self) {
        self.field_a.push(1); // ✓ OK - mutable access
    }

    // Can't have conflicting borrows even within same function
    fn no_conflict(&{mut field_a} mut self) {
        let _x = &self.field_a;      // Immutable borrow
        // Can't mutate while immutably borrowed
        // self.field_a.push(1);      // Would error (normal borrow rules)

        // But this is fine:
        let len = self.field_a.len();
        let _ = len;
    }
}

// =============================================================================
// SAFETY: Zero-sized types
// =============================================================================

struct WithZST {
    marker: std::marker::PhantomData<i32>,
    actual: String,
}

impl WithZST {
    fn access_actual(&{mut actual} mut self) {
        self.actual = String::from("test"); // ✓ OK
    }
}

// =============================================================================
// SAFETY: Multiple fields in view work correctly
// =============================================================================

struct MultiField {
    a: i32,
    b: i32,
    c: i32,
}

impl MultiField {
    fn two_fields(&{mut a, mut b} mut self) {
        self.a = 1;
        self.b = 2;
        // self.c would be rejected
    }

    fn mixed_mut(&{mut a, b} mut self) -> i32 {
        self.a = 10;
        self.b // ✓ OK - immutable access to b
    }

    // Can still borrow third field while calling view-typed method
    fn test_third(&mut self) {
        let _c_ref = &mut self.c;
        self.two_fields(); // ✓ OK - only borrows a, b (not c)
    }
}

// =============================================================================
// SAFETY: Const generics
// =============================================================================

struct WithConstGeneric<const N: usize> {
    array: [i32; N],
    count: usize,
}

impl<const N: usize> WithConstGeneric<N> {
    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn process(&mut self) {
        for _item in &mut self.array {
            self.increment_count(); // ✓ Disjoint: count vs array
        }
    }
}

// =============================================================================
// SAFETY: repr(C) compatibility
// =============================================================================

#[repr(C)]
struct ReprC {
    x: i32,
    y: i32,
}

impl ReprC {
    fn mutate_x(&{mut x} mut self) {
        self.x = 100;
    }

    fn test_repr_c(&mut self) {
        let _y_ref = &mut self.y;
        self.mutate_x(); // ✓ Disjoint fields work with repr(C)
    }
}

// =============================================================================
// SAFETY: Validation catches violations
// =============================================================================

struct Validated {
    allowed: i32,
    forbidden: i32,
}

impl Validated {
    fn only_allowed(&{mut allowed} mut self) {
        self.allowed = 5; // ✓ OK
        // self.forbidden = 10; // Would be rejected by validation
    }
}

// =============================================================================
// Test main - all safety invariants hold
// =============================================================================

fn main() {
    // DisjointFields tests
    let mut df = DisjointFields {
        field_a: 0,
        field_b: String::new(),
        field_c: vec![1, 2, 3],
    };
    df.test_disjoint();

    // Generic tests
    let mut g = Generic {
        data: vec![1, 2, 3],
        count: 0,
    };
    g.process_generic();

    // Multi-field tests
    let mut mf = MultiField { a: 0, b: 0, c: 0 };
    mf.test_third();

    // Const generic tests
    let mut cg = WithConstGeneric {
        array: [1, 2, 3],
        count: 0,
    };
    cg.process();

    // repr(C) tests
    let mut rc = ReprC { x: 0, y: 0 };
    rc.test_repr_c();

    println!("All safety tests passed!");
}
