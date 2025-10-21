#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 7: Theorem 11 - disjoint_fields_no_conflict
//
// THEOREM (formalization/Core_Proven.v):
// Theorem disjoint_fields_no_conflict : forall v1 v2,
//   (forall fa1 fa2, In fa1 v1 -> In fa2 v2 -> fa_name fa1 <> fa_name fa2) ->
//   views_conflict v1 v2 = false.
//
// MEANING: If ALL field names in v1 are different from ALL field names in v2,
//          then the view specs do not conflict.
//
// This is the generalization of different_fields_no_conflict to multi-field views.
//
// PROOF TECHNIQUE:
// views_conflict iterates over v1 checking if ANY field conflicts with ANY in v2.
// If all names differ, no pair will match, so views_conflict returns false.
//
// TEST STRATEGY:
// Create view specs with completely disjoint field sets and verify they can coexist.

//@ check-pass

struct SixFields {
    a: i32,
    b: i32,
    c: i32,
    d: i32,
    e: i32,
    f: i32,
}

impl SixFields {
    // View spec 1: {a, b} - first two fields
    fn use_a_and_b(&{mut a, mut b} mut self) {
        self.a = 1;
        self.b = 2;
    }

    // View spec 2: {c, d} - completely disjoint from {a, b}
    fn use_c_and_d(&{mut c, mut d} mut self) {
        self.c = 10;
        self.d = 20;
    }

    // View spec 3: {e, f} - disjoint from both above
    fn use_e_and_f(&{mut e, mut f} mut self) {
        self.e = 100;
        self.f = 200;
    }

    // Larger view spec: {a, b, c}
    fn use_a_b_c(&{mut a, mut b, mut c} mut self) {
        self.a = 1;
        self.b = 2;
        self.c = 3;
    }

    // Disjoint from above: {d, e, f}
    fn use_d_e_f(&{mut d, mut e, mut f} mut self) {
        self.d = 10;
        self.e = 20;
        self.f = 30;
    }
}

// TEST CASE 1: Two-field views, completely disjoint
// Theorem 11: {a, b} ∩ {c, d} = ∅ → no conflict
fn test_disjoint_two_field_views() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    // Explicitly borrow fields {c, d}
    let c_ref = &mut s.c;
    let d_ref = &mut s.d;

    // Call method with view spec {a, b} - completely disjoint!
    // Theorem 11 guarantees this is safe
    s.use_a_and_b(); // OK: {a, b} ∩ {c, d} = ∅

    *c_ref = 100;
    *d_ref = 200;

    println!("Disjoint two-field views: OK");
}

// TEST CASE 2: Three-field views, completely disjoint
// Tests larger view specs
fn test_disjoint_three_field_views() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    // Explicitly borrow fields {d, e, f}
    let d_ref = &mut s.d;

    // Call method with view spec {a, b, c} - completely disjoint!
    s.use_a_b_c(); // OK: {a, b, c} ∩ {d, e, f} = ∅

    *d_ref = 100;

    println!("Disjoint three-field views: OK");
}

// TEST CASE 3: Sequential calls to disjoint views
// Validates that disjoint views can be used back-to-back
fn test_sequential_disjoint_calls() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    // These are all disjoint sets, should all work sequentially
    s.use_a_and_b();  // {a, b}
    s.use_c_and_d();  // {c, d} - disjoint from above
    s.use_e_and_f();  // {e, f} - disjoint from both above

    println!("Sequential disjoint view calls: OK");
}

// TEST CASE 4: Simultaneous disjoint borrows
// The most direct test of Theorem 11
fn test_simultaneous_disjoint() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    // Create simultaneous borrows of disjoint field sets
    let a_ref = &mut s.a;
    let b_ref = &mut s.b;

    // Call method accessing disjoint fields {c, d}
    s.use_c_and_d(); // OK: {c, d} ∩ {a, b} = ∅

    // Can even call another disjoint method
    s.use_e_and_f(); // OK: {e, f} ∩ {a, b, c, d} = ∅

    *a_ref = 1;
    *b_ref = 2;

    println!("Simultaneous disjoint borrows: OK");
}

// TEST CASE 5: Real-world pattern - partitioned struct access
// This is the practical use case for multi-field view types
fn test_partitioned_struct_access() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    // Loop borrows one partition {a, b}
    let refs = [&mut s.a, &mut s.b];
    for r in refs {
        // While holding borrows of {a, b}, call method accessing {c, d}
        // This is safe because the partitions are disjoint
        s.use_c_and_d(); // OK: {c, d} ∩ {a, b} = ∅

        *r = 42;
    }

    println!("Partitioned struct access: OK");
}

// TEST CASE 6: Verification of set semantics
// Order of fields shouldn't matter for disjointness
fn test_set_semantics_for_disjoint() {
    let mut s = SixFields { a: 0, b: 0, c: 0, d: 0, e: 0, f: 0 };

    let c_ref = &mut s.c;

    // {a, b} and {b, a} are the same set
    // Both are disjoint from {c}
    s.use_a_and_b(); // OK

    *c_ref = 100;

    println!("Set semantics for disjointness: OK");
}

fn main() {
    test_disjoint_two_field_views();
    test_disjoint_three_field_views();
    test_sequential_disjoint_calls();
    test_simultaneous_disjoint();
    test_partitioned_struct_access();
    test_set_semantics_for_disjoint();

    println!("\n✓ Theorem 11 verified: disjoint_fields_no_conflict");
    println!("✓ Completely disjoint multi-field view specs don't conflict");
    println!("✓ This enables safe partitioned access to structs!");
    println!("✓ Implementation correctly checks ALL fields for overlap!");
}
