#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 4: Theorem 7 - different_fields_no_conflict
//
// THEOREM (formalization/Core_Proven.v):
// Theorem different_fields_no_conflict : forall f1 f2 m1 m2,
//   f1 <> f2 ->
//   fields_conflict (mkFieldAccess f1 m1) (mkFieldAccess f2 m2) = false.
//
// MEANING: If field names are different, they never conflict,
//          regardless of mutability combinations!
//
// This is THE KEY THEOREM that enables view types!
// It proves that disjoint fields can be borrowed simultaneously.
//
// PROOF TECHNIQUE: If f1 ≠ f2, then fields_conflict returns false
//
// TEST STRATEGY:
// 1. Borrow field 'a' mutably
// 2. Call view-typed method that accesses field 'b' mutably
// 3. Should work because a ≠ b (proven safe!)

//@ check-pass

struct S {
    a: i32,
    b: i32,
    c: i32,
}

impl S {
    // View spec: mutably accesses field 'b'
    fn use_b(&{mut b} mut self) {
        self.b = 100;
    }

    // View spec: mutably accesses field 'c'
    fn use_c(&{mut c} mut self) {
        self.c = 200;
    }
}

fn main() {
    let mut s = S { a: 0, b: 0, c: 0 };

    // Explicitly borrow field 'a' mutably
    let a_ref = &mut s.a;

    // Call method that mutably accesses field 'b' (different field!)
    // Theorem 7: a ≠ b, so no conflict regardless of mutability
    s.use_b(); // OK: different fields!

    // Can even call another view-typed method accessing field 'c'
    s.use_c(); // Also OK: a ≠ c and b ≠ c!

    // All three can coexist:
    // - a_ref: mutable borrow of 'a'
    // - use_b temporarily borrows 'b'
    // - use_c temporarily borrows 'c'
    *a_ref = 42;

    println!("Success! Different fields don't conflict!");
    println!("This is the core property that makes view types useful!");
}
