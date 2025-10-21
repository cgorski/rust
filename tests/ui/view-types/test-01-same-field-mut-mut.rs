#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 1: Theorem 3 - same_field_mut_conflicts
//
// THEOREM (formalization/Core_Proven.v):
// Theorem same_field_mut_conflicts : forall f,
//   fields_conflict (mkFieldAccess f Mut) (mkFieldAccess f Mut) = true.
//
// MEANING: Two mutable accesses to the same field always conflict
//
// PROOF TECHNIQUE: Simple - same field name, both mutable → conflict
//
// TEST STRATEGY:
// Create explicit mutable borrow of a field, then call view-typed method
// that also mutably accesses that field. Should error.

struct S {
    a: i32,
    b: i32,
}

impl S {
    // View spec: mutably accesses field 'a'
    fn use_a_mut(&{mut a} mut self) {
        self.a = 1;
    }
}

fn main() {
    let mut s = S { a: 0, b: 0 };

    // Explicitly borrow field 'a' mutably
    let a_ref = &mut s.a;

    // Try to call method that also mutably accesses 'a'
    // Theorem 3 guarantees this conflicts
    s.use_a_mut(); //~ ERROR cannot borrow

    // Keep the first borrow active
    *a_ref = 10;
}
