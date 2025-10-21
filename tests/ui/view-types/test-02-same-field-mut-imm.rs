#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 2: Theorem 4 - same_field_mut_imm_conflicts
//
// THEOREM (formalization/Core_Proven.v):
// Theorem same_field_mut_imm_conflicts : forall f,
//   fields_conflict (mkFieldAccess f Mut) (mkFieldAccess f Imm) = true.
//
// MEANING: A mutable access to a field conflicts with an immutable access
//          to the same field
//
// PROOF TECHNIQUE: Same field name, one mutable → always conflict
//
// TEST STRATEGY:
// Create mutable borrow of a field, then call view-typed method that
// immutably accesses that field. Should error (cannot have mutable and
// immutable borrow of same data simultaneously).

struct S {
    a: i32,
    b: i32,
}

impl S {
    // View spec: immutably accesses field 'a'
    fn read_a(&{a} self) -> i32 {
        self.a
    }
}

fn main() {
    let mut s = S { a: 0, b: 0 };

    // Explicitly borrow field 'a' mutably
    let a_ref = &mut s.a;

    // Try to call method that immutably accesses 'a'
    // Theorem 4 guarantees this conflicts (mut + imm on same field)
    s.read_a(); //~ ERROR cannot borrow

    // Keep the first borrow active
    *a_ref = 10;
}
