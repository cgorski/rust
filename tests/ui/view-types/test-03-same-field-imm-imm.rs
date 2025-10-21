#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 3: Theorem 6 - same_field_imm_no_conflict
//
// THEOREM (formalization/Core_Proven.v):
// Theorem same_field_imm_no_conflict : forall f,
//   fields_conflict (mkFieldAccess f Imm) (mkFieldAccess f Imm) = false.
//
// MEANING: Two immutable accesses to the same field do NOT conflict
//          Multiple readers are allowed!
//
// PROOF TECHNIQUE: Same field name, both immutable → no conflict
//
// TEST STRATEGY:
// Create immutable borrow of a field, then call view-typed method that
// also immutably accesses that field. Should compile successfully.

//@ check-pass

struct S {
    a: i32,
    b: i32,
}

impl S {
    // View spec: immutably accesses field 'a'
    fn read_a(&{a} self) -> i32 {
        self.a
    }

    // Another immutable accessor
    fn also_read_a(&{a} self) -> i32 {
        self.a + 1
    }
}

fn main() {
    let s = S { a: 42, b: 100 };

    // Explicitly borrow field 'a' immutably
    let a_ref = &s.a;

    // Call method that also immutably accesses 'a'
    // Theorem 6 guarantees this does NOT conflict (immutable sharing is safe)
    let value1 = s.read_a(); // OK: immutable + immutable = no conflict!

    // Can even call ANOTHER immutable view-typed method
    let value2 = s.also_read_a(); // Also OK!

    // All three can coexist
    println!("a_ref: {}, value1: {}, value2: {}", a_ref, value1, value2);

    // Multiple readers are safe - this is a core property of Rust's borrow system
    // View types preserve this property!
}
