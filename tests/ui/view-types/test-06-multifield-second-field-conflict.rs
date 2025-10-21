#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST 6: Multi-field overlap on SECOND field (THE BUG FIX TEST)
//
// SOUNDNESS BUG THIS TESTS:
// Original implementation only checked the FIRST field from multi-field view specs.
// This test validates that ALL fields are now checked, not just the first.
//
// BUG SCENARIO:
// - View spec 1: {mut x, mut y} - first field is 'x', second is 'y'
// - View spec 2: {mut z, mut y} - first field is 'z', second is 'y'
// - OLD BUG: Only compared first fields (x vs z) → no conflict detected!
// - REALITY: Both access second field 'y' → SHOULD conflict!
//
// THEOREM (formalization/Core_Proven.v):
// Theorem disjoint_fields_no_conflict : forall v1 v2,
//   (forall fa1 fa2, In fa1 v1 -> In fa2 v2 -> fa_name fa1 <> fa_name fa2) ->
//   views_conflict v1 v2 = false.
//
// CONTRAPOSITIVE: If ANY field name matches, views_conflict = true
//
// PROOF VERIFICATION:
// views_conflict checks ALL pairs of fields, not just first fields.
// Our implementation must do the same.

struct ThreeFields {
    x: i32,
    y: i32,
    z: i32,
}

impl ThreeFields {
    // View spec: {mut x, mut y} - x is first, y is second
    fn use_x_and_y(&{mut x, mut y} mut self) {
        self.x = 1;
        self.y = 2;
    }

    // View spec: {mut z, mut y} - z is first, y is second
    // CRITICAL: First field 'z' differs from above's 'x'
    //           BUT second field 'y' is THE SAME!
    //           This MUST be detected as a conflict!
    fn use_z_and_y(&{mut z, mut y} mut self) {
        self.z = 3;
        self.y = 4; // This conflicts with use_x_and_y's access to y!
    }
}

// TEST CASE 1: Explicit borrow of second field, call method that accesses it
// This creates the actual conflict scenario
fn test_explicit_second_field_conflict() {
    let mut s = ThreeFields { x: 0, y: 0, z: 0 };

    // Explicitly borrow the SECOND field 'y' mutably
    let y_ref = &mut s.y;

    // Try to call use_z_and_y which has view spec {mut z, mut y}
    // OLD BUG: Only checked first field 'z', didn't see conflict with 'y'
    // FIXED: All fields checked, 'y' conflict detected!
    s.use_z_and_y(); //~ ERROR cannot borrow `s.y` as mutable more than once at a time

    *y_ref = 100;
}

// TEST CASE 2: Verify first field is DIFFERENT (no false positive)
// This ensures we're not just detecting all multi-field overlaps
fn test_first_fields_different_is_ok_if_second_disjoint() {
    let mut s = ThreeFields { x: 0, y: 0, z: 0 };

    // Borrow 'x' explicitly
    let x_ref = &mut s.x;

    // Call use_z_and_y: {mut z, mut y}
    // First field 'z' differs from 'x' ✓
    // Second field 'y' differs from 'x' ✓
    // No conflict!
    s.use_z_and_y(); // OK: {z, y} disjoint from {x}

    *x_ref = 100;

    println!("Different first fields with disjoint seconds: OK");
}

// TEST CASE 3: Three fields - conflict on THIRD field
// Validates that position doesn't matter (third field checked too)
struct FiveFields {
    a: i32,
    b: i32,
    c: i32,
    d: i32,
    e: i32,
}

impl FiveFields {
    fn use_abc(&{mut a, mut b, mut c} mut self) {
        self.a = 1;
        self.b = 2;
        self.c = 3;
    }

    // First two fields differ, but THIRD field matches
    fn use_dec(&{mut d, mut e, mut c} mut self) {
        self.d = 10;
        self.e = 20;
        self.c = 30; // Conflicts with use_abc on field 'c'!
    }
}

fn test_third_field_conflict() {
    let mut s = FiveFields { a: 0, b: 0, c: 0, d: 0, e: 0 };

    // Explicitly borrow the THIRD field 'c'
    let c_ref = &mut s.c;

    // Call use_dec which has view spec {mut d, mut e, mut c}
    // First field 'd' - no conflict with 'c'
    // Second field 'e' - no conflict with 'c'
    // Third field 'c' - CONFLICT!
    s.use_dec(); //~ ERROR cannot borrow `s.c` as mutable more than once at a time

    *c_ref = 100;
}

// TEST CASE 4: All permutations of two fields
// Mathematically verify order independence
fn test_two_field_permutations() {
    let mut s = ThreeFields { x: 0, y: 0, z: 0 };

    // Borrow 'y'
    let y_ref = &mut s.y;

    // Both {x, y} and {y, x} should conflict with this borrow
    // We can only test one without erroring, but conceptually both equivalent

    // use_x_and_y has {mut x, mut y} - 'y' is SECOND
    // Should conflict regardless of position
    s.use_x_and_y(); //~ ERROR cannot borrow

    *y_ref = 100;
}

// TEST CASE 5: Four-field overlap on FOURTH field (extreme case)
impl FiveFields {
    fn use_abcd(&{mut a, mut b, mut c, mut d} mut self) {
        self.a = 1;
        self.b = 2;
        self.c = 3;
        self.d = 4;
    }
}

fn test_fourth_field_position() {
    let mut s = FiveFields { a: 0, b: 0, c: 0, d: 0, e: 0 };

    // Borrow the FOURTH field
    let d_ref = &mut s.d;

    // Call method with view spec {a, b, c, d} where 'd' is fourth
    // OLD BUG: If only first field checked, this passes
    // FIXED: Fourth field is checked!
    s.use_abcd(); //~ ERROR cannot borrow `s.d` as mutable more than once at a time

    *d_ref = 100;
}

fn main() {
    // These tests verify that field POSITION in view spec doesn't matter
    // Conflicts are detected regardless of where overlapping fields appear

    test_first_fields_different_is_ok_if_second_disjoint();
    test_two_field_permutations();
    test_third_field_conflict();
    test_fourth_field_position();
    test_explicit_second_field_conflict();

    println!("\n✓ CRITICAL: Second field conflicts detected!");
    println!("✓ Third field conflicts detected!");
    println!("✓ Fourth field conflicts detected!");
    println!("✓ Field position does not affect conflict detection!");
    println!("✓ SOUNDNESS BUG IS FIXED!");
}
