//@ edition:2021
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Multi-Field View Specs - V1 Restrictions
//
// This test validates TWO V1 restrictions on multi-field view specs:
//
// 1. RETURN REFERENCES BLOCKED:
//    View-typed methods cannot return references in V1 (conservative restriction).
//    This prevents potential soundness issues with field borrow lifetime tracking.
//    See formalization/Lifetimes_Returns.v for the formal analysis.
//
// 2. ALL FIELDS CHECKED:
//    When a multi-field view spec like &{mut x, mut y} is used, ALL fields
//    are checked for conflicts (not just the first one). This validates the
//    fix for a previous soundness bug where only the first field was checked.
//
// EXPECTED BEHAVIOR: All marked lines should produce compilation errors.

// =============================================================================
// Test 1: Return References Not Allowed (V1 Restriction)
// =============================================================================

struct ThreeFields {
    x: i32,
    y: i32,
    z: i32,
}

impl ThreeFields {
    // View spec with two fields, attempting to return reference
    fn use_x_and_y(&{mut x, mut y} mut self) -> &mut i32 { //~ ERROR view-typed functions cannot return references
        self.x = 1;
        self.y = 2;
        &mut self.y
    }

    // Another multi-field view spec with return reference
    fn use_z_and_y(&{mut z, mut y} mut self) -> &mut i32 { //~ ERROR view-typed functions cannot return references
        self.z = 3;
        self.y = 4;
        &mut self.y
    }

    // V1 RATIONALE:
    // If these were allowed, calling them sequentially MIGHT seem safe
    // (different first fields), but both return references to field 'y',
    // creating potential aliasing. V1 conservatively blocks ALL return refs.
}

// =============================================================================
// Test 2: All Fields in View Spec Are Checked (Bug Fix Validation)
// =============================================================================

struct Config {
    setting_a: bool,
    setting_b: bool,
    setting_c: bool,
}

impl Config {
    // View spec: first field = setting_a, second field = setting_b
    fn modify_a_and_b(&{mut setting_a, mut setting_b} mut self) {
        self.setting_a = true;
        self.setting_b = false;
    }

    fn modify_b_and_c(&{mut setting_b, mut setting_c} mut self) {
        self.setting_b = true;
        self.setting_c = false;
    }

    // CRITICAL TEST: Validates ALL fields are checked
    fn test_second_field_conflict(&mut self) {
        // Explicitly borrow field setting_b
        let b_ref = &mut self.setting_b;

        // Call method where setting_b is the SECOND field in view spec
        // OLD BUG: Only first field (setting_a) was checked, missed conflict on setting_b
        // FIXED: ALL fields checked, detects setting_b is already borrowed
        self.modify_a_and_b(); //~ ERROR cannot borrow `self.setting_b` as mutable more than once at a time

        *b_ref = true;
    }
}

// =============================================================================
// Test 3: Combined Test - Field Conflict + Return References
// =============================================================================

struct State {
    counter: i32,
    cache: i32,
    data: Vec<i32>,
}

impl State {
    fn update_counter_and_cache(&{mut counter, mut cache} mut self) {
        self.counter += 1;
        self.cache = self.counter * 2;
    }

    fn update_cache_and_data(&{mut cache, mut data} mut self) {
        self.cache = 999;
        self.data.push(self.cache);
    }

    // Test that field conflicts are detected in complex scenarios
    fn test_overlapping_calls(&mut self) {
        // Borrow cache explicitly
        let _cache_ref = &self.cache;

        // Try to call method that accesses cache (second field in its view spec)
        // Should error: cache already borrowed
        self.update_cache_and_data(); //~ ERROR cannot borrow `self.cache` as mutable because it is also borrowed as immutable

        // Use the reference
        println!("Cache: {}", _cache_ref);
    }
}

// =============================================================================
// Test 4: Return References with Overlapping Fields
// =============================================================================

struct Complex {
    field_x: i32,
    field_y: i32,
    field_z: i32,
}

impl Complex {
    // These methods would create aliasing if returns were allowed
    fn accessor_xy(&{mut field_x, mut field_y} mut self) -> &mut i32 { //~ ERROR view-typed functions cannot return references
        self.field_x += 1;
        &mut self.field_y
    }

    fn accessor_yz(&{mut field_y, mut field_z} mut self) -> &mut i32 { //~ ERROR view-typed functions cannot return references
        self.field_z += 1;
        &mut self.field_y
    }

    // SOUNDNESS ISSUE (if returns were allowed):
    // Both methods return mutable reference to field_y.
    // Sequential calls would create aliasing:
    //   let r1 = self.accessor_xy();
    //   let r2 = self.accessor_yz();
    //   *r1 = 100; // Both r1 and r2 point to field_y!
    //   *r2 = 200; // UNSOUND!
    //
    // V1 prevents this by blocking ALL return references.
}

fn main() {
    // These tests validate that the compiler correctly rejects invalid patterns
    println!("This test validates V1 restrictions on multi-field view specs:");
    println!("1. Return references are blocked (conservative restriction)");
    println!("2. ALL fields in view specs are checked for conflicts (bug fix validation)");
}
