//@ edition:2021
#![feature(view_types)]
#![allow(incomplete_features)]

// NEGATIVE TEST: Overlapping Paths in View Specifications
//
// This test verifies that the compiler rejects view specifications where
// a parent path and child path are both specified, as this creates redundancy
// and ambiguity about access permissions.
//
// Examples that SHOULD error:
// - &{mut inner, mut inner.value} - parent and child
// - &{mut a.b, mut a.b.c} - parent and child at deeper level
// - &{mut field.x, mut field} - child then parent (order shouldn't matter)

// =============================================================================
// ERROR: Parent and child in same view spec
// =============================================================================

struct Inner {
    value: i32,
}

struct Outer {
    inner: Inner,
}

impl Outer {
    // ERROR: Specifying both 'inner' and 'inner.value'
    fn parent_and_child(&{mut inner, mut inner.value} self) {} //~ ERROR

    // ERROR: Specifying child then parent (order doesn't matter)
    fn child_and_parent(&{mut inner.value, mut inner} self) {} //~ ERROR

    // ERROR: Same path twice (basic duplicate)
    fn duplicate_simple(&{mut inner, inner} self) {} //~ ERROR
}

// =============================================================================
// ERROR: Multiple levels of nesting with overlap
// =============================================================================

struct Level3 {
    data: i32,
}

struct Level2 {
    level3: Level3,
}

struct Level1 {
    level2: Level2,
}

impl Level1 {
    // ERROR: level2 and level2.level3 overlap
    fn level2_and_level3(&{mut level2, mut level2.level3} self) {} //~ ERROR

    // ERROR: level2.level3 and level2.level3.data overlap
    fn level3_and_data(&{mut level2.level3, mut level2.level3.data} self) {} //~ ERROR

    // ERROR: level2 and level2.level3.data overlap (multiple levels)
    fn level2_and_data(&{mut level2, mut level2.level3.data} self) {} //~ ERROR

    // ERROR: Same nested path twice
    fn duplicate_nested(&{mut level2.level3, level2.level3} self) {} //~ ERROR
}

// =============================================================================
// ERROR: Overlapping with non-overlapping paths (should still error on overlap)
// =============================================================================

struct Multiple {
    field_a: Inner,
    field_b: Inner,
    field_c: i32,
}

impl Multiple {
    // ERROR: field_a and field_a.value overlap, even though field_b is also present
    fn mixed_overlap(&{mut field_a, mut field_b, mut field_a.value} self) {} //~ ERROR

    // OK: field_a.value and field_b.value don't overlap (different parents)
    fn no_overlap(&{mut field_a.value, mut field_b.value} self) {}
}

// =============================================================================
// ERROR: Three-way overlap
// =============================================================================

struct Deep {
    a: Level1,
    b: i32,
}

impl Deep {
    // ERROR: a, a.level2, and a.level2.level3 all overlap
    fn three_way(&{mut a, mut a.level2, mut a.level2.level3} self) {} //~ ERROR
    //~| ERROR
    //~| ERROR
}

// =============================================================================
// ERROR: Immutable and mutable overlap (still an error)
// =============================================================================

struct S {
    field: Inner,
}

impl S {
    // ERROR: Can't have both immutable parent and mutable child
    fn immut_parent_mut_child(&{field, mut field.value} self) {} //~ ERROR

    // ERROR: Can't have both mutable parent and immutable child
    fn mut_parent_immut_child(&{mut field, field.value} self) {} //~ ERROR
}

fn main() {}
