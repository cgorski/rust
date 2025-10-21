//@ edition:2021
#![feature(view_types)]
#![allow(incomplete_features)]

// NEGATIVE TEST: Basic View Type Syntax Errors
//
// This test covers fundamental syntax errors in view type specifications:
// - Keywords used as field names
// - Empty view specifications
// - Numeric field identifiers (tuple syntax not supported)

// =============================================================================
// ERROR: Keywords cannot be used as field names
// =============================================================================

struct S1 {
    field: i32,
}

impl S1 {
    fn keyword_self(&{mut self} self) {} //~ ERROR expected identifier, found keyword `self`

    fn keyword_super(&{mut super} self) {} //~ ERROR expected identifier, found keyword `super`
}

// =============================================================================
// ERROR: Empty view specification is not allowed
// =============================================================================

struct S2 {
    field: i32,
}

impl S2 {
    fn empty_view(&{} self) {} //~ ERROR expected field name or tuple index
}

// =============================================================================
// NOTE: Tuple fields now supported - this parses successfully
// Tuple struct wrapper used to test tuple field syntax
// =============================================================================

struct TupleWrapper(i32, String);

impl TupleWrapper {
    fn tuple_field(&{mut 0} self) {} // Parses now (tuple fields supported)
}

// =============================================================================
// ERROR: View types require reference types
// =============================================================================

struct S3 {
    field: i32,
}

impl S3 {
    fn owned_value({mut field} self) {} //~ ERROR expected parameter name, found `{`
}

fn main() {}
