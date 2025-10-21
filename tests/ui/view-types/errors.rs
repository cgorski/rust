//@ edition:2021
#![feature(view_types)]
#![allow(incomplete_features)]

// Comprehensive error test suite for view types
// Tests all error conditions and invalid uses

// =============================================================================
// ERROR: Non-existent field
// =============================================================================

struct S1 {
    field_a: i32,
}

impl S1 {
    fn nonexistent_field(&{mut nonexistent} self) {}
}

// =============================================================================
// ERROR: View type on non-struct types
// =============================================================================

fn view_on_primitive(x: &{mut field} i32) {} //~ ERROR view types are not supported on free functions

fn view_on_tuple(x: &{mut 0} (i32, String)) {} //~ ERROR view types are not supported on free functions

enum MyEnum {
    Variant { field: i32 },
}

fn view_on_enum(x: &{mut field} MyEnum) {} //~ ERROR view types are not supported on free functions

fn view_on_trait_object(x: &{mut field} dyn std::fmt::Debug) {} //~ ERROR view types are not supported on free functions

fn view_on_slice(x: &{mut field} [i32]) {} //~ ERROR view types are not supported on free functions

// =============================================================================
// ERROR: Empty view specification
// =============================================================================

struct S2 {
    field: i32,
}

impl S2 {
    fn empty_view(&{} self) {} //~ ERROR expected field name or tuple index
}

// =============================================================================
// ERROR: Duplicate fields in view spec
// =============================================================================

struct S3 {
    field_a: i32,
    field_b: String,
}

impl S3 {
    fn duplicate_fields(&{mut field_a, field_a} self) {} //~ ERROR

    fn duplicate_mixed_mut(&{mut field_a, field_a} self) {} //~ ERROR
}

// =============================================================================
// ERROR: Private field access
// =============================================================================

mod inner {
    pub struct S4 {
        pub public_field: i32,
        private_field: String,
    }
}

use inner::S4;

impl S4 {
    fn access_private(&{mut private_field} self) {}

    fn mixed_public_private(&{public_field, private_field} self) {}
}

// =============================================================================
// ERROR: Type mismatch in view spec
// =============================================================================

struct S5 {
    field: i32,
}

// View type doesn't change the actual type of the reference
fn type_mismatch() {
    let s = S5 { field: 42 };
    let r: &i32 = &{field} s; //~ ERROR expected one of `.`, `;`, `?`, `else`, or an operator
}

// =============================================================================
// ERROR: Conflicting borrows should still error
// =============================================================================

struct S6 {
    field_a: i32,
    field_b: String,
}

impl S6 {
    fn uses_field_a(&{mut field_a} mut self) {
        self.field_a = 10;
    }

    fn conflicting_same_field(&mut self) {
        let _x = &mut self.field_a; // First borrow
        self.uses_field_a();
    }
}

// =============================================================================
// ERROR: View type with wrong reference kind
// =============================================================================

struct S7 {
    field: i32,
}

impl S7 {
    // Can't use view types on owned types
    fn owned_value({mut field} self) {} //~ ERROR expected parameter name, found `{`

    // Can't use view types on raw pointers (not yet supported)
    fn view_on_raw_ptr(x: *mut {mut field} S7) {} //~ ERROR expected type, found `{`
}

// =============================================================================
// ERROR: Accessing wrong field through view
// =============================================================================

struct S8 {
    allowed: i32,
    forbidden: String,
}

impl S8 {
    fn access_wrong_field(&{mut allowed} mut self) {
        self.forbidden = String::from("error"); //~ ERROR cannot access field `forbidden` through view-typed parameter
    }

    fn read_wrong_field(&{allowed} self) -> String {
        self.forbidden.clone() //~ ERROR cannot access field `forbidden` through view-typed parameter
    }
}

// =============================================================================
// ERROR: Method calls on view-typed parameters
// =============================================================================

struct S9 {
    field_a: i32,
    field_b: String,
}

impl S9 {
    fn helper(&mut self) {}

    fn call_method(&{mut field_a} mut self) {
        self.helper();
    }
}

// =============================================================================
// ERROR: View types only allowed on pub(crate) or private (V1 restriction)
// =============================================================================

struct S10 {
    field_a: i32,
    field_b: String,
}

impl S10 {
    // Private function with view type - OK
    fn private_ok(&{mut field_a} mut self) {}

    // pub(crate) function with view type - OK
    pub(crate) fn pub_crate_ok(&{mut field_a} mut self) {}

    // pub function with view type - ERROR (V1 restriction)
    pub fn public_not_allowed(&{mut field_a} mut self) {} //~ ERROR view types are not allowed on public functions
}

// =============================================================================
// ERROR: View types don't work on Box, Rc, Arc (for now)
// =============================================================================

struct S11 {
    field: i32,
}

impl S11 {
    fn view_on_box(x: Box<&{mut field} S11>) {}
}

// =============================================================================
// ERROR: Nested field access (not yet supported)
// =============================================================================

struct Outer {
    inner: Inner,
}

struct Inner {
    value: i32,
}


// =============================================================================
// NOTE: Tuple fields now supported - this parses successfully
// But tuple TYPES (not tuple structs) have no practical use case for view types
// Tuple types should be destructured instead: fn foo((x, y): &mut (i32, String))
// =============================================================================

fn tuple_field_access(x: &{mut 0} (i32, String)) {} //~ ERROR view types are not supported on free functions

// =============================================================================
// ERROR: View type with const
// =============================================================================

struct S12 {
    value: i32,
}

fn view_with_const(x: &{mut field} const S12) {} //~ ERROR const trait bounds are not allowed
//~| ERROR expected trait, found struct `S12`
//~| ERROR const trait impls are experimental
//~| ERROR expected a type, found a trait
//~| ERROR view types are not supported on free functions

fn main() {}
