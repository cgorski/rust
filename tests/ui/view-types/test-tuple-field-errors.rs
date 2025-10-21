#![feature(view_types)]
#![allow(incomplete_features)]

// TEST: Tuple Field Error Cases
//
// PURPOSE: Verify that invalid tuple field syntax in view specs is rejected
// with clear, helpful error messages.
//
// ERROR CATEGORIES:
// 1. Integer suffixes (0u32, 1i32) - not allowed
// 2. Negative indices (-1, -2) - not allowed
// 3. Float literals (0.5, 1.0) - lexer tokenizes 0.0 as float (V2 feature)
// 4. Out of bounds indices - parser accepts, type checker rejects
// 5. Very large indices - parser accepts, type checker validates

// =============================================================================
// ERROR: Integer Literal with Suffix
// =============================================================================

struct Point(f32, f32);

fn suffix_u32(x: &{mut 0u32} Point) {} //~ ERROR tuple field index cannot have a suffix

fn suffix_i32(x: &{mut 1i32} Point) {} //~ ERROR tuple field index cannot have a suffix

fn suffix_usize(x: &{mut 0usize} Point) {} //~ ERROR tuple field index cannot have a suffix

// =============================================================================
// ERROR: Negative Indices
// =============================================================================

struct Data(i32, i32, i32);

// Note: The lexer tokenizes -1 as MINUS followed by 1, so this will fail differently
// This test documents the actual error behavior
fn negative_index(x: &{mut -1} Data) {} //~ ERROR expected field name or tuple index

// =============================================================================
// ERROR: Mixed Valid and Invalid Syntax
// =============================================================================

struct Triple(i32, i32, i32);

fn mixed_suffix(x: &{mut 0, mut 1u32} Triple) {} //~ ERROR tuple field index cannot have a suffix

// =============================================================================
// NOTE: Type Checker Errors (Out of Bounds Fields)
// =============================================================================
// These are tested separately because parser errors prevent reaching type checker.
// See test-tuple-fields-typeck-errors.rs for field existence validation tests.
//
// Examples that would fail in type checking:
// - fn out_of_bounds(x: &{mut 2} Pair) where Pair only has 0, 1
// - fn empty_struct(x: &{mut 0} Empty) where Empty has no fields
//
// The parser accepts any non-negative integer; type checker validates field exists.

// =============================================================================
// Main (required to avoid E0601)
// =============================================================================

fn main() {
    // This file tests error cases only
    // All functions above should fail to compile
}
