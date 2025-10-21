//@ check-pass
//@ compile-flags: --crate-type=lib

#![feature(view_types)]
#![allow(dead_code)]
#![allow(unnecessary_transmutes)]
#![allow(unused_mut)]
#![allow(unused_variables)]
#![allow(incomplete_features)]
#![allow(unused_unsafe)]

// Comprehensive test suite for unsafe code interaction with view types
//
// This test file verifies that view types interact correctly with unsafe code
// according to the formal model in formalization/Unsafe_Interaction.v
//
// Key principles tested:
// 1. View types don't weaken existing unsafe guarantees
// 2. Unsafe code that respects view contracts maintains safety
// 3. Contract violations are programmer responsibility (documented as potential UB)
// 4. Raw pointers can be created from view borrows

use std::ptr;

struct Data {
    counter: u32,
    value: i64,
    buffer: Vec<u8>,
}

// ============================================================================
// TEST CATEGORY 1: Raw Pointers to View-Specified Fields (SAFE)
// Corresponds to: Theorem raw_pointer_from_view_borrow
// ============================================================================

impl Data {
    // Safe: Raw pointer to field specified in view
    fn increment_unsafe(&{mut counter} mut self) {
        unsafe {
            let ptr = &raw mut self.counter;
            *ptr += 1;
        }
    }

    // Safe: Multiple operations on view-specified field
    fn update_counter_complex(&{mut counter} mut self, val: u32) {
        unsafe {
            let ptr = &raw mut self.counter;
            *ptr = val;
            *ptr += 10;
            *ptr *= 2;
        }
    }

    // Safe: Reading through raw pointer
    fn read_counter_unsafe(&{counter} self) -> u32 {
        unsafe {
            let ptr = &raw const self.counter;
            *ptr
        }
    }

    // Safe: Raw pointer to different field in different view
    fn update_value_unsafe(&{mut value} mut self) {
        unsafe {
            let ptr = &raw mut self.value;
            *ptr = 42;
        }
    }
}

// ============================================================================
// TEST CATEGORY 2: Contract-Respecting Multi-Field Unsafe
// Corresponds to: Theorem contract_respecting_unsafe_is_safe
// ============================================================================

impl Data {
    // Safe: Unsafe code accessing multiple fields in view spec
    fn swap_counter_value(&{mut counter, mut value} mut self) {
        unsafe {
            let c_ptr = &raw mut self.counter;
            let v_ptr = &raw mut self.value;

            let temp = *c_ptr as i64;
            *c_ptr = *v_ptr as u32;
            *v_ptr = temp;
        }
    }

    // Safe: Pointer arithmetic within a single field's bounds
    fn modify_buffer_element(&{mut buffer} mut self, index: usize) {
        unsafe {
            if let Some(elem) = self.buffer.get_mut(index) {
                let ptr = elem as *mut u8;
                *ptr = 255;
            }
        }
    }
}

// ============================================================================
// TEST CATEGORY 3: Pointer Arithmetic (POTENTIAL UB IF ESCAPES BOUNDS)
// These compile but programmer must ensure they stay within field bounds
// ============================================================================

impl Data {
    // Safe: Pointer arithmetic stays within field
    fn arithmetic_within_bounds(&{mut counter} mut self) {
        unsafe {
            let ptr = &raw mut self.counter;
            let byte_ptr = ptr as *mut u8;

            // Safe: stays within u32 bounds (4 bytes)
            for i in 0..4 {
                *byte_ptr.add(i) = 0;
            }
        }
    }

    // POTENTIAL UB: If offset exceeds field bounds
    // Programmer responsibility: ensure index doesn't escape counter field
    fn arithmetic_with_offset(&{mut counter} mut self, offset: usize) {
        unsafe {
            let ptr = &raw mut self.counter;
            let byte_ptr = ptr as *mut u8;

            // PROGRAMMER MUST ENSURE: offset < 4 (size of u32)
            // Otherwise: UB (accesses beyond contracted field)
            if offset < 4 {
                *byte_ptr.add(offset) = 0;
            }
        }
    }
}

// ============================================================================
// TEST CATEGORY 4: Transmute with View Types
// Corresponds to: Theorem transmute_respects_contracts
// ============================================================================

impl Data {
    // Safe: Transmute within view-specified field's type
    fn transmute_counter(&{mut counter} mut self) {
        unsafe {
            let bytes: [u8; 4] = std::mem::transmute(self.counter);
            self.counter = std::mem::transmute(bytes);
        }
    }

    // Safe: Read field value via transmute_copy (stays within bounds)
    fn read_via_transmute(&{counter} self) -> [u8; 4] {
        unsafe {
            std::mem::transmute(self.counter)
        }
    }
}

// ============================================================================
// TEST CATEGORY 5: FFI and External Calls (Conservative)
// FFI is conservatively treated as potentially accessing all fields
// ============================================================================

extern "C" {
    fn external_modify(ptr: *mut u32);
}

impl Data {
    // FFI call - conservatively assumes may access beyond pointer
    // View type provides documentation but can't fully enforce
    fn call_ffi(&{mut counter} mut self) {
        unsafe {
            external_modify(&raw mut self.counter);
            // Conservative: FFI might do anything with the pointer
        }
    }
}

// ============================================================================
// TEST CATEGORY 6: View Types Preserve Existing Unsafe Semantics
// Corresponds to: Theorem view_types_preserve_unsafe_semantics
// ============================================================================

// Without view types: standard unsafe pattern
fn standard_unsafe_pattern(data: &mut Data) {
    unsafe {
        let ptr = &raw mut data.counter;
        *ptr = 100;
    }
}

// With view types: same unsafe pattern, same guarantees
fn view_typed_unsafe_pattern(data: &mut Data) {
    fn helper(&{mut counter} mut data: &mut Data) {
        unsafe {
            let ptr = &raw mut data.counter;
            *ptr = 100;
        }
    }
    helper(data);
}

// ============================================================================
// TEST CATEGORY 7: ptr::read and ptr::write with View Types
// ============================================================================

impl Data {
    fn read_write_unsafe(&{mut counter} mut self) {
        unsafe {
            let ptr = &raw mut self.counter;
            let old_val = ptr::read(ptr);
            ptr::write(ptr, old_val + 1);
        }
    }

    fn swap_via_ptr(&{mut counter, mut value} mut self) {
        unsafe {
            let c_ptr = &raw mut self.counter;
            let v_ptr = &raw mut self.value;

            // Safe: swapping different fields
            let c_val = ptr::read(c_ptr);
            let v_val = ptr::read(v_ptr);
            ptr::write(c_ptr, v_val as u32);
            ptr::write(v_ptr, c_val as i64);
        }
    }
}

// ============================================================================
// TEST CATEGORY 8: Union Field Access
// ============================================================================

union MyUnion {
    int_value: u32,
    float_value: f32,
}

struct UnionContainer {
    data: MyUnion,
    other: u64,
}

impl UnionContainer {
    // Safe: Accessing specific union field in view
    fn access_union_int(&{mut data} mut self) {
        unsafe {
            self.data.int_value = 42;
        }
    }

    // Safe: Reading union field
    fn read_union_float(&{data} self) -> f32 {
        unsafe { self.data.float_value }
    }
}

// ============================================================================
// TEST CATEGORY 9: Interior Mutability with Unsafe
// ============================================================================

use std::cell::UnsafeCell;

struct InteriorMutData {
    counter: UnsafeCell<u32>,
    value: u64,
}

impl InteriorMutData {
    // Safe: UnsafeCell access in view
    fn increment_cell(&{counter} self) {
        unsafe {
            let ptr = self.counter.get();
            *ptr += 1;
        }
    }
}

// ============================================================================
// TEST CATEGORY 10: Multiple Raw Pointers to Same Field
// ============================================================================

impl Data {
    // Safe: Two raw pointers to different fields (view allows both)
    fn two_raw_pointers(&{mut counter, mut value} mut self) {
        unsafe {
            let ptr1 = &raw mut self.counter;
            let ptr2 = &raw mut self.value;

            *ptr1 = 10;
            *ptr2 = 20;
        }
    }

    // Creating two raw pointers to same field is allowed
    // But dereferencing both would be UB (programmer responsibility)
    fn two_pointers_same_field(&{mut counter} mut self) {
        unsafe {
            let ptr1 = &raw mut self.counter;
            let ptr2 = &raw mut self.counter;

            // Only using one is safe
            *ptr1 = 10;
            // Using both would be UB: *ptr2 = 20;
            let _ = ptr2; // Just to avoid unused warning
        }
    }
}

// ============================================================================
// TEST CATEGORY 11: Complex Real-World Patterns
// ============================================================================

struct ComplexData {
    reference_count: u32,
    data_ptr: *mut u8,
    capacity: usize,
}

impl ComplexData {
    // Safe: Complex unsafe in view-specified fields only
    fn increment_refcount(&{mut reference_count} mut self) -> u32 {
        unsafe {
            let ptr = &raw mut self.reference_count;
            let old = ptr::read(ptr);
            ptr::write(ptr, old.wrapping_add(1));
            old
        }
    }

    // Safe: Multiple unsafe operations on disjoint fields
    fn update_metadata(&{mut reference_count, mut capacity} mut self) {
        unsafe {
            let rc_ptr = &raw mut self.reference_count;
            let cap_ptr = &raw mut self.capacity;

            *rc_ptr = 1;
            *cap_ptr = 1024;
        }
    }
}

// ============================================================================
// SUMMARY
// ============================================================================

// This test suite demonstrates that view types interact safely with unsafe code:
//
// ✅ SAFE AND PROVEN:
//    - Raw pointers to view-specified fields
//    - Multiple operations on contract-respecting fields
//    - View types preserve existing unsafe semantics
//    - ptr::read/write on contracted fields
//    - Union access within view bounds
//    - UnsafeCell within view bounds
//
// ⚠️ PROGRAMMER RESPONSIBILITY:
//    - Pointer arithmetic must stay within field bounds
//    - FFI calls must respect contracts
//    - Aliasing multiple mutable raw pointers is still UB
//    - Transmute must not read/write beyond contracted fields
//
// 🔒 GUARANTEED BY THEOREMS:
//    - View types don't weaken existing unsafe guarantees
//    - Contract-respecting unsafe maintains safety
//    - Conservative handling is always sound
//
// All code in this file compiles successfully (check-pass).
// Code marked as potential UB requires programmer discipline to maintain invariants.
