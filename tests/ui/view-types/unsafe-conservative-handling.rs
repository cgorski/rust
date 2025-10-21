//@ check-pass
//@ compile-flags: --crate-type=lib

#![feature(view_types)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(incomplete_features)]
#![allow(unused_unsafe)]
#![allow(unused_mut)]

// Test file: Conservative Unsafe Handling
//
// This file tests the conservative handling of unsafe blocks in view-typed functions.
//
// Conservative Handling Policy:
// - Any function with an unsafe block is treated as potentially accessing ALL fields
// - This is sound: we never assume safety that doesn't exist
// - This is conservative: we may reject valid code
// - Future: implement flow-sensitive analysis for Tier 2 (tracked unsafe)
//
// Corresponds to: Theorem conservative_handling_is_sound in Unsafe_Interaction.v

use std::ptr;

struct Server {
    request_count: u64,
    error_count: u64,
    config: String,
    cache: Vec<u8>,
}

// ============================================================================
// TEST 1: Basic Conservative Handling
// ============================================================================

impl Server {
    /// Contains unsafe block - treated conservatively
    /// Compiler assumes this MAY access any field
    fn increment_with_unsafe(&{mut request_count} mut self) {
        unsafe {
            let ptr = &raw mut self.request_count;
            *ptr += 1;
        }
        // Conservative: compiler treats this as potentially accessing all fields
        // even though we can see it only touches request_count
    }

    /// Safe version for comparison
    fn increment_safe(&{mut request_count} mut self) {
        self.request_count += 1;
        // Not conservative: compiler knows this only accesses request_count
    }
}

// ============================================================================
// TEST 2: Conservative Handling Prevents Incorrect Optimizations
// ============================================================================

impl Server {
    /// Conservative handling prevents assuming fields are disjoint
    fn conservative_multi_field(&{mut request_count, mut error_count} mut self) {
        unsafe {
            // Even though we can see these are disjoint fields,
            // conservative handling doesn't assume anything about unsafe code
            let req_ptr = &raw mut self.request_count;
            let err_ptr = &raw mut self.error_count;

            *req_ptr = 100;
            *err_ptr = 50;
        }
    }
}

// ============================================================================
// TEST 3: Mixed Safe and Unsafe Code
// ============================================================================

impl Server {
    /// Function with both safe and unsafe sections
    fn mixed_safe_unsafe(&{mut request_count} mut self) {
        // Safe code: fully tracked
        self.request_count += 1;

        // Unsafe code: conservatively handled
        unsafe {
            let ptr = &raw mut self.request_count;
            *ptr += 1;
        }

        // Safe code again: fully tracked
        self.request_count += 1;

        // Conservative: presence of unsafe means conservative handling for entire function
    }
}

// ============================================================================
// TEST 4: Nested Unsafe Blocks
// ============================================================================

impl Server {
    /// Multiple unsafe blocks in one function
    fn multiple_unsafe_blocks(&{mut request_count, mut error_count} mut self) {
        unsafe {
            let ptr1 = &raw mut self.request_count;
            *ptr1 = 0;
        }

        self.request_count += 1; // Safe code between

        unsafe {
            let ptr2 = &raw mut self.error_count;
            *ptr2 = 0;
        }

        // Conservative: all unsafe blocks trigger conservative handling
    }
}

// ============================================================================
// TEST 5: Unsafe Function Calls
// ============================================================================

unsafe fn external_operation(x: &mut u64) {
    *x = 42;
}

impl Server {
    /// Calling unsafe functions triggers conservative handling
    fn call_unsafe_function(&{mut request_count} mut self) {
        unsafe {
            external_operation(&mut self.request_count);
        }
        // Conservative: unsafe function call
    }
}

// ============================================================================
// TEST 6: FFI Calls (Most Conservative)
// ============================================================================

extern "C" {
    fn c_increment(ptr: *mut u64);
}

impl Server {
    /// FFI calls are maximally conservative
    fn call_ffi(&{mut request_count} mut self) {
        unsafe {
            c_increment(&mut self.request_count as *mut u64);
        }
        // Conservative: FFI has no guarantees about what it accesses
    }
}

// ============================================================================
// TEST 7: Pointer-Based Algorithms
// ============================================================================

impl Server {
    /// Complex unsafe algorithm - conservative handling
    fn complex_unsafe_algorithm(&{mut cache} mut self) {
        unsafe {
            if self.cache.len() >= 4 {
                let ptr = self.cache.as_mut_ptr();

                // Swap bytes using pointers
                let a = ptr::read(ptr);
                let b = ptr::read(ptr.add(1));
                ptr::write(ptr, b);
                ptr::write(ptr.add(1), a);
            }
        }
        // Conservative: complex pointer operations
    }
}

// ============================================================================
// TEST 8: Union Access
// ============================================================================

union DataUnion {
    as_int: u64,
    as_float: f64,
}

struct UnionContainer {
    data: DataUnion,
    other: u32,
}

impl UnionContainer {
    /// Union access is always unsafe - conservative handling
    fn access_union(&{mut data} mut self) {
        unsafe {
            self.data.as_int = 42;
        }
        // Conservative: union access
    }
}

// ============================================================================
// TEST 9: Atomic Operations
// ============================================================================

use std::sync::atomic::{AtomicU64, Ordering};

struct AtomicServer {
    atomic_count: AtomicU64,
    regular_count: u64,
}

impl AtomicServer {
    /// Atomic operations with unsafe - conservative
    fn atomic_with_unsafe(&{atomic_count} self) {
        unsafe {
            let ptr = &self.atomic_count as *const AtomicU64;
            // Even though atomics are safe, using unsafe around them is conservative
            let _val = (*ptr).load(Ordering::Relaxed);
        }
    }
}

// ============================================================================
// TEST 10: Documentation of Conservative Approach
// ============================================================================

impl Server {
    /// CONSERVATIVE EXAMPLE: Function appears to only touch request_count
    ///
    /// However, because it contains unsafe code, the compiler CANNOT verify
    /// that it truly only touches request_count. It might:
    /// - Cast self to *mut Server and access other fields
    /// - Use pointer arithmetic to reach other fields
    /// - Call FFI that modifies other fields
    /// - Do transmute tricks
    ///
    /// Therefore: Conservative handling treats this as potentially accessing
    /// ALL fields, which is always sound but may be overly restrictive.
    fn documented_conservative(&{mut request_count} mut self) {
        unsafe {
            let ptr = &raw mut self.request_count;
            *ptr += 1;
        }
    }
}

// ============================================================================
// FUTURE: Tier 2 (Tracked Unsafe)
// ============================================================================

// In the future, we could implement Tier 2: Tracked Unsafe
// This would use flow-sensitive analysis to verify that unsafe code
// respects view contracts.
//
// Example of what could be tracked:
//
// fn tier2_trackable(&{mut request_count} mut self) {
//     unsafe {
//         let ptr = &raw mut self.request_count;  // Track: ptr -> request_count
//         *ptr += 1;                               // Verify: only touches request_count
//     }
//     // Could prove: unsafe code respects contract
// }
//
// vs.
//
// fn tier2_untrackable(&{mut request_count} mut self) {
//     unsafe {
//         let ptr = arbitrary_pointer();
//         *ptr = 0;
//     }
//     // Cannot track: arbitrary pointer
//     // Falls back to conservative (Tier 3)
// }

// ============================================================================
// GUARANTEES
// ============================================================================

// Conservative handling provides these GUARANTEES:
//
// 1. SOUNDNESS: We never assume safety that doesn't exist
//    - If unsafe code violates contract, we don't optimize incorrectly
//    - Conservative = always safe
//
// 2. COMPATIBILITY: Existing unsafe code continues to work
//    - View types don't break unsafe patterns
//    - Unsafe has same semantics with or without view types
//
// 3. CLARITY: Programmers know what to expect
//    - unsafe block = conservative handling
//    - No surprising optimizations
//    - Clear documentation of tradeoffs
//
// TRADEOFFS:
//
// 1. May reject valid code
//    - Unsafe code that respects contract is treated conservatively
//    - Solution: use safe code where possible, or wait for Tier 2
//
// 2. Less optimization
//    - Can't assume disjoint access in presence of unsafe
//    - Conservative = fewer optimizations
//
// 3. Documentation burden
//    - Programmer must understand conservative model
//    - Need to document when unsafe respects contracts

// ============================================================================
// TEST VALIDATION
// ============================================================================

// This test file should compile successfully (check-pass)
// All functions demonstrate conservative handling
// No undefined behavior (all unsafe code respects actual contracts)
//
// Corresponds to Coq theorems:
// - conservative_handling_is_sound: Always sound ✓
// - view_types_preserve_unsafe_semantics: No weakening ✓
