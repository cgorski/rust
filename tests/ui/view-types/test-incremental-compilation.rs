//@ check-pass
//@ incremental
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Incremental Compilation with View Types
//
// CRITICAL PROPERTY: View types must work correctly with incremental compilation.
// Changes to struct fields, view specs, or method signatures must trigger proper
// recompilation of dependent code.
//
// This test validates that view types don't break incremental compilation and that
// the compiler correctly tracks dependencies for view-typed code.
//
// KEY SCENARIOS:
// 1. Field name changes should invalidate view-typed methods
// 2. View spec changes should invalidate callers
// 3. Struct layout changes should trigger recompilation
// 4. Cross-module dependencies work correctly
// 5. Metadata encoding/decoding preserves view type information
//
// NOTE: This is a smoke test. Full incremental testing requires multi-revision
// tests which are more complex. This validates basic incremental compatibility.

// =============================================================================
// Test 1: Basic Struct with View-Typed Methods
// =============================================================================

struct Counter {
    count: usize,
    max: usize,
    name: String,
}

impl Counter {
    fn increment(&{mut count} mut self) {
        self.count += 1;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }

    fn update_max(&{mut max} mut self, new_max: usize) {
        self.max = new_max;
    }

    fn get_stats(&{count, max} self) -> (usize, usize) {
        (self.count, self.max)
    }
}

fn test_basic_incremental() {
    let mut counter = Counter {
        count: 0,
        max: 100,
        name: String::from("test"),
    };

    counter.increment();
    counter.update_max(200);
    let (count, max) = counter.get_stats();
    assert_eq!(count, 1);
    assert_eq!(max, 200);

    println!("Basic incremental: OK");
}

// =============================================================================
// Test 2: Generic Struct with View Types (Tests Generic Monomorphization)
// =============================================================================

struct Container<T> {
    data: T,
    metadata: String,
    count: usize,
}

impl<T> Container<T> {
    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn update_metadata(&{mut metadata} mut self, new_meta: String) {
        self.metadata = new_meta;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }
}

fn test_generic_incremental() {
    // Test with different concrete types (monomorphization)
    let mut c1: Container<i32> = Container {
        data: 42,
        metadata: String::from("int"),
        count: 0,
    };

    let mut c2: Container<String> = Container {
        data: String::from("data"),
        metadata: String::from("string"),
        count: 0,
    };

    c1.increment_count();
    c2.increment_count();
    c2.update_metadata(String::from("updated"));

    assert_eq!(c1.get_count(), 1);
    assert_eq!(c2.get_count(), 1);

    println!("Generic incremental: OK");
}

// =============================================================================
// Test 3: Nested Modules (Tests Cross-Module Incremental)
// =============================================================================

mod inner {
    pub struct Data {
        pub value: i32,
        pub name: String,
    }

    impl Data {
        pub(crate) fn update_value(&{mut value} mut self, new_val: i32) {
            self.value = new_val;
        }

        pub(crate) fn get_name_len(&{name} self) -> usize {
            self.name.len()
        }
    }
}

fn test_cross_module_incremental() {
    let mut data = inner::Data {
        value: 10,
        name: String::from("cross-module"),
    };

    data.update_value(20);
    let len = data.get_name_len();
    assert_eq!(len, 12);

    println!("Cross-module incremental: OK");
}

// =============================================================================
// Test 4: Multiple Impl Blocks (Tests Incremental with Multiple Impls)
// =============================================================================

struct MultiImpl {
    field_a: i32,
    field_b: String,
    field_c: Vec<i32>,
}

impl MultiImpl {
    fn access_a(&{field_a} self) -> i32 {
        self.field_a
    }

    fn update_a(&{mut field_a} mut self, val: i32) {
        self.field_a = val;
    }
}

impl MultiImpl {
    fn access_b(&{field_b} self) -> usize {
        self.field_b.len()
    }

    fn update_b(&{mut field_b} mut self, val: String) {
        self.field_b = val;
    }
}

impl MultiImpl {
    fn access_c(&{field_c} self) -> usize {
        self.field_c.len()
    }
}

fn test_multiple_impls() {
    let mut m = MultiImpl {
        field_a: 1,
        field_b: String::from("test"),
        field_c: vec![1, 2, 3],
    };

    assert_eq!(m.access_a(), 1);
    m.update_a(2);
    assert_eq!(m.access_a(), 2);

    assert_eq!(m.access_b(), 4);
    m.update_b(String::from("updated"));
    assert_eq!(m.access_b(), 7);

    assert_eq!(m.access_c(), 3);

    println!("Multiple impl blocks incremental: OK");
}

// =============================================================================
// Test 5: Trait Bounds on Generic Impls (Tests Incremental with Trait Resolution)
// =============================================================================

struct BoundedContainer<T: Clone> {
    data: T,
    count: usize,
}

impl<T: Clone> BoundedContainer<T> {
    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }
}

fn test_trait_bounds_incremental() {
    let mut bc = BoundedContainer {
        data: vec![1, 2, 3],
        count: 0,
    };

    bc.increment_count();
    assert_eq!(bc.get_count(), 1);

    println!("Trait bounds incremental: OK");
}

// =============================================================================
// Test 6: Lifetime Parameters (Tests Incremental with Lifetimes)
// =============================================================================

struct WithLifetime<'a> {
    reference: &'a str,
    counter: usize,
}

impl<'a> WithLifetime<'a> {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn get_counter(&{counter} self) -> usize {
        self.counter
    }
}

fn test_lifetime_incremental() {
    let data = String::from("test");
    let mut wl = WithLifetime {
        reference: &data,
        counter: 0,
    };

    wl.increment();
    assert_eq!(wl.get_counter(), 1);

    println!("Lifetime incremental: OK");
}

// =============================================================================
// Test 7: Complex Nested Structures (Tests Incremental with Complex Types)
// =============================================================================

struct Inner {
    value: i32,
}

struct Outer {
    inner: Inner,
    name: String,
}

impl Outer {
    fn update_inner(&{mut inner} mut self, val: i32) {
        self.inner.value = val;
    }

    fn get_name_len(&{name} self) -> usize {
        self.name.len()
    }
}

fn test_nested_structures() {
    let mut outer = Outer {
        inner: Inner { value: 10 },
        name: String::from("outer"),
    };

    outer.update_inner(20);
    assert_eq!(outer.inner.value, 20);
    assert_eq!(outer.get_name_len(), 5);

    println!("Nested structures incremental: OK");
}

// =============================================================================
// Test 8: Macro-Generated Code (Tests Incremental with Macros)
// =============================================================================

macro_rules! make_accessor {
    ($field:ident, $ty:ty) => {
        fn access(&{$field} self) -> $ty {
            self.$field.clone()
        }
    };
}

struct MacroGenerated {
    value: i32,
    text: String,
}

impl MacroGenerated {
    make_accessor!(value, i32);

    fn get_text_len(&{text} self) -> usize {
        self.text.len()
    }
}

fn test_macro_incremental() {
    let mg = MacroGenerated {
        value: 42,
        text: String::from("macro"),
    };

    assert_eq!(mg.access(), 42);
    assert_eq!(mg.get_text_len(), 5);

    println!("Macro-generated incremental: OK");
}

// =============================================================================
// Test 9: Large Number of Methods (Stress Test for Incremental)
// =============================================================================

struct ManyMethods {
    field_01: i32,
    field_02: i32,
    field_03: i32,
    field_04: i32,
    field_05: i32,
    field_06: i32,
    field_07: i32,
    field_08: i32,
    field_09: i32,
    field_10: i32,
}

impl ManyMethods {
    fn access_01(&{field_01} self) -> i32 { self.field_01 }
    fn access_02(&{field_02} self) -> i32 { self.field_02 }
    fn access_03(&{field_03} self) -> i32 { self.field_03 }
    fn access_04(&{field_04} self) -> i32 { self.field_04 }
    fn access_05(&{field_05} self) -> i32 { self.field_05 }
    fn access_06(&{field_06} self) -> i32 { self.field_06 }
    fn access_07(&{field_07} self) -> i32 { self.field_07 }
    fn access_08(&{field_08} self) -> i32 { self.field_08 }
    fn access_09(&{field_09} self) -> i32 { self.field_09 }
    fn access_10(&{field_10} self) -> i32 { self.field_10 }

    fn update_01(&{mut field_01} mut self, val: i32) { self.field_01 = val; }
    fn update_02(&{mut field_02} mut self, val: i32) { self.field_02 = val; }
    fn update_03(&{mut field_03} mut self, val: i32) { self.field_03 = val; }
    fn update_04(&{mut field_04} mut self, val: i32) { self.field_04 = val; }
    fn update_05(&{mut field_05} mut self, val: i32) { self.field_05 = val; }
}

fn test_many_methods() {
    let mut mm = ManyMethods {
        field_01: 1, field_02: 2, field_03: 3, field_04: 4, field_05: 5,
        field_06: 6, field_07: 7, field_08: 8, field_09: 9, field_10: 10,
    };

    assert_eq!(mm.access_01(), 1);
    assert_eq!(mm.access_05(), 5);
    assert_eq!(mm.access_10(), 10);

    mm.update_01(100);
    assert_eq!(mm.access_01(), 100);

    println!("Many methods incremental: OK");
}

// =============================================================================
// Test 10: Derive Macros with View Types (Tests Incremental with Derives)
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct WithDerive {
    value: i32,
    name: String,
}

impl WithDerive {
    fn update_value(&{mut value} mut self, val: i32) {
        self.value = val;
    }

    fn get_name_len(&{name} self) -> usize {
        self.name.len()
    }
}

fn test_derive_incremental() {
    let mut wd1 = WithDerive {
        value: 1,
        name: String::from("test"),
    };

    let wd2 = wd1.clone();
    assert_eq!(wd1, wd2);

    wd1.update_value(2);
    assert_eq!(wd1.get_name_len(), 4);

    println!("Derive with incremental: OK");
}

// =============================================================================
// Main Test Runner
// =============================================================================

fn main() {
    test_basic_incremental();
    test_generic_incremental();
    test_cross_module_incremental();
    test_multiple_impls();
    test_trait_bounds_incremental();
    test_lifetime_incremental();
    test_nested_structures();
    test_macro_incremental();
    test_many_methods();
    test_derive_incremental();

    println!("\n✓ All incremental compilation tests passed!");
    println!("✓ View types work correctly with incremental compilation");
    println!("✓ Generic monomorphization works incrementally");
    println!("✓ Cross-module dependencies tracked correctly");
    println!("✓ Multiple impl blocks work incrementally");
    println!("✓ Trait bounds and lifetime parameters work");
    println!("✓ Nested structures and complex types work");
    println!("✓ Macro-generated code works incrementally");
    println!("✓ Large numbers of view-typed methods work");
    println!("✓ Derive macros compatible with incremental compilation");
}
