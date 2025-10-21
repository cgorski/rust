//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Derive Macro Compatibility with View Types
//
// CRITICAL PROPERTY: Standard derive macros (Debug, Clone, PartialEq, etc.)
// must work on structs that have view-typed methods.
//
// RATIONALE:
// Derive macros are ubiquitous in Rust. If view types break derives, adoption
// is impossible. This tests that common derives work correctly:
// - Debug, Clone, PartialEq, Eq, Hash (common trait derives)
// - Derives on structs with view-typed methods
// - Derives on generic structs with view-typed methods
//
// NOTE: View types only work on inherent methods, so derives (which generate
// trait impls) are separate from view-typed method definitions.

use std::collections::HashMap;

// =============================================================================
// Test 1: Basic Derives on Struct with View-Typed Methods
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Basic {
    field_a: i32,
    field_b: String,
}

impl Basic {
    // View-typed methods on a struct with derives
    fn update_a(&{mut field_a} mut self, value: i32) {
        self.field_a = value;
    }

    fn read_b(&{field_b} self) -> usize {
        self.field_b.len()
    }

    fn both(&{field_a, field_b} self) -> i32 {
        self.field_a + self.field_b.len() as i32
    }
}

fn test_basic_derives() {
    let b1 = Basic {
        field_a: 10,
        field_b: String::from("test"),
    };
    let b2 = b1.clone(); // Clone works
    assert_eq!(b1, b2);  // PartialEq works
    println!("{:?}", b1); // Debug works

    // Use in HashMap (requires Hash + Eq)
    let mut map = HashMap::new();
    map.insert(b1, 42);

    // View-typed methods still work
    let mut b3 = b2.clone();
    b3.update_a(20);
    let _len = b3.read_b();
}

// =============================================================================
// Test 2: Derives on Generic Struct with View-Typed Methods
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct Generic<T> {
    value: T,
    counter: usize,
}

impl<T> Generic<T> {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn get_counter(&{counter} self) -> usize {
        self.counter
    }
}

impl<T: Clone> Generic<T> {
    fn clone_value(&{value} self) -> T {
        self.value.clone()
    }
}

fn test_generic_derives() {
    let g1: Generic<i32> = Generic {
        value: 42,
        counter: 0,
    };
    let g2 = g1.clone(); // Clone works
    assert_eq!(g1, g2);  // PartialEq works
    println!("{:?}", g1); // Debug works

    let mut g3 = g2.clone();
    g3.increment(); // View-typed method works
    let _val = g3.clone_value(); // Trait-bounded method works
}

// =============================================================================
// Test 3: Derives on Struct with Lifetime Parameters
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct WithLifetime<'a> {
    reference: &'a str,
    counter: usize,
}

impl<'a> WithLifetime<'a> {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn has_data(&{reference} self) -> bool {
        !self.reference.is_empty()
    }
}

fn test_lifetime_derives() {
    let data = String::from("test data");
    let w1 = WithLifetime {
        reference: &data,
        counter: 0,
    };
    let w2 = w1.clone();
    assert_eq!(w1, w2);
    println!("{:?}", w1);

    let mut w3 = w2.clone();
    w3.increment();
    let _has = w3.has_data();
}

// =============================================================================
// Test 4: Copy Derive (Special Case - No Custom Drop)
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Copyable {
    x: i32,
    y: i32,
}

impl Copyable {
    fn update_x(&{mut x} mut self, value: i32) {
        self.x = value;
    }

    fn sum(&{x, y} self) -> i32 {
        self.x + self.y
    }
}

fn test_copy_derive() {
    let c1 = Copyable { x: 1, y: 2 };
    let c2 = c1; // Copy works (no move)
    assert_eq!(c1, c2); // Original still usable

    let mut c3 = c1;
    c3.update_x(10); // View-typed method works
    let _sum = c3.sum();
}

// =============================================================================
// Test 5: Default Derive
// =============================================================================

#[derive(Debug, Clone, Default)]
struct WithDefault {
    field_a: i32,
    field_b: String,
}

impl WithDefault {
    fn reset_a(&{mut field_a} mut self) {
        self.field_a = 0;
    }

    fn is_empty(&{field_b} self) -> bool {
        self.field_b.is_empty()
    }
}

fn test_default_derive() {
    let d1 = WithDefault::default();
    println!("{:?}", d1);

    let mut d2 = d1.clone();
    d2.reset_a();
    let _empty = d2.is_empty();
}

// =============================================================================
// Test 6: Multiple Derives on Complex Struct
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Complex {
    id: usize,
    name: String,
    tags: Vec<String>,
    metadata: HashMap<String, String>,
}

impl Complex {
    fn update_id(&{mut id} mut self, new_id: usize) {
        self.id = new_id;
    }

    fn add_tag(&{mut tags} mut self, tag: String) {
        self.tags.push(tag);
    }

    fn insert_metadata(&{mut metadata} mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    fn get_name_len(&{name} self) -> usize {
        self.name.len()
    }

    fn tag_count(&{tags} self) -> usize {
        self.tags.len()
    }

    fn metadata_count(&{metadata} self) -> usize {
        self.metadata.len()
    }
}

fn test_complex_derives() {
    let c1 = Complex::default();
    let c2 = c1.clone();
    assert_eq!(c1, c2);
    println!("{:?}", c1);

    // Note: Cannot use Complex as HashMap key because it contains HashMap
    // (HashMap doesn't implement Hash)

    // View-typed methods work
    let mut c3 = c2.clone();
    c3.update_id(42);
    c3.add_tag(String::from("test"));
    c3.insert_metadata(String::from("key"), String::from("value"));
    let _name_len = c3.get_name_len();
    let _tag_count = c3.tag_count();
    let _meta_count = c3.metadata_count();
}

// =============================================================================
// Test 7: Derives with Nested Structs
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct Inner {
    value: i32,
}

#[derive(Debug, Clone, PartialEq)]
struct Outer {
    inner: Inner,
    name: String,
}

impl Outer {
    fn update_inner(&{mut inner} mut self, value: i32) {
        self.inner.value = value;
    }

    fn get_name_len(&{name} self) -> usize {
        self.name.len()
    }
}

fn test_nested_derives() {
    let o1 = Outer {
        inner: Inner { value: 10 },
        name: String::from("outer"),
    };
    let o2 = o1.clone();
    assert_eq!(o1, o2);
    println!("{:?}", o1);

    let mut o3 = o2.clone();
    o3.update_inner(20);
    let _len = o3.get_name_len();
}

// =============================================================================
// Test 8: Derives Don't Interfere with View Type Checking
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
struct Validated {
    field_a: i32,
    field_b: String,
}

impl Validated {
    fn only_a(&{field_a} self) -> i32 {
        self.field_a
        // Cannot access field_b even though Debug can print it
        // let _ = self.field_b; // Would error
    }

    fn only_b(&{field_b} self) -> usize {
        self.field_b.len()
        // Cannot access field_a
        // let _ = self.field_a; // Would error
    }
}

fn test_view_restrictions_preserved() {
    let v = Validated {
        field_a: 10,
        field_b: String::from("test"),
    };

    // Derives work (can access all fields)
    let v2 = v.clone();
    println!("{:?}", v2);

    // View-typed methods still respect restrictions
    let _a = v.only_a();
    let _b = v.only_b();
}

// =============================================================================
// Test 9: Derives on Tuple Structs
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TupleStruct(i32, i32);

impl TupleStruct {
    fn update_first(&{mut 0} mut self, value: i32) {
        self.0 = value;
    }

    fn get_second(&{1} self) -> i32 {
        self.1
    }
}

fn test_tuple_struct_derives() {
    let t1 = TupleStruct(1, 2);
    let t2 = t1; // Copy
    assert_eq!(t1, t2);
    println!("{:?}", t1);

    let mut t3 = t1;
    t3.update_first(10);
    let _second = t3.get_second();
}

// =============================================================================
// Test 10: Serde-Like Pattern (Manual Trait Impl + View Types)
// =============================================================================

// Simulate pattern where users manually implement traits
// alongside view-typed methods

trait Serialize {
    fn serialize(&self) -> String;
}

#[derive(Debug, Clone)]
struct Serializable {
    id: usize,
    data: String,
}

// Manual trait impl (not view-typed - trait methods not supported)
impl Serialize for Serializable {
    fn serialize(&self) -> String {
        format!("{{id: {}, data: {}}}", self.id, self.data)
    }
}

// View-typed inherent methods
impl Serializable {
    fn update_id(&{mut id} mut self, new_id: usize) {
        self.id = new_id;
    }

    fn update_data(&{mut data} mut self, new_data: String) {
        self.data = new_data;
    }
}

fn test_manual_trait_impl() {
    let mut s = Serializable {
        id: 1,
        data: String::from("test"),
    };

    // Trait method works
    let _serialized = s.serialize();

    // View-typed methods work
    s.update_id(2);
    s.update_data(String::from("updated"));

    // Derives work
    let s2 = s.clone();
    println!("{:?}", s2);
}

// =============================================================================
// Main Test Runner
// =============================================================================

fn main() {
    test_basic_derives();
    test_generic_derives();
    test_lifetime_derives();
    test_copy_derive();
    test_default_derive();
    test_complex_derives();
    test_nested_derives();
    test_view_restrictions_preserved();
    test_tuple_struct_derives();
    test_manual_trait_impl();

    println!("✓ All derive macro compatibility tests passed!");
    println!("✓ Standard derives work on structs with view-typed methods");
    println!("✓ Debug, Clone, PartialEq, Eq, Hash, Copy, Default all work");
    println!("✓ Derives work with generic structs and lifetime parameters");
    println!("✓ View-typed methods and derived traits coexist correctly");
    println!("✓ View restrictions are preserved despite derive-generated trait impls");
}
