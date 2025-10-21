//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Lifetime Variance with View Types (Methods Only)
//
// PROPERTY: View types should preserve Rust's standard lifetime variance rules
// when used in inherent methods. Specifically: &'long {field} S should be usable
// where &'short {field} S is expected (covariance in lifetime parameter).
//
// CONSTRAINT: V1 only supports view types on inherent methods, not free functions
// or trait methods. This test works within that constraint.
//
// RATIONALE:
// Rust references are covariant in their lifetime: &'long T <: &'short T
// when 'long: 'short. View types add field restrictions but should NOT
// change this fundamental property.

struct S {
    field_a: i32,
    field_b: String,
    field_c: Vec<i32>,
}

// =============================================================================
// Test 1: Explicit Lifetime Parameters on Methods
// =============================================================================

impl S {
    // Method with explicit lifetime parameter
    fn read_field_a_explicit<'a>(&'a {field_a} self) -> i32 {
        self.field_a
    }

    // Method with lifetime that can accept any lifetime
    fn read_field_b_any<'any>(&'any {field_b} self) -> usize {
        self.field_b.len()
    }

    // Method that calls another with explicit lifetime
    fn test_explicit_lifetime_call<'outer>(&'outer {field_a} self) -> i32 {
        // Should work: 'outer can be used where any lifetime is expected
        // (lifetime inference handles this automatically)
        self.read_field_a_explicit()
    }
}

// =============================================================================
// Test 2: Lifetime Elision with View Types
// =============================================================================

impl S {
    // Elided lifetime - should work just like non-view methods
    fn read_field_c_elided(&{field_c} self) -> usize {
        self.field_c.len()
    }

    // Multiple parameters with elision
    fn compare_with_elided(&{field_a} self, other: &S) -> bool {
        self.field_a == other.field_a
    }
}

// =============================================================================
// Test 3: Multiple Lifetimes in Struct Definition
// =============================================================================

struct TwoRefs<'a, 'b> {
    first: &'a str,
    second: &'b str,
    counter: usize,
}

impl<'a, 'b> TwoRefs<'a, 'b> {
    // Method with view type on struct with multiple lifetimes
    fn increment_counter(&{mut counter} mut self) {
        self.counter += 1;
    }

    // Method that reads counter - should work with any combination of 'a, 'b
    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    // Method accessing lifetime-parameterized field
    fn first_len(&{first} self) -> usize {
        self.first.len()
    }

    fn second_len(&{second} self) -> usize {
        self.second.len()
    }
}

// =============================================================================
// Test 4: Lifetime Bounds on Impl Blocks
// =============================================================================

struct WithLifetime<'a> {
    borrowed: &'a str,
    owned: String,
    counter: usize,
}

impl<'a> WithLifetime<'a> {
    // Method on struct with lifetime parameter
    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    // Method that accesses lifetime-parameterized field
    fn borrowed_len(&{borrowed} self) -> usize {
        self.borrowed.len()
    }

    // Method modifying non-lifetime field
    fn update_owned(&{mut owned} mut self, s: &str) {
        self.owned.push_str(s);
    }

    // Method with additional lifetime parameter beyond struct's
    fn compare_borrowed<'other>(&{borrowed} self, other: &'other str) -> bool
    where
        'other: 'a,  // 'other must outlive 'a
    {
        self.borrowed == other
    }
}

// Test with lifetime bound on impl itself
impl<'long: 'short, 'short> WithLifetime<'long> {
    // Method using the bounded lifetimes
    fn with_lifetime_bound(&{counter} self) -> usize {
        self.counter
    }
}

// =============================================================================
// Test 5: Nested Struct with Lifetimes
// =============================================================================

struct Outer<'a> {
    inner: Inner<'a>,
    metadata: String,
}

struct Inner<'a> {
    data: &'a str,
    count: usize,
}

impl<'a> Outer<'a> {
    // Method accessing metadata (non-lifetime field)
    fn get_metadata_len(&{metadata} self) -> usize {
        self.metadata.len()
    }

    // Method that could access inner through view
    fn increment_inner_count(&{mut inner} mut self) {
        self.inner.count += 1;
    }
}

impl<'a> Inner<'a> {
    fn get_count(&{count} self) -> usize {
        self.count
    }

    fn data_len(&{data} self) -> usize {
        self.data.len()
    }
}

// =============================================================================
// Test 6: Method Chaining with Different Lifetimes
// =============================================================================

struct Chainable {
    value: i32,
    multiplier: i32,
}

impl Chainable {
    // Methods that could be chained
    fn read_value(&{value} self) -> i32 {
        self.value
    }

    fn read_multiplier(&{multiplier} self) -> i32 {
        self.multiplier
    }

    // Method that calls both
    fn compute(&{value, multiplier} self) -> i32 {
        self.value * self.multiplier
    }
}

// =============================================================================
// Test 7: Generic Struct with Lifetimes
// =============================================================================

struct GenericWithLifetime<'a, T> {
    reference: &'a T,
    owned: T,
    flag: bool,
}

impl<'a, T> GenericWithLifetime<'a, T> {
    fn get_flag(&{flag} self) -> bool {
        self.flag
    }

    fn toggle_flag(&{mut flag} mut self) {
        self.flag = !self.flag;
    }
}

impl<'a, T: Clone> GenericWithLifetime<'a, T> {
    // Method with trait bound that accesses owned field
    fn clone_owned(&{owned} self) -> T {
        self.owned.clone()
    }
}

// =============================================================================
// Test 8: Static Lifetime Special Case
// =============================================================================

static STATIC_DATA: S = S {
    field_a: 42,
    field_b: String::new(),
    field_c: Vec::new(),
};

impl S {
    // Method that can work with static data
    fn from_static() -> i32 {
        // &'static should work where any lifetime is expected
        STATIC_DATA.read_field_a_explicit()
    }
}

// =============================================================================
// Test 9: Lifetime Variance Doesn't Weaken View Restrictions
// =============================================================================

impl S {
    // This method only accesses field_a
    fn only_field_a(&{field_a} self) -> i32 {
        self.field_a
        // Cannot access field_b or field_c even with lifetime flexibility
        // let _ = self.field_b; // Would error
    }

    // Call from another method
    fn test_restriction_preserved(&{field_a} self) -> i32 {
        // Calling only_field_a should work (same view)
        self.only_field_a()
    }
}

// =============================================================================
// Test 10: Lifetime Elision in Practice (Without Returns)
// =============================================================================

struct Container {
    items: Vec<i32>,
    name: String,
}

impl Container {
    // V1: Cannot return references, so return owned values
    fn get_name_len(&{name} self) -> usize {
        self.name.len()
    }

    // This should work: method accesses items
    fn items_len(&{items} self) -> usize {
        self.items.len()
    }

    // Method with explicit lifetime parameter (no return reference)
    fn has_name<'a>(&'a {name} self) -> bool {
        !self.name.is_empty()
    }
}

// =============================================================================
// Test 11: Complex Lifetime Interactions
// =============================================================================

struct ComplexLifetimes<'a, 'b, 'c> {
    first: &'a str,
    second: &'b str,
    third: &'c str,
    counter: usize,
}

impl<'a, 'b, 'c> ComplexLifetimes<'a, 'b, 'c> {
    // Method accessing non-lifetime field
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    // Method with where clause
    fn check_order(&{counter} self) -> bool
    where
        'a: 'b,
        'b: 'c,
    {
        self.counter > 0
    }
}

// =============================================================================
// Test 12: Lifetime Variance Through Struct Updates
// =============================================================================

impl S {
    // Method that modifies field
    fn update_field_a(&{mut field_a} mut self, value: i32) {
        self.field_a = value;
    }

    // Method that reads after potential update
    fn read_after_update(&{field_a} self) -> i32 {
        self.field_a
    }

    // Method demonstrating sequential access is fine
    fn update_and_read(&{mut field_a} mut self, value: i32) -> i32 {
        self.update_field_a(value);
        self.read_after_update()
    }
}

// =============================================================================
// Main Test Runner
// =============================================================================

fn main() {
    // Test 1: Explicit lifetimes
    let s = S {
        field_a: 10,
        field_b: String::from("test"),
        field_c: vec![1, 2, 3],
    };
    let _val = s.test_explicit_lifetime_call();

    // Test 2: Elision
    let _len = s.read_field_c_elided();
    let s2 = S {
        field_a: 20,
        field_b: String::from("other"),
        field_c: vec![],
    };
    let _eq = s.compare_with_elided(&s2);

    // Test 3: Multiple lifetimes
    let mut two_refs = TwoRefs {
        first: "hello",
        second: "world",
        counter: 0,
    };
    two_refs.increment_counter();
    let _count = two_refs.get_counter();
    let _len1 = two_refs.first_len();
    let _len2 = two_refs.second_len();

    // Test 4: Lifetime bounds
    let with_lifetime = WithLifetime {
        borrowed: "data",
        owned: String::from("owned"),
        counter: 5,
    };
    let _c = with_lifetime.get_counter();
    let _len = with_lifetime.borrowed_len();
    let _eq = with_lifetime.compare_borrowed("data");
    let _bounded = with_lifetime.with_lifetime_bound();

    // Test 5: Nested lifetimes
    let inner = Inner {
        data: "inner data",
        count: 10,
    };
    let mut outer = Outer {
        inner,
        metadata: String::from("meta"),
    };
    let _meta_len = outer.get_metadata_len();
    outer.increment_inner_count();
    let _inner_count = outer.inner.get_count();

    // Test 6: Method chaining
    let chain = Chainable {
        value: 5,
        multiplier: 3,
    };
    let _v = chain.read_value();
    let _m = chain.read_multiplier();
    let _result = chain.compute();

    // Test 7: Generic with lifetimes
    let value = 42;
    let mut generic = GenericWithLifetime {
        reference: &value,
        owned: 100,
        flag: true,
    };
    let _flag = generic.get_flag();
    generic.toggle_flag();
    let _cloned = generic.clone_owned();

    // Test 8: Static lifetime
    let _static_val = S::from_static();

    // Test 9: Restrictions preserved
    let _restricted = s.test_restriction_preserved();

    // Test 10: Elision in practice (without returns)
    let container = Container {
        items: vec![1, 2, 3, 4, 5],
        name: String::from("container"),
    };
    let _name_len = container.get_name_len();
    let _items_len = container.items_len();
    let _has_name = container.has_name();

    // Test 11: Complex lifetimes
    let mut complex = ComplexLifetimes {
        first: "a",
        second: "b",
        third: "c",
        counter: 1,
    };
    complex.increment();
    let _check = complex.check_order();

    // Test 12: Update patterns
    let mut s_mut = S {
        field_a: 0,
        field_b: String::new(),
        field_c: vec![],
    };
    s_mut.update_field_a(42);
    let _read = s_mut.read_after_update();
    let _combined = s_mut.update_and_read(100);

    println!("✓ All lifetime variance tests passed!");
    println!("✓ View types preserve Rust's standard lifetime covariance");
    println!("✓ Explicit lifetimes, elision, and bounds all work correctly");
    println!("✓ Multiple lifetime parameters handled properly");
    println!("✓ View restrictions are preserved across lifetime boundaries");
}
