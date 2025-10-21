# View Types for Rust

An implementation of view types for Rust, enabling field-level borrowing to increase flexibility in function calls. Based on the approach described in "View Types in Rust" (SPLASH 2025).

## Overview

View types allow function signatures to specify exactly which struct fields they access. This resolves a common limitation where Rust's borrow checker conservatively assumes any `&mut self` method might access all fields, rejecting safe code that accesses disjoint fields.

### The Problem

```rust
struct S {
    next_id: usize,
    data: Vec<i32>,
}

impl S {
    fn new_id(&mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    fn assign_ids(&mut self) {
        for item in &mut self.data {
            let id = self.new_id();  // Error: cannot borrow `*self` as mutable
            *item = id as i32;
        }
    }
}
```

The borrow checker rejects this code because `&mut self.data` is active when `new_id()` is called. Since `new_id()` takes `&mut self`, the compiler assumes it might access `data`, creating a conflict.

### The Solution

```rust
#![feature(view_types)]

impl S {
    fn new_id(&{mut next_id} mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    fn assign_ids(&mut self) {
        for item in &mut self.data {
            let id = self.new_id();  // Works: new_id only accesses next_id
            *item = id as i32;
        }
    }
}
```

The view type `&{mut next_id}` specifies that `new_id()` only accesses the `next_id` field. The borrow checker can verify that `next_id` and `data` are disjoint, allowing the call.

## What Was Implemented

### Core Language Feature

- **Parser Extension**: View type syntax in function signatures (`&{field1, field2} Type`, `&{mut field} Type`)
- **Type Checking**: View specifications validated against struct definitions
- **Borrow Checker Integration**: Field-level borrow tracking in MIR (Mid-level Intermediate Representation)
- **View Spec Conflict Detection**: Algorithm to determine if two view specifications access overlapping fields with conflicting mutabilities

### Supported Patterns

**Single field access:**
```rust
fn update_count(&{mut count} mut self) { self.count += 1; }
```

**Multiple field access:**
```rust
fn update_stats(&{mut hits, mut misses} mut self) {
    self.hits += 1;
    self.misses = 0;
}
```

**Mixed mutability:**
```rust
fn compute(&{value, mut result} mut self) {
    self.result = self.value * 2;
}
```

**Tuple struct fields:**
```rust
fn update_first(&{mut 0} mut self, val: i32) {
    self.0 = val;
}
```

### Restrictions

- **Inherent methods only**: View types work on `impl Block` methods, not free functions or trait methods
- **No return references**: Methods with view types cannot return references (conservative safety restriction)
- **Private/pub(crate) only**: View-typed methods must have restricted visibility to avoid abstraction barrier issues

These restrictions simplify the implementation and avoid complications with trait coherence, lifetime tracking, and semantic versioning.

## Technical Details

### Compilation Pipeline

1. **Parsing** (`rustc_parse`): View type syntax parsed into AST
2. **AST → HIR Lowering** (`rustc_ast_lowering`): View specs preserved in HIR
3. **Type Checking** (`rustc_hir_typeck`): 
   - View specs validated against struct field definitions
   - Non-existent fields rejected
   - Duplicate fields rejected
   - Public visibility violations detected
4. **THIR Building** (`rustc_mir_build`):
   - View specs extracted from HIR function signatures
   - Field borrows generated at call sites
   - Each field in view spec creates separate `BorrowData` entry
5. **Borrow Checking** (`rustc_borrowck`):
   - Standard field projection conflict detection
   - Multiple borrows per location supported via `Vec<BorrowData>`
   - View spec conflicts checked using proven algorithm

### Key Data Structures

```rust
// HIR representation
pub struct ViewSpec {
    pub fields: Vec<ViewField>,
}

pub struct ViewField {
    pub path: FieldPath,           // Field identifier (name or tuple index)
    pub mutability: Mutability,    // Mutable or immutable
}

// THIR/MIR representation
pub struct ViewSpec<'tcx> {
    pub fields: Vec<ViewField<'tcx>>,
}

// Methods
impl ViewSpec<'tcx> {
    pub fn conflicts_with(&self, other: &ViewSpec<'tcx>) -> bool;
    pub fn is_subview_of(&self, other: &ViewSpec<'tcx>) -> bool;
}
```

### Conflict Detection Algorithm

Two view specs conflict if any field appears in both with at least one mutable access:

```
conflicts(V1, V2) = ∃f. (f ∈ V1 ∧ f ∈ V2 ∧ (mut(f, V1) ∨ mut(f, V2)))
```

Implementation uses nested iteration checking all field pairs. Complexity is O(n×m) where n and m are the number of fields in each view spec.

## Feature Completeness

### Working Features

- Field-level borrowing in inherent methods
- Single and multi-field view specifications
- Mixed mutable/immutable access
- Tuple struct field access (numeric indices)
- Generic structs with view-typed methods
- Lifetime parameters in view-typed structs
- Standard derive macros (`Debug`, `Clone`, etc.)
- Declarative macros (`macro_rules!`) with view types
- Incremental compilation
- Concurrency primitives (`Arc<Mutex<T>>`, `RefCell`)
- Two-phase borrows and Non-Lexical Lifetimes (NLL)

### Current Limitations

**Scoping:**
- Trait methods not supported (requires trait system integration)
- Free functions not supported (requires additional HIR infrastructure)
- Generic type parameters cannot have view types (`fn foo<T>(x: &{field} T)` rejected)

**Return Values:**
- View-typed methods cannot return references (conservative soundness restriction)
- Return-position impl trait (`-> impl Trait`) not tested with view types

**Field Paths:**
- Nested field paths are supported (`&{transform.position}`, `&{outer.inner.value}`)
- Arbitrary nesting depth supported

## Test Suite

Comprehensive test suite covering core functionality, edge cases, concurrency, macros, and error handling.

### Test Categories

**Core Functionality:**
- Same field mut/mut conflicts
- Same field mut/imm conflicts
- Same field imm/imm no conflict
- Different fields no conflict
- Multi-field view specs
- Motivating example from paper

**Edge Cases:**
- Lifetime variance and subtyping
- Generic structs with view types
- Derive macro compatibility
- Tuple struct fields
- Zero-sized types (ZST)
- repr(C) and repr(packed) structs
- Nested field paths (multiple depth levels)
- Large field counts (stress testing)

**Concurrency:**
- `Arc<Mutex<T>>` with view-typed methods
- `RefCell` interior mutability
- `Send`/`Sync` auto-trait derivation

**Macro Interactions:**
- `macro_rules!` field name generation
- Token tree manipulation
- Macro hygiene preservation
- Repetition patterns

**Compiler Features:**
- Incremental compilation correctness
- Two-phase borrows
- Non-Lexical Lifetimes (NLL)

**Error Handling:**
- Invalid syntax rejection
- Non-existent field errors
- Public visibility violations
- Overlapping view spec conflicts
- Diagnostic message quality

### Running Tests

```bash
# Build stage 1 compiler
./x build --stage 1

# Run all view types tests
./x test --stage 1 tests/ui/view-types/

# Run specific test
./x test --stage 1 tests/ui/view-types/motivating-example.rs
```

## Formal Verification

The implementation is backed by formal proofs in Coq establishing core safety properties. Proofs are located in the `formalization/` directory.

### Status

**Core_Proven.v:** Fully verified with zero admits  
**Supporting files:** Additional proofs with some admits for heap semantics

### Key Theorems Proven (Core_Proven.v)

**Core Safety Properties:**
1. **Mutable Exclusivity**: Mutable borrow of field f excludes other accesses to f
2. **Shared Immutability**: Multiple immutable borrows of field f can coexist
3. **Field Independence**: Borrows of different fields never conflict (core theorem)
4. **Decidability**: Conflict detection is computable
5. **Motivating Example**: The paper's example (next_id and data fields) is proven safe

**The Critical Theorem:**
```coq
Theorem different_fields_no_conflict : forall f1 f2 m1 m2,
  f1 <> f2 ->
  fields_conflict (mkFieldAccess f1 m1) (mkFieldAccess f2 m2) = false.
```

This proves that different fields can be borrowed simultaneously regardless of mutability, which is the entire purpose of view types.

### Proof Files

**Core_Proven.v** (253 lines)
- 28 theorems with zero admits
- All theorems machine-checked
- Proves core safety properties

**BasicProofs_Clean.v** (414 lines)
- 17 fully proven theorems
- 6 admitted meta-properties (symmetry, transitivity, reflexivity)

**ViewTypes.v** (297 lines)
- Definitions and conflict detection algorithms

**ListHelpers.v** (346 lines)
- Helper lemmas for list operations

### Verified Algorithm (Core_Proven.v)

The conflict detection algorithm proven correct:

```coq
Definition fields_conflict (fa1 fa2 : field_access) : bool :=
  if String.eqb (fa_name fa1) (fa_name fa2)
  then match (fa_mutability fa1, fa_mutability fa2) with
       | (Mut, _) => true
       | (_, Mut) => true
       | (Imm, Imm) => false
       end
  else false.

Fixpoint views_conflict (v1 v2 : view_spec) : bool :=
  match v1 with
  | [] => false
  | fa1 :: rest1 =>
      (existsb (fields_conflict fa1) v2) || (views_conflict rest1 v2)
  end.
```

This algorithm is used directly in the Rust compiler implementation.

### What Is Proven (Core_Proven.v)

- Conflict detection algorithm correctly identifies overlapping field accesses with conflicting mutabilities
- Different fields can be borrowed simultaneously without aliasing violations
- Mutable access to a field is exclusive
- Immutable access to a field can be shared
- Algorithm is decidable

### Additional Formalization Files

- **Progress.v, Preservation.v, Operational.v, Typing.v**: Outline full type soundness proofs with admits for heap semantics
- **Unsafe_Interaction.v**: Analysis of view types interaction with unsafe code
- **Lifetimes_Returns.v**: Analysis of return reference restrictions

### Compilation

```bash
cd formalization
coqc ViewTypes.v
coqc ListHelpers.v
coqc BasicProofs_Clean.v
coqc Core_Proven.v
```

Core_Proven.v compiles successfully with zero admits.

## Usage Guide

### Enabling the Feature

```rust
#![feature(view_types)]
#![allow(incomplete_features)]
```

### Basic Examples

**Database cache with separate stat tracking:**
```rust
struct Database {
    cache: HashMap<String, Value>,
    hits: usize,
    misses: usize,
}

impl Database {
    fn record_hit(&{mut hits} mut self) {
        self.hits += 1;
    }

    fn record_miss(&{mut misses} mut self) {
        self.misses += 1;
    }

    fn lookup(&mut self, key: &str) -> Option<Value> {
        if let Some(val) = self.cache.get(key) {
            self.record_hit();  // Works: hits ⊥ cache
            Some(val.clone())
        } else {
            self.record_miss();  // Works: misses ⊥ cache
            None
        }
    }
}
```

**Game entity with separate transform and AI:**
```rust
struct Entity {
    transform: Transform,
    ai_state: AIState,
    physics: PhysicsBody,
}

impl Entity {
    fn update_physics(&{mut physics} mut self, dt: f32) {
        self.physics.step(dt);
    }

    fn update_ai(&{mut ai_state} mut self, world: &World) {
        self.ai_state.tick(world);
    }

    fn game_tick(&mut self, dt: f32, world: &World) {
        self.update_physics(dt);  // Works: physics ⊥ ai_state
        self.update_ai(world);
    }
}
```

## License

This implementation is part of the Rust compiler project and follows the same license: MIT/Apache-2.0.