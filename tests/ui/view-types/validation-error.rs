//@ edition:2021
#![feature(view_types)]
#![allow(incomplete_features)]

// Test that view type validation correctly catches violations

struct S {
    field_a: u32,
    field_b: String,
    field_c: Vec<i32>,
}

impl S {
    // Valid: only accesses field_a which is in the view
    fn valid(&{mut field_a} mut self) {
        self.field_a = 42;
    }

    // Invalid: tries to access field_b which is not in the view
    fn invalid_access_b(&{mut field_a} mut self) {
        self.field_b = String::from("hello"); //~ ERROR cannot access field `field_b`
    }

    // Invalid: tries to access field_c which is not in the view
    fn invalid_access_c(&{mut field_a} mut self) {
        self.field_c.push(1); //~ ERROR cannot access field `field_c`
    }

    // Valid: can access multiple fields if they're all in the view
    fn valid_multiple(&{mut field_a, mut field_b} mut self) {
        self.field_a = 10;
        self.field_b = String::from("world");
    }

    // Invalid: tries to access field_c which is not in this view
    fn invalid_multiple(&{mut field_a, mut field_b} mut self) {
        self.field_a = 10;
        self.field_b = String::from("world");
        self.field_c.push(2); //~ ERROR cannot access field `field_c`
    }

    // Valid: immutable access to field_a
    fn valid_immutable(&{field_a} self) -> u32 {
        self.field_a
    }

    // Invalid: tries to access field_b immutably
    fn invalid_immutable(&{field_a} self) -> String {
        self.field_b.clone() //~ ERROR cannot access field `field_b`
    }
}

fn main() {}
