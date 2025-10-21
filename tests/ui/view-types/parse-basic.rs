//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

struct S {
    a: u32,
    b: String,
    c: Vec<i32>,
}

// Test basic view type syntax
impl S {
    fn test1(&{mut a} self) {}
    fn test2(&{a, b} self) {}
    fn test3(&{mut a, mut b, c} mut self) {}

    // Test with lifetime
    fn test4<'a>(&'a {mut a} self) {}
}

fn main() {}
