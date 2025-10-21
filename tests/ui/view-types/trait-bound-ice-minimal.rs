#![feature(view_types)]
#![allow(incomplete_features)]

// Minimal reproduction: Generic function with trait bound calling view-typed trait method
// RESTRICTION: View types are not supported on trait methods - should error clearly, not ICE

trait Update {
    fn update(&{mut value} mut self); //~ ERROR patterns aren't allowed in functions without bodies
    //~| WARN this was previously accepted by the compiler but is being phased out
}

struct Data {
    value: i32,
    other: String,
}

impl Update for Data {
    fn update(&{mut value} mut self) { //~ ERROR view types are not supported on trait method implementations
        self.value += 1;
    }
}

// ICE occurs here: generic function with trait bound
fn use_trait<T: Update>(item: &mut T) {
    item.update();  // Calling trait method with view type through generic
}

fn main() {
    let mut data = Data {
        value: 0,
        other: String::new(),
    };

    use_trait(&mut data);

    println!("Value: {}", data.value);
}
