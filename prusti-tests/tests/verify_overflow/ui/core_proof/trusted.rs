// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

#[trusted]
struct TrustedBox {
    value: u32,
}

impl TrustedBox {
    #[trusted]
    fn new(value: u32) -> Self {
        Self {
            value
        }
    }
}

fn test1() {
    let a = TrustedBox::new(1);
    let _b = a.value;   //~ ERROR: Accessing fields of a trusted type.
}

#[trusted]
struct GenericTrustedBox<T> {
    value: T,
}

impl<T> GenericTrustedBox<T> {
    #[trusted]
    fn new(value: T) -> Self {
        Self {
            value
        }
    }
}

fn test2() {
    let a = GenericTrustedBox::new(1);
    let _b = a.value;   //~ ERROR: Accessing fields of a trusted type.
}

struct JustBox {
    value: u32,
}

impl JustBox {
    #[trusted]
    fn new(value: u32) -> Self {
        Self {
            value
        }
    }
}

fn test3() {
    let a = JustBox::new(4);
    let _b = a.value;
}

fn main() {}
