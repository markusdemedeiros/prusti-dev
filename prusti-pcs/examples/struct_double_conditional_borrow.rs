extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

struct S {t1: T, t2: T}


#[pure]
fn main() {
    let mut s = S {t1: T {}, t2: T {}};

    let mut b: &mut T;
    
    if true {
        // Partially drop all fields of the struct 
        b = &mut s.t1;
    } else {
        b = &mut s.t2;
    }

    let w = b;
    let v = s;
}
