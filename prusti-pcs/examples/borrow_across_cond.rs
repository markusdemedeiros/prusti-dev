extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}

struct S {
    s1: K,
    s2: T,
}

struct T {
    td: K,
}



#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    let mut y: K = K {kd: 5};
    
    let mut s: S = S {s1: x, s2: T { td: y } };
    let z = &mut s.s2;
    if true {
        let w = 12;
    }
    let a = z;
}
