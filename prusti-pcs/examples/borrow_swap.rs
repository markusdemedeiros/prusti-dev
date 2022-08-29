extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}


#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    let mut y: K = K {kd: 5};
    
    let mut bx = &mut x;
    let mut by = &mut y;

    let tmp = bx;
    bx = by;
    by = tmp;

    let lx = bx;
    let ly = by;
    
}
