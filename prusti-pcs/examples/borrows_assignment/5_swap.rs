extern crate prusti_contracts;
use prusti_contracts::*;

struct K {d: u32}

#[pure]
fn main() {
    let mut x = &mut K {d: 0};
    let mut y = &mut K {d: 0};
    let tmp = x;
    x = y;
    y = tmp;
    let _ = x;
    let _ = y;
}