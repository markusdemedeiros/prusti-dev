extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}


#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    x = K {kd: 5};
}
