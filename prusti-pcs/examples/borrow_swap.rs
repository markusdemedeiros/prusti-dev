extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}


#[pure]
fn main() {
    let mut x: K = K {kd: 4};   // _1
    let mut y: K = K {kd: 5};   // _2
    
    let mut bx = &mut x;        // _3
    let mut by = &mut y;        // _4

    let tmp = bx;               // _5
 
    bx = by;                    // _6 = &mut *_4, _3 = 6,
                                // _5 --* _1
                                // _4 --* _2
                                // _3 --* (*_4)

    by = tmp;                   // _7 = &mut *_5;  _4 = ? 

    // u _4 should be regained at some point and the values in the DAG should
    // be tagged. When?

    let lx = bx;
    let ly = by;
    
}
