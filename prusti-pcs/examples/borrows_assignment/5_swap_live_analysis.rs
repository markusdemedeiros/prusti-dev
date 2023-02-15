struct K {d: u32}

#[analyzer::run]
fn main() {
    let mut x = &mut K {d: 0};  // _1 = x, _2 = K {..}
    let mut y = &mut K {d: 0};  // _3 = y, _4 = K {..}
    let tmp = x;                // _5 = tmp
    x = y;                      // _6 = reborrow of y (temporary thing)
    y = tmp;                    // _7 = reborrow of tmp (temporary thing)
    let bx = x;
    let by = y;
}
