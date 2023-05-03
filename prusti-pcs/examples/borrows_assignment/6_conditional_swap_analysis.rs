struct T {}

#[analyzer::run]
fn swap(mut t0: T, mut t1: T, b: bool) {
    let mut x = &mut t0;
    let mut y = &mut t1;
    if b {
        let tmp = x;
        x = y;
        y = tmp;
    }
    let test_x = x;
    let test_y = y;
}



fn main() {
}


