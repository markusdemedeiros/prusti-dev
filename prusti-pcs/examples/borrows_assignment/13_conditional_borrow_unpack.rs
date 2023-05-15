struct T {}

#[analyzer::run]
fn test(b: bool) {
    let mut t0 = T{};
    let mut t1 = T{};

    // I have to do this, since the coupling graph doesn't support type ascriptions yet :/ 
    let mut t2 = T{};
    let mut x = &mut t2;

    if b {
        x = &mut t0;
    } else {
        x = &mut t1;
    }

    let test_x = x;
    let test_t0 = t0;
    let test_t1 = t1;
}



fn main() {
}


