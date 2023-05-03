struct Tree { data: u32, left: Option<Box<Tree>>, right: Option<Box<Tree>>}

// fixme: this example

#[analyzer::run]
fn test(mut t: Tree, target: u32)
{
    // goal: make b borrow the closest node to target
    let mut b = &mut t;
        
    loop {
        if b.data == target {
            break;
        } else if b.data > target {
            if let Some(left_tree) = &mut b.left {
                b = &mut (*left_tree);
                continue;
            } else {
                break;
            }
        }
    }
}


fn main() { }
