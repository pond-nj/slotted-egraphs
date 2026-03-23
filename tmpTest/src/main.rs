use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let counter = RefCell::new(1usize);

    // owner 1
    {
        let mut n = counter.borrow_mut();
        *n += 1;
    }

    // owner 2
    {
        let mut n = counter.borrow_mut();
        *n += 2;
    }

    println!("counter = {}", counter.borrow()); // 3
    println!("c1 counter = {}", counter.borrow()); // 3
    println!("c2 counter = {}", counter.borrow()); // 3
}
