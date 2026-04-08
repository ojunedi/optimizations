use common::*;
use std::collections::HashSet;

/* ----------------------------- Error Handling ----------------------------- */

#[repr(u64)]
#[allow(unused)]
pub enum SnakeErr {
    ArithmeticOverflow = 0,
    ExpectedNum = 1,
    ExpectedBool = 2,
    ExpectedArray = 3,
    NegativeLength = 4,
    IndexOutOfBounds = 5,
}

#[export_name = "\u{1}snake_error"]
pub extern "C" fn snake_error(ecode: SnakeErr, v: SnakeValue) -> SnakeValue {
    match ecode {
        SnakeErr::ArithmeticOverflow => eprintln!("arithmetic operation overflowed"),
        SnakeErr::ExpectedNum => eprintln!("expected a number, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedBool => eprintln!("expected a boolean, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedArray => eprintln!("expected an array, got {}", sprint_snake_val(v)),
        SnakeErr::NegativeLength => eprintln!("length {} is negative", sprint_snake_val(v)),
        SnakeErr::IndexOutOfBounds => eprintln!("index {} out of bounds", sprint_snake_val(v)),
    }
    std::process::exit(1)
}

/* ---------------------------- Print Snake Value --------------------------- */

fn sprint_snake_val_loop(v: SnakeValue, buf: &mut String, mut parents: HashSet<*const u64>) {
    if v.0 & INT_MASK == INT_TAG {
        // it's a signed 63-bit integer
        buf.push_str(&format!("{}", unsigned_to_signed(v.0) >> 1))
    } else if v.0 & FULL_MASK == ARRAY_TAG {
        // array
        let addr = (v.0 - ARRAY_TAG) as *const u64;
        if parents.contains(&addr) {
            // print a <loop> tag if we've already seen this array pointer
            buf.push_str("<loop>");
        } else {
            parents.insert(addr);
            let arr = load_snake_array(addr);
            let mut p = arr.elts;
            buf.push_str("[");
            if arr.size != 0 {
                // don't prepend a comma for the first element
                unsafe {
                    sprint_snake_val_loop(*p, buf, parents.clone());
                    p = p.add(1);
                }

                for _ in 1..arr.size {
                    buf.push_str(", ");
                    unsafe {
                        sprint_snake_val_loop(*p, buf, parents.clone());
                        p = p.add(1);
                    }
                }
            }
            buf.push_str("]");
        }
    } else if v == SNAKE_TRU {
        buf.push_str("true")
    } else if v == SNAKE_FLS {
        buf.push_str("false")
    } else {
        buf.push_str(&format!("(Invalid snake value 0x{:x})", v.0));
    }
}

/* Implement the following function for printing a snake value.
**/
pub fn sprint_snake_val(x: SnakeValue) -> String {
    let mut buf = String::new();
    sprint_snake_val_loop(x, &mut buf, HashSet::new());
    buf
}
