//! Implementation of Bulletproofs++ in rust

mod norm_arg;
mod rangeproof;

fn main() {
    norm_arg::tester(64, 64);
}