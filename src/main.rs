//! Implementation of Bulletproofs++ in rust

mod norm_arg;
mod rangeproof;

pub use rangeproof::{Proof, Prover, Verifier, commit};
use norm_arg::log;

fn main() {
    norm_arg::tester(64, 64);
}