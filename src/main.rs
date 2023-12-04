#![feature(impl_trait_in_fn_trait_return)]

pub use executions::*;

mod executions;
mod fenwick;
mod iter;
mod relations;

fn main() {
    println!("Hello, world!");
}
