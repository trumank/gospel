use std::env;
use std::fs::write;
use std::path::PathBuf;
use proc_macro2::TokenStream;
use quote::quote;

// We need the target triplet definition from the typelib module to parse the TARGET environment variable
pub mod target_triplet {
    include!("src/target_triplet.rs");
}
use crate::target_triplet::{TargetTriplet};

fn convert_target_triplet(target_triplet_str: &str) -> TokenStream {
    let target_triplet: TargetTriplet = if let Some(x) = TargetTriplet::parse(target_triplet_str) {
        x
    } else { return quote!{ None }; };

    let arch_as_u8 = target_triplet.arch as u8;
    let sys_as_u8 = target_triplet.sys as u8;
    let env = if target_triplet.env.is_some() {
        let env_as_u8 = target_triplet.env.map(|x| x as u8);
        quote!{ Some(std::mem::transmute(#env_as_u8)) }
    } else { quote!{ None } };

    quote!{ Some(unsafe{ TargetTriplet{arch: std::mem::transmute(#arch_as_u8), sys: std::mem::transmute(#sys_as_u8), env: #env} }) }
}

fn main() {
    let compiled_target_triplet = env::var("TARGET").unwrap();
    let converted_target_triplet = convert_target_triplet(&compiled_target_triplet);

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let file_path = out_dir.join("compiled_target_triplet.in");

    write(file_path, converted_target_triplet.to_string().as_bytes()).unwrap();
}