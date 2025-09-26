use gospel_typelib::compiled_target_triplet;
use gospel_typelib::target_triplet::BitWidth;

fn main() {
    let target_triplet = compiled_target_triplet().unwrap_or_else(|| panic!("Current platform not supported for local type model"));

    let wide_char_size = match target_triplet.wide_char_size() {
        BitWidth::Width16 => "2",
        BitWidth::Width32 => "4",
        _ => { panic!("Unexpected wide char size for target triplet"); }
    };
    println!("cargo::rustc-check-cfg=cfg(platform_wide_char_size, values(\"2\", \"4\"))");
    println!("cargo::rustc-cfg=platform_wide_char_size=\"{}\"", wide_char_size);

    let long_size = match target_triplet.long_size() {
        BitWidth::Width32 => "4",
        BitWidth::Width64 => "8",
        _ => { panic!("Unexpected long size for target triplet"); }
    };
    println!("cargo::rustc-check-cfg=cfg(platform_long_size, values(\"4\", \"8\"))");
    println!("cargo::rustc-cfg=platform_long_size=\"{}\"", long_size);
}
