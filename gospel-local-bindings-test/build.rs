use gospel_bindings_gen::build_rs_generate_bindings;

fn main() {
    build_rs_generate_bindings("unreal", gospel_bindings_gen::ModuleBindingsType::Local);
}
