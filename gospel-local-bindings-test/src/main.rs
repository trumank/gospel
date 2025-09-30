#![feature(ptr_metadata)]
#![feature(allocator_api)]
#![feature(clone_to_uninit)]
#![feature(ptr_as_ref_unchecked)]

use std::path::PathBuf;
use std::ptr::null;
use std::str::FromStr;
use gospel_runtime::local_type_model::{static_cast_checked, ImplicitPtrMetadata};
use gospel_runtime::vm_integration::{GospelVMTypeGraphBackend, GospelVMTypeUniverse};
use gospel_typelib::compiled_target_triplet;
use gospel_vm::vm::GospelVMOptions;
use crate::gospel_bindings::{EClassCastFlags, UField, UObject};

include!(concat!(env!("OUT_DIR"), "/", "gospel_bindings.rs"));

#[repr(C)]
struct TestUObjectLayout {
    vtable: u64,
    object_flags: u32,
    internal_index: i32,
    class_private: *const TestUObjectLayout,
    name_private: u64,
    outer_private: *const TestUObjectLayout,
}
#[repr(C)]
struct TestUFieldLayout {
    baseclass_0: TestUObjectLayout,
    next: *const TestUFieldLayout,
}

fn main() -> anyhow::Result<()> {
    let module_path = PathBuf::from_str(env!("CARGO_MANIFEST_DIR"))?.join("res/gospel/unreal");

    let vm_options = GospelVMOptions::default().target_triplet(compiled_target_triplet().unwrap()).with_global("UE_VERSION", 504);
    let type_graph_backend = GospelVMTypeGraphBackend::create_from_module_tree(&module_path, &Vec::new(), vm_options)?;
    GospelVMTypeUniverse::set_type_graph_backend(type_graph_backend);

    let test_field = TestUFieldLayout{baseclass_0: TestUObjectLayout{vtable: 0, object_flags: 1, internal_index: 50, class_private: null(), name_private: 0, outer_private: null()}, next: null()};

    let field_ref = unsafe { UField::from_raw_ptr(&test_field as *const TestUFieldLayout).as_ref_unchecked() };
    // TODO: Generate a type-level static_cast and static_cast_checked function that automatically picks implied type universe
    let object_ref = static_cast_checked::<UField, UObject, GospelVMTypeUniverse>(field_ref);
    let object_internal_index = *object_ref.internal_index();
    assert_eq!(test_field.baseclass_0.internal_index, object_internal_index);

    let class_cast_flags = EClassCastFlags::a_player_controller();
    assert_eq!(class_cast_flags, EClassCastFlags::sized_from_raw_discriminant(0x0000002000000000u64));

    Ok({})
}
