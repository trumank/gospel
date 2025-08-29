use std::env::current_dir;
use std::path::PathBuf;
use std::ptr::null;
use std::str::FromStr;
use std::sync::Arc;
use gospel_runtime::current_process::CurrentProcessMemory;
use gospel_runtime::memory_access::OpaquePtr;
use gospel_runtime::static_type_wrappers::StaticallyTypedPtr;
use gospel_runtime::vm_integration::GospelVMTypeGraphBackend;
use gospel_typelib::type_model::TargetTriplet;
use gospel_vm::vm::GospelVMOptions;
use crate::gospel_bindings::{UObject};

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

fn main() -> anyhow::Result<()> {
    let current_process_memory = Arc::new(CurrentProcessMemory{});
    let module_path = PathBuf::from_str(env!("CARGO_MANIFEST_DIR"))?.join("res/gospel/unreal");

    let vm_options = GospelVMOptions::default().target_triplet(TargetTriplet::current_target().unwrap()).with_global("UE_VERSION", 504);
    let type_namespace = GospelVMTypeGraphBackend::create_from_module_tree(&module_path, &Vec::new(), vm_options)?.to_type_ptr_namespace()?;

    let test_object = TestUObjectLayout{vtable: 0, object_flags: 1, internal_index: 50, class_private: null(), name_private: 0, outer_private: null()};
    let test_object_address = (&test_object as *const TestUObjectLayout) as u64;
    let opaque_object_ptr = OpaquePtr{memory: current_process_memory, address: test_object_address};

    let object_ptr = UObject::from_raw_ptr(opaque_object_ptr, &type_namespace)?;
    let object_internal_index = object_ptr.internal_index()?.read()?;
    assert_eq!(test_object.internal_index, object_internal_index);
    Ok({})
}
