#![feature(arbitrary_self_types)]

use std::ops::Deref;
use std::path::PathBuf;
use std::ptr::null;
use std::str::FromStr;
use std::sync::Arc;
use gospel_runtime::current_process::CurrentProcessMemory;
use gospel_runtime::external_memory::OpaquePtr;
use gospel_runtime::external_type_model::{MemoryAndTypeNamespace, Ptr};
use gospel_runtime::vm_integration::{GospelVMTypeGraphBackend, GospelVMTypeNamespace};
use gospel_typelib::type_model::TargetTriplet;
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
type M = MemoryAndTypeNamespace<CurrentProcessMemory, GospelVMTypeNamespace>;

fn main() -> anyhow::Result<()> {
    let module_path = PathBuf::from_str(env!("CARGO_MANIFEST_DIR"))?.join("res/gospel/unreal");

    let vm_options = GospelVMOptions::default().target_triplet(TargetTriplet::current_target().unwrap()).with_global("UE_VERSION", 504);
    let type_graph_backend = GospelVMTypeGraphBackend::create_from_module_tree(&module_path, &Vec::new(), vm_options)?;
    let current_process_memory =  Arc::new(M{memory: CurrentProcessMemory{}, namespace: type_graph_backend.to_type_ptr_namespace()});

    let test_field = TestUFieldLayout{baseclass_0: TestUObjectLayout{vtable: 0, object_flags: 1, internal_index: 50, class_private: null(), name_private: 0, outer_private: null()}, next: null()};
    let test_field_address = (&test_field as *const TestUFieldLayout) as u64;
    let opaque_field_ptr = OpaquePtr{memory: current_process_memory.clone(), address: test_field_address};

    let field_ptr = Ptr::<M, UField>::from_raw_ptr(opaque_field_ptr.clone()).to_ref_checked();
    let object_ptr = field_ptr.cast_checked::<UObject>();
    let object_internal_index = UObject::internal_index(&object_ptr).read()?;
    assert_eq!(test_field.baseclass_0.internal_index, object_internal_index);

    let class_cast_flags = EClassCastFlags::a_player_controller(current_process_memory.deref());
    assert_eq!(class_cast_flags, EClassCastFlags(0x0000002000000000u64));

    Ok({})
}
