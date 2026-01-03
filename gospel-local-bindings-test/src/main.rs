#![feature(ptr_metadata)]
#![feature(allocator_api)]
#![feature(clone_to_uninit)]
#![feature(ptr_as_ref_unchecked)]

use std::alloc::{Global};
use std::mem::MaybeUninit;
use std::path::PathBuf;
use std::ptr::null;
use std::str::FromStr;
use gospel_runtime::local_type_model::{allocate_default, allocate_zeroed, enable_dynamic_code_backtraces, static_cast_mut_checked, ImplicitPtrMetadata, PlatformWideChar};
use gospel_runtime::vm_integration::{GospelVMTypeGraphBackend, GospelVMTypeUniverse};
use gospel_typelib::compiled_target_triplet;
use gospel_vm::vm::GospelVMOptions;
use crate::gospel_bindings::{EClassCastFlags, EPropertyPointerType, FIntVector, FString, TArray, TSizedHeapAllocator, UClass, UField, UObject};

include!(concat!(env!("OUT_DIR"), "/", "gospel_bindings.rs"));

#[repr(C)]
struct FNameLayout {
    value: u32,
    number: u32,
}

#[repr(C)]
struct FStringLayout {
    data_ptr: *mut PlatformWideChar,
    array_num: i32,
    array_max: i32,
}

#[repr(C)]
struct TestUObjectVTableLayout {
    destructor: unsafe extern "C" fn(*mut TestUObjectLayout),
    register_dependencies: unsafe extern "C" fn(*mut TestUObjectLayout),
    deferred_register: unsafe extern "C" fn(*mut TestUObjectLayout, *const TestUObjectLayout, *const PlatformWideChar, *const PlatformWideChar),
    get_f_name_for_stat_id: unsafe extern "C" fn(*const TestUObjectLayout, *mut FNameLayout) -> *mut FNameLayout,
    can_be_cluster_root: unsafe extern "C" fn(*const TestUObjectLayout) -> bool,
    export_text_internal: unsafe extern "C" fn(*const TestUObjectLayout, *mut FStringLayout, *const u8, i32, *const u8, *mut TestUObjectLayout, i32, *mut TestUObjectLayout),
}

unsafe extern "C" fn u_object_destructor_impl(_object: *mut TestUObjectLayout) {
}
unsafe extern "C" fn u_object_register_dependencies_impl(object: *mut TestUObjectLayout) {
    unsafe { assert_eq!(object.as_ref_unchecked().name_private.value, 49); }
}
unsafe extern "C" fn u_object_deferred_register_impl(object: *mut TestUObjectLayout, static_class: *const TestUObjectLayout, package_name: *const PlatformWideChar, class_name: *const PlatformWideChar) {
    unsafe { assert_eq!(object.as_ref_unchecked().name_private.value, 49); }
    assert_eq!(static_class.addr(), 133);
    assert_eq!(package_name.addr(), 789);
    assert_eq!(class_name.addr(), 800);
}
unsafe extern "C" fn u_object_get_f_name_for_stat_id_impl(object: *const TestUObjectLayout, return_value_storage: *mut FNameLayout) -> *mut FNameLayout {
    unsafe { assert_eq!(object.as_ref_unchecked().name_private.value, 49); }
    let return_value = unsafe { (return_value_storage as *mut MaybeUninit<FNameLayout>).as_mut_unchecked() };
    unsafe { return_value.write(FNameLayout{value: object.as_ref_unchecked().name_private.value, number: 7777}); }
    return_value_storage
}
unsafe extern "C" fn u_object_can_be_cluster_root_impl(object: *const TestUObjectLayout) -> bool {
    unsafe { assert_eq!(object.as_ref_unchecked().name_private.value, 49); }
    true
}
unsafe extern "C" fn u_object_export_text_internal(object: *const TestUObjectLayout, result_str: *mut FStringLayout, property_value: *const u8, pointer_type: i32, default_value: *const u8, parent_object: *mut TestUObjectLayout, port_flags: i32, export_scope: *mut TestUObjectLayout) {
    unsafe { assert_eq!(object.as_ref_unchecked().name_private.value, 49); }
    assert_eq!(property_value.addr(), 0);
    assert_eq!(pointer_type, 1);
    assert_eq!(default_value.addr(), 889);
    assert_eq!(parent_object.addr(), 0);
    assert_eq!(port_flags, 24);
    assert_eq!(export_scope.addr(), 900);
    unsafe { result_str.as_mut_unchecked().array_num = 133; }

    let stack_backtrace = std::backtrace::Backtrace::force_capture().to_string();
    assert!(stack_backtrace.contains("unreal:unreal::UObject::ExportText_Internal"));
}

impl TestUObjectVTableLayout {
    fn static_get_object_vtable() -> *const TestUObjectVTableLayout {
        static VTABLE_OBJECT: TestUObjectVTableLayout = TestUObjectVTableLayout{
            destructor: u_object_destructor_impl,
            register_dependencies: u_object_register_dependencies_impl,
            deferred_register: u_object_deferred_register_impl,
            get_f_name_for_stat_id: u_object_get_f_name_for_stat_id_impl,
            can_be_cluster_root: u_object_can_be_cluster_root_impl,
            export_text_internal: u_object_export_text_internal,
        };
        &VTABLE_OBJECT as *const TestUObjectVTableLayout
    }
}

#[repr(C)]
struct TestUObjectLayout {
    vtable: *const TestUObjectVTableLayout,
    object_flags: u32,
    internal_index: i32,
    class_private: *const TestUObjectLayout,
    name_private: FNameLayout,
    outer_private: *const TestUObjectLayout,
}
#[repr(C)]
struct TestUFieldLayout {
    baseclass_0: TestUObjectLayout,
    next: *const TestUFieldLayout,
}

fn main() -> anyhow::Result<()> {
    enable_dynamic_code_backtraces();

    let module_path = PathBuf::from_str(env!("CARGO_MANIFEST_DIR"))?.join("res/gospel/unreal");

    let vm_options = GospelVMOptions::default().target_triplet(compiled_target_triplet().unwrap()).with_global("UE_VERSION", 504);
    let type_graph_backend = GospelVMTypeGraphBackend::create_from_module_tree(&module_path, &Vec::new(), vm_options)?;
    GospelVMTypeUniverse::set_type_graph_backend(type_graph_backend);

    let mut test_field = TestUFieldLayout{baseclass_0: TestUObjectLayout{vtable: TestUObjectVTableLayout::static_get_object_vtable(),
        object_flags: 1, internal_index: 50, class_private: null(), name_private: FNameLayout{value: 49, number: 5}, outer_private: null()}, next: null()};

    let field_ref = unsafe { UField::from_raw_ptr_mut(&mut test_field as *mut TestUFieldLayout).as_mut_unchecked() };
    // TODO: Generate a type-level static_cast and static_cast_checked function that automatically picks implied type universe
    let object_ref = static_cast_mut_checked::<UField, UObject, GospelVMTypeUniverse>(field_ref);
    let object_internal_index = *object_ref.internal_index();
    assert_eq!(test_field.baseclass_0.internal_index, object_internal_index);

    object_ref.register_dependencies();
    object_ref.deferred_register(UClass::from_raw_ptr_mut(std::ptr::without_provenance_mut::<u8>(133)), std::ptr::without_provenance(789), std::ptr::without_provenance(800));
    assert_eq!(*object_ref.get_f_name_for_stat_id(Global).number().unwrap(), 7777);
    assert_eq!(object_ref.can_be_cluster_root(), true);

    let mut result_str = unsafe { Box::from_non_null_in(allocate_zeroed::<FString, Global>(&Global), Global) };
    object_ref.export_text_internal(result_str.as_mut(), null(), EPropertyPointerType::container(),
        std::ptr::without_provenance_mut(889), UObject::null_mut_ptr(), 24, UObject::from_raw_ptr_mut(std::ptr::without_provenance_mut::<u8>(900)));
    assert_eq!(*static_cast_mut_checked::<FString, TArray<PlatformWideChar, TSizedHeapAllocator<i32>>, GospelVMTypeUniverse>(result_str.as_mut()).array_num().static_cast::<i32>().unwrap(), 133);

    let class_cast_flags = EClassCastFlags::a_player_controller();
    assert_eq!(class_cast_flags, EClassCastFlags::sized_from_raw_discriminant(0x0000002000000000u64));
    assert_eq!(*allocate_default::<FIntVector, Global>(Global).x(), 0);
    Ok({})
}
