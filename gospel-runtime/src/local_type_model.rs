use std::sync::{Mutex, RwLock};
use gospel_typelib::type_model::{MutableTypeGraph, TargetTriplet};
use crate::core_type_definitions::StaticTypeLayoutCache;

/// Returns the target triplet for which this module has been compiled
pub fn native_target_triplet() -> TargetTriplet {
    TargetTriplet::current_target().unwrap()
}

/// Type universe represents a contained type graph
pub trait TypeUniverse {
    fn target_triplet() -> TargetTriplet;
    fn type_graph() -> &'static RwLock<dyn MutableTypeGraph>;
    fn type_layout_cache() -> &'static Mutex<StaticTypeLayoutCache>;
}
