use std::rc::Rc;
use crate::container::GospelContainer;

struct GospelTypeLocator {
    container_index: usize,
    type_name_index: usize,
    type_index: usize,

}

pub struct GospelVMState {
    loaded_containers: Vec<Rc<GospelContainer>>,

}

impl GospelVMState {

}