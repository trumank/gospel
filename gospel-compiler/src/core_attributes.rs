use crate::backend::CompilerFunctionDeclaration;

fn is_explicitly_trivial(declaration: &CompilerFunctionDeclaration) -> bool {
    declaration.metadata.contains_key("trivial_class")
}

pub fn is_trivially_constructible(declaration: &CompilerFunctionDeclaration) -> bool {
    is_explicitly_trivial(declaration) || declaration.metadata.contains_key("zero_constructible")
}

pub fn is_trivially_copyable(declaration: &CompilerFunctionDeclaration) -> bool {
    is_explicitly_trivial(declaration) || declaration.metadata.contains_key("bitwise_copyable")
}

pub fn is_trivially_destructible(declaration: &CompilerFunctionDeclaration) -> bool {
    is_explicitly_trivial(declaration) || declaration.metadata.contains_key("no_destructor")
}

pub fn is_trivial_class(declaration: &CompilerFunctionDeclaration) -> bool {
    is_trivially_constructible(declaration) && is_trivially_copyable(declaration) && is_trivially_destructible(declaration)
}
