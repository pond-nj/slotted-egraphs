use std::sync::{RwLock, RwLockWriteGuard};

struct SomeStruct {
    field: u32,
}

struct S {
    field: SomeStruct,
}

impl S {
    fn get_mut_field(&mut self) -> &mut SomeStruct {
        &mut self.field
    }
}

// Wrapper that owns the RwLock
pub struct Handle {
    inner: RwLock<S>,
}

impl Handle {
    pub fn write_field(&self) -> S::WriteFieldGuard<'_> {
        S::WriteFieldGuard {
            guard: self.inner.write().unwrap(),
        }
    }
}

// Wrapper that holds the guard and exposes the field

impl<'a> WriteFieldGuard<'a> {
    pub fn field(&mut self) -> &mut SomeStruct {
        &mut self.guard.field
    }
}
