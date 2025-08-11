use serde::{Deserialize, Serialize};

macro_rules! def_id_tracker {
    ($name:ident) => {
        #[derive(Debug, Serialize, Deserialize)]
        pub struct $name {
            id: u64,
        }

        impl $name {
            pub fn new() -> Self {
                Self { id: 0 }
            }

            pub fn new_at(id: u64) -> Self {
                Self { id }
            }

            pub fn next(&mut self) -> u64 {
                let result = self.id;
                self.id += 1;
                result
            }

            pub fn peek(&self) -> u64 {
                self.id
            }

            /// Clone this ID tracker. After this is done, only one of the ID trackers may
            /// be used otherwise duplicate IDs will be generated. It is up to the caller of this
            /// method to make sure that no mutable references are handed out to one of the clonse
            pub fn make_clone(&self) -> Self {
                Self { id: self.id }
            }
        }
        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

macro_rules! def_typed_id_tracker {
    ($name:ident, $type_name:ident) => {
        #[derive(Debug, Serialize, Deserialize)]
        pub struct $name {
            id: u64,
        }

        impl $name {
            pub fn new() -> Self {
                Self { id: 0 }
            }

            pub fn new_at(id: u64) -> Self {
                Self { id }
            }

            pub fn next(&mut self) -> $type_name {
                let result = self.id;
                self.id += 1;
                $type_name(result)
            }

            pub fn peek(&self) -> u64 {
                self.id
            }

            /// Clone this ID tracker. After this is done, only one of the ID trackers may
            /// be used otherwise duplicate IDs will be generated. It is up to the caller of this
            /// method to make sure that no mutable references are handed out to one of the clonse
            pub fn make_clone(&self) -> Self {
                Self { id: self.id }
            }
        }
        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

pub struct NameIdInner(pub u64);

/// An ID of an expression-like thing. In practice something that has a type in the
/// type inferer.
#[derive(Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy, Serialize, Deserialize, Debug)]
pub struct ExprID(pub u64);

#[derive(Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy, Serialize, Deserialize, Debug)]
pub struct ImplID(pub u64);

def_typed_id_tracker!(ExprIdTracker, ExprID);
def_typed_id_tracker!(ImplIdTracker, ImplID);
def_id_tracker!(NameIdTracker);
def_id_tracker!(AAVarTracker);
