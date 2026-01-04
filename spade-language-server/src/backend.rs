use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use camino::Utf8PathBuf;
use spade_common::name::NameID;
use spade_diagnostics::CodeBundle;
use spade_hir::query::QueryCache;
use spade_hir::symbol_table::FrozenSymtab;
use spade_hir::ItemList;
use spade_typeinference::traits::TraitImplList;
use spade_typeinference::TypeState;
use tokio::sync::mpsc;
use tower_lsp::lsp_types::MessageType;

pub struct ServerBackend {
    /// The root folder that is opened in the client.
    pub root_dir: Arc<Mutex<Option<Utf8PathBuf>>>,

    /// Syntax tree and assorted datastructures used to find information regarding the program.
    pub symtab: Arc<Mutex<Option<FrozenSymtab>>>,
    pub item_list: Arc<Mutex<ItemList>>,
    pub type_states: Arc<Mutex<BTreeMap<NameID, TypeState>>>,
    pub trait_impls: Arc<Mutex<TraitImplList>>,
    pub code: Arc<Mutex<CodeBundle>>,
    pub query_cache: Arc<Mutex<QueryCache>>,
    // Note: Try using two copies of code again to make functionality work(better) even when the parser bails early.
    pub _old_code: Arc<Mutex<CodeBundle>>,

    /// A channel allowing for logging without requiring an async context or handle to the client.
    pub client_log_chan: mpsc::Sender<(MessageType, String)>,
}

impl ServerBackend {
    pub fn new(sender: mpsc::Sender<(MessageType, String)>) -> Self {
        Self {
            root_dir: Arc::new(Mutex::new(None)),
            symtab: Arc::new(Mutex::new(None)),
            item_list: Arc::new(Mutex::new(ItemList::new())),
            trait_impls: Arc::new(Mutex::new(TraitImplList::new())),
            code: Arc::new(Mutex::new(CodeBundle::new(String::new()))),
            query_cache: Arc::new(Mutex::new(QueryCache::empty())),
            _old_code: Arc::new(Mutex::new(CodeBundle::new(String::new()))),
            type_states: Arc::new(Mutex::new(BTreeMap::new())),
            client_log_chan: sender,
        }
    }
}
