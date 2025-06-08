use crate::keywords;
use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, RwLock};

use camino::Utf8PathBuf;
use spade_common::name::NameID;
use spade_diagnostics::CodeBundle;
use spade_hir::query::QueryCache;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::ItemList;
use spade_typeinference::traits::TraitImplList;
use spade_typeinference::TypeState;
use tokio::sync::mpsc;
use tower_lsp::lsp_types::{CompletionItem, MessageType};

pub struct ServerBackend {
    /// The root folder that is opened in the client.
    pub root_dir: Arc<Mutex<Option<Utf8PathBuf>>>,

    /// Syntax tree and assorted datastructures used to find information regarding the program.
    pub symtab: Arc<Mutex<Option<SymbolTable>>>,
    pub item_list: Arc<Mutex<ItemList>>,
    pub type_states: Arc<Mutex<BTreeMap<NameID, TypeState>>>,
    pub trait_impls: Arc<Mutex<TraitImplList>>,
    pub code: Arc<Mutex<CodeBundle>>,
    pub query_cache: Arc<Mutex<QueryCache>>,
    // Note: Try using two copies of code again to make functionality work(better) even when the parser bails early.
    pub _old_code: Arc<Mutex<CodeBundle>>,

    /// Cached changes to files.
    ///
    /// We want to compile files that are being changed before they are saved, so this HashMap keeps track
    /// of what the files contains in the WIP state. The paths are canonicalized.
    pub changed_files: Arc<RwLock<HashMap<Utf8PathBuf, String>>>,

    /// A channel allowing for logging without requiring an async context or handle to the client.
    pub client_log_chan: mpsc::Sender<(MessageType, String)>,

    /// List of Spades built in keywords.
    pub keyword_completions: [CompletionItem; keywords::NR_OF_KEYWORDS],
}

impl ServerBackend {
    pub fn new(sender: mpsc::Sender<(MessageType, String)>) -> Self {
        Self {
            root_dir: Arc::new(Mutex::new(None)),
            changed_files: Arc::new(RwLock::new(HashMap::new())),
            symtab: Arc::new(Mutex::new(None)),
            item_list: Arc::new(Mutex::new(ItemList::new())),
            trait_impls: Arc::new(Mutex::new(TraitImplList::new())),
            code: Arc::new(Mutex::new(CodeBundle::new(String::new()))),
            query_cache: Arc::new(Mutex::new(QueryCache::empty())),
            _old_code: Arc::new(Mutex::new(CodeBundle::new(String::new()))),
            type_states: Arc::new(Mutex::new(BTreeMap::new())),
            client_log_chan: sender,
            keyword_completions: keywords::get_keyword_completions(),
        }
    }
}
