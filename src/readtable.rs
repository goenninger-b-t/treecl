// TreeCL Readtables
//
// Defines syntactic character types and macro dispatch tables.

use std::collections::HashMap;
use crate::reader::{Reader, ReaderResult};

/// Character Syntax Types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxType {
    Constituent,
    Whitespace,
    TerminatingMacro,
    NonTerminatingMacro,
    SingleEscape,   // \
    MultiEscape,    // |
}

/// Reader Macro Function Signature
/// Takes the Reader and the triggering character.
pub type ReaderMacroFn = fn(&mut Reader, char) -> ReaderResult;

/// Readtable case modes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadtableCase {
    Upcase,
    Downcase,
    Preserve,
    Invert,
}

/// Handle for a stored readtable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReadtableId(pub u32);

/// The Readtable
#[derive(Clone)]
pub struct Readtable {
    syntax_types: HashMap<char, SyntaxType>,
    macro_functions: HashMap<char, ReaderMacroFn>,
    default_syntax: SyntaxType,
    case_mode: ReadtableCase,
}

impl Readtable {
    pub fn new() -> Self {
        let mut rt = Self {
            syntax_types: HashMap::new(),
            macro_functions: HashMap::new(),
            default_syntax: SyntaxType::Constituent,
            case_mode: ReadtableCase::Upcase,
        };
        rt.initialize_standard();
        rt
    }
    
    fn initialize_standard(&mut self) {
        // Whitespace
        for c in [' ', '\t', '\n', '\r', '\x0c'] {
            self.set_syntax_type(c, SyntaxType::Whitespace);
        }
        
        // Macros (Terminating)
        self.set_syntax_type('(', SyntaxType::TerminatingMacro);
        self.set_syntax_type(')', SyntaxType::TerminatingMacro);
        self.set_syntax_type('"', SyntaxType::TerminatingMacro);
        self.set_syntax_type('\'', SyntaxType::TerminatingMacro);
        self.set_syntax_type(';', SyntaxType::TerminatingMacro);
        self.set_syntax_type('`', SyntaxType::TerminatingMacro);
        self.set_syntax_type(',', SyntaxType::TerminatingMacro);
        
        // Macros (Non-Terminating)
        self.set_syntax_type('#', SyntaxType::NonTerminatingMacro);
        
        // Escapes
        self.set_syntax_type('\\', SyntaxType::SingleEscape);
        self.set_syntax_type('|', SyntaxType::MultiEscape);
    }
    
    pub fn get_syntax_type(&self, c: char) -> SyntaxType {
        *self.syntax_types.get(&c).unwrap_or(&self.default_syntax)
    }
    
    pub fn set_syntax_type(&mut self, c: char, syntax: SyntaxType) {
        self.syntax_types.insert(c, syntax);
    }
    
    pub fn get_macro_character(&self, c: char) -> Option<ReaderMacroFn> {
        self.macro_functions.get(&c).copied()
    }
    
    pub fn set_macro_character(&mut self, c: char, func: Option<ReaderMacroFn>) {
        if let Some(f) = func {
            self.macro_functions.insert(c, f);
        } else {
            self.macro_functions.remove(&c);
        }
    }
    
    pub fn is_whitespace(&self, c: char) -> bool {
        self.get_syntax_type(c) == SyntaxType::Whitespace
    }

    pub fn readtable_case(&self) -> ReadtableCase {
        self.case_mode
    }

    pub fn set_readtable_case(&mut self, mode: ReadtableCase) {
        self.case_mode = mode;
    }
}

/// Storage for readtables
pub struct ReadtableStore {
    tables: Vec<Readtable>,
    free_list: Vec<u32>,
}

impl ReadtableStore {
    pub fn new() -> Self {
        Self {
            tables: Vec::new(),
            free_list: Vec::new(),
        }
    }

    pub fn alloc(&mut self, table: Readtable) -> ReadtableId {
        if let Some(idx) = self.free_list.pop() {
            self.tables[idx as usize] = table;
            ReadtableId(idx)
        } else {
            let idx = self.tables.len() as u32;
            self.tables.push(table);
            ReadtableId(idx)
        }
    }

    pub fn get(&self, id: ReadtableId) -> Option<&Readtable> {
        self.tables.get(id.0 as usize)
    }

    pub fn get_mut(&mut self, id: ReadtableId) -> Option<&mut Readtable> {
        self.tables.get_mut(id.0 as usize)
    }
}
