// TreeCL Reader - S-Expression Parser
//
// Implements ANSI CL reader with readtable support.

use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolTable, SymbolId};
use crate::readtable::{Readtable, SyntaxType};
use crate::arrays::ArrayStore;
use std::iter::Peekable;
use std::str::Chars;

/// Reader error types
#[derive(Debug, Clone)]
pub enum ReaderError {
    UnexpectedEof,
    UnexpectedChar(char),
    UnbalancedParen,
    InvalidNumber(String),
    InvalidChar(String),
}

impl std::fmt::Display for ReaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "Unexpected end of input"),
            Self::UnexpectedChar(c) => write!(f, "Unexpected character: '{}'", c),
            Self::UnbalancedParen => write!(f, "Unbalanced parentheses"),
            Self::InvalidNumber(s) => write!(f, "Invalid number: {}", s),
            Self::InvalidChar(s) => write!(f, "Invalid character: {}", s),
        }
    }
}

pub type ReaderResult = Result<NodeId, ReaderError>;

/// The TreeCL Reader
pub struct Reader<'a> {
    input: Peekable<Chars<'a>>,
    arena: &'a mut Arena,
    symbols: &'a mut SymbolTable,
    readtable: &'a Readtable,
    arrays: Option<&'a mut ArrayStore>,
    nil_node: NodeId,
}

impl<'a> Reader<'a> {
    pub fn new(input: &'a str, arena: &'a mut Arena, symbols: &'a mut SymbolTable, readtable: &'a Readtable, arrays: Option<&'a mut ArrayStore>) -> Self {
        // Create or get NIL node
        let nil_node = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        
        Self {
            input: input.chars().peekable(),
            arena,
            symbols,
            readtable,
            arrays,
            nil_node,
        }
    }
    
    /// Read a single expression
    pub fn read(&mut self) -> ReaderResult {
        self.skip_whitespace();
        
        match self.input.peek() {
            None => Err(ReaderError::UnexpectedEof),
            Some(&c) => {
                let syntax = self.readtable.get_syntax_type(c);
                match syntax {
                    SyntaxType::TerminatingMacro | SyntaxType::NonTerminatingMacro => {
                        // Dispatch macro
                        // Note: Macros consume the char, so we need to consume it?
                        // Standard: macro fn(stream, char)
                        // If we call the macro, it should consume 'c' if needed?
                        // Usually macro functions expect to consume the stream.
                        // Here, we peeked. 
                        // Let's consume it and pass to macro?
                        // Actually, standard CL reader macros are called with char already peeped/consumed?
                        // "The reader macro function is called with the stream and the character that caused the dispatch."
                        // So we consume it.
                        let ch = self.input.next().unwrap();
                        
                        // Look up function
                        // Simplified: hardcode standard macros for Phase 10 to bootstrap,
                        // OR use the HashMap in readtable if we can populate it.
                        // Since we can't easily pass function pointers to methods of structs we are borrowing (Reader),
                        // this is tricky in Rust if Reader holds &mut Arena.
                        // The macro function needs &mut Reader.
                        // 
                        // For Phase 10, let's keep hardcoded dispatch for standard macros,
                        // but use the SyntaxType to Decide.
                        
                        match ch {
                           '(' => self.read_list(),
                           ')' => Err(ReaderError::UnexpectedChar(')')),
                           '\'' => self.read_quote(),
                           '`' => self.read_quasiquote(),
                           ',' => self.read_unquote(),
                           '"' => self.read_string(),
                           ';' => {
                               self.skip_line_comment();
                               self.read()
                           }
                           '#' => self.read_dispatch(),
                           _ => {
                               // Look up user macro
                               if let Some(func) = self.readtable.get_macro_character(ch) {
                                   func(self, ch)
                               } else {
                                   Err(ReaderError::InvalidChar(format!("Macro not implemented: {}", ch)))
                               }
                           }
                        }
                    }
                    SyntaxType::Whitespace => {
                        self.input.next();
                        self.read()
                    }
                    _ => self.read_atom(), // Constituent, Escape
                }
            }
        }
    }
    
    /// Skip whitespace and comments
    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.input.peek() {
            if c.is_whitespace() {
                self.input.next();
            } else {
                break;
            }
        }
    }
    
    /// Skip line comment (;...)
    fn skip_line_comment(&mut self) {
        while let Some(c) = self.input.next() {
            if c == '\n' {
                break;
            }
        }
    }
    
    /// Read a list: (a b c)
    fn read_list(&mut self) -> ReaderResult {
        self.skip_whitespace();
        
        if let Some(&')') = self.input.peek() {
            self.input.next();
            return Ok(self.nil_node);
        }
        
        let mut elements = Vec::new();
        let mut dotted_cdr = None;
        
        loop {
            self.skip_whitespace();
            
            match self.input.peek() {
                None => return Err(ReaderError::UnbalancedParen),
                Some(&')') => {
                    self.input.next();
                    break;
                }
                Some(&'.') => {
                    // Check for dotted pair
                    self.input.next();
                    if let Some(&c) = self.input.peek() {
                        if c.is_whitespace() || c == ')' {
                            // Dotted pair
                            self.skip_whitespace();
                            dotted_cdr = Some(self.read()?);
                            self.skip_whitespace();
                            if self.input.peek() != Some(&')') {
                                return Err(ReaderError::UnexpectedChar('.'));
                            }
                            self.input.next();
                            break;
                        } else {
                            // Symbol starting with dot
                            let atom = self.read_atom_with_prefix('.')?;
                            elements.push(atom);
                        }
                    }
                }
                _ => {
                    elements.push(self.read()?);
                }
            }
        }
        
        // Build list from elements
        let mut result = dotted_cdr.unwrap_or(self.nil_node);
        for elem in elements.into_iter().rev() {
            result = self.arena.alloc(Node::Fork(elem, result));
        }
        
        Ok(result)
    }
    
    /// Read a quoted expression: 'x -> (quote x)
    fn read_quote(&mut self) -> ReaderResult {
        let expr = self.read()?;
        let quote_sym = self.make_symbol("QUOTE");
        Ok(self.list(&[quote_sym, expr]))
    }
    
    /// Read a quasiquoted expression: `x -> (quasiquote x)
    fn read_quasiquote(&mut self) -> ReaderResult {
        let expr = self.read()?;
        let qq_sym = self.make_symbol("QUASIQUOTE");
        Ok(self.list(&[qq_sym, expr]))
    }
    
    /// Read an unquoted expression: ,x or ,@x
    fn read_unquote(&mut self) -> ReaderResult {
        let splice = self.input.peek() == Some(&'@');
        if splice {
            self.input.next();
        }
        let expr = self.read()?;
        let sym_name = if splice { "UNQUOTE-SPLICING" } else { "UNQUOTE" };
        let uq_sym = self.make_symbol(sym_name);
        Ok(self.list(&[uq_sym, expr]))
    }
    
    /// Read a string: "hello"
    fn read_string(&mut self) -> ReaderResult {
        let mut s = String::new();
        
        loop {
            match self.input.next() {
                None => return Err(ReaderError::UnexpectedEof),
                Some('"') => break,
                Some('\\') => {
                    // Escape sequence
                    match self.input.next() {
                        None => return Err(ReaderError::UnexpectedEof),
                        Some('n') => s.push('\n'),
                        Some('t') => s.push('\t'),
                        Some('r') => s.push('\r'),
                        Some('\\') => s.push('\\'),
                        Some('"') => s.push('"'),
                        Some(c) => s.push(c),
                    }
                }
                Some(c) => s.push(c),
            }
        }
        
        // Store string content directly
        Ok(self.arena.alloc(Node::Leaf(OpaqueValue::String(s))))
    }
    
    /// Read dispatch macro: #...
    fn read_dispatch(&mut self) -> ReaderResult {
        match self.input.peek() {
            None => Err(ReaderError::UnexpectedEof),
            Some(&'\'') => {
                // #'fn -> (function fn)
                self.input.next();
                let name = self.read()?;
                let func_sym = self.make_symbol("FUNCTION");
                Ok(self.list(&[func_sym, name]))
            }
            Some(&'\\') => {
                // #\char
                self.input.next();
                self.read_character()
            }
            Some(&'(') => {
                // #(...) -> vector
                self.read_vector()
            }
            Some(&':') => {
                // #:uninterned-symbol
                self.input.next();
                self.read_uninterned_symbol()
            }
            Some(&c) if c.is_ascii_digit() => {
                // #nA, #nR, etc.
                self.read_number_dispatch()
            }
            Some(&c) => Err(ReaderError::UnexpectedChar(c)),
        }
    }
    
    /// Read a character literal: #\x or #\space
    fn read_character(&mut self) -> ReaderResult {
        let mut name = String::new();
        
        while let Some(&c) = self.input.peek() {
            if c.is_alphanumeric() || c == '-' {
                name.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        
        let ch = match name.to_uppercase().as_str() {
            "SPACE" => ' ',
            "NEWLINE" => '\n',
            "TAB" => '\t',
            "RETURN" => '\r',
            s if s.len() == 1 => s.chars().next().unwrap(),
            _ => return Err(ReaderError::InvalidChar(name)),
        };
        
        // Store character as integer (code point)
        Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(ch as i64))))
    }
    
    /// Read a vector literal: #(1 2 3)
    fn read_vector(&mut self) -> ReaderResult {
        self.skip_whitespace();
        
        let mut elements = Vec::new();
        
        loop {
            self.skip_whitespace();
            match self.input.peek() {
                None => return Err(ReaderError::UnbalancedParen),
                Some(&')') => {
                    self.input.next();
                    break;
                }
                _ => {
                    elements.push(self.read()?);
                }
            }
        }
        
        // Create vector in ArrayStore
        if let Some(store) = self.arrays.as_mut() {
            // Allocate vector
            // What about size? It's dynamic here. 
            // ArrayStore expects size + initial.
            // We need a method to alloc from Vec<NodeId>.
            // ArrayStore currently has `alloc(size, initial)`.
            // We need `alloc_from_vec(vec)`.
            // I need to add `alloc_from_vec` to ArrayStore. 
            // BUT I can't modify ArrayStore here.
            // Wait, I can modify `read_vector` to assume `alloc_from_vec` exists, then go add it.
            
            // Temporary hack: use `alloc` then `set_aref` loop? Inefficient.
            // Better: Add `alloc_from_vec` to `ArrayStore` in next step.
            // For now, just generate error if no store.
            
            // Assume the method exists.
            let vec_id = store.alloc_from_vec(elements);
             Ok(self.arena.alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
        } else {
             Err(ReaderError::InvalidChar("Vectors not supported without ArrayStore".to_string()))
        }
    }
    
    /// Read [ ... ] as vector
    pub fn read_left_bracket(&mut self, _char: char) -> ReaderResult {
        // Read until ]
        let mut elements = Vec::new();
        
        loop {
            self.skip_whitespace();
             match self.input.peek() {
                None => return Err(ReaderError::UnexpectedEof),
                Some(&']') => {
                    self.input.next();
                    break;
                }
                _ => {
                    elements.push(self.read()?);
                }
            }
        }
        
        // Create vector
        if let Some(store) = self.arrays.as_mut() {
            let vec_id = store.alloc_from_vec(elements);
            Ok(self.arena.alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
        } else {
            Err(ReaderError::InvalidChar("Vectors not supported without ArrayStore".to_string()))
        }
    }
    
    /// Error on unmatched ]
    pub fn read_right_bracket(&mut self, _char: char) -> ReaderResult {
        Err(ReaderError::UnexpectedChar(']'))
    }
    
    /// Read an uninterned symbol: #:foo
    fn read_uninterned_symbol(&mut self) -> ReaderResult {
        let name = self.read_symbol_name();
        let sym_id = self.symbols.make_symbol(&name);
        self.symbol_to_node(sym_id)
    }
    
    /// Read number-prefixed dispatch
    fn read_number_dispatch(&mut self) -> ReaderResult {
        // Skip for now
        Err(ReaderError::UnexpectedChar('#'))
    }
    
    /// Read an atom (number or symbol)
    fn read_atom(&mut self) -> ReaderResult {
        let s = self.read_symbol_name();
        self.parse_atom(&s)
    }
    
    /// Read atom with a prefix character
    fn read_atom_with_prefix(&mut self, prefix: char) -> ReaderResult {
        let mut s = String::new();
        s.push(prefix);
        s.push_str(&self.read_symbol_name());
        self.parse_atom(&s)
    }
    
    /// Read a symbol name (until delimiter)
    /// Check if character is a delimiter (based on readtable)
    fn is_delimiter(&self, c: char) -> bool {
        match self.readtable.get_syntax_type(c) {
            SyntaxType::Whitespace | SyntaxType::TerminatingMacro => true,
            _ => false,
        }
    }

    /// Read a symbol name (until delimiter)
    fn read_symbol_name(&mut self) -> String {
        let mut name = String::new();
        
        while let Some(&c) = self.input.peek() {
            if self.is_delimiter(c) {
                break;
            }
            name.push(c);
            self.input.next();
        }
        
        name
    }
    
    /// Parse an atom string as number or symbol
    fn parse_atom(&mut self, s: &str) -> ReaderResult {
        let upper = s.to_uppercase();
        
        // Check for NIL
        if upper == "NIL" {
            return Ok(self.nil_node);
        }
        
        // Try integer
        if let Ok(n) = s.parse::<i64>() {
            return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n))));
        }
        
        // Try big integer
        if let Ok(bn) = s.parse::<num_bigint::BigInt>() {
             return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::BigInt(bn))));
        }
        
        // Try float
        if let Ok(f) = s.parse::<f64>() {
            return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Float(f))));
        }
        
        // Check for keyword
        if s.starts_with(':') {
            let key_name = &s[1..];
            let sym_id = self.symbols.intern_keyword(key_name);
            return self.symbol_to_node(sym_id);
        }
        
        // Check for package-qualified symbol
        if let Some(pos) = s.find(':') {
            let (pkg_name, sym_name) = if s[pos..].starts_with("::") {
                (&s[..pos], &s[pos+2..])
            } else {
                (&s[..pos], &s[pos+1..])
            };
            
            if let Some(pkg_id) = self.symbols.find_package(pkg_name) {
                let sym_id = self.symbols.intern_in(sym_name, pkg_id);
                return self.symbol_to_node(sym_id);
            }
        }
        
        // Regular symbol in current package
        let sym_id = self.symbols.intern(&upper);
        self.symbol_to_node(sym_id)
    }
    
    /// Convert a SymbolId to a Node representation
    fn symbol_to_node(&mut self, sym_id: SymbolId) -> ReaderResult {
        // We encode symbols as Leaf(Symbol(id))
        Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
    }
    
    /// Create a symbol node from name
    fn make_symbol(&mut self, name: &str) -> NodeId {
        let sym_id = self.symbols.intern(name);
        self.arena.alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    }
    
    /// Build a list from nodes
    fn list(&mut self, items: &[NodeId]) -> NodeId {
        let mut result = self.nil_node;
        for &item in items.iter().rev() {
            result = self.arena.alloc(Node::Fork(item, result));
        }
        result
    }
}

/// Check if character is a delimiter

/// Convenience function to read from string
pub fn read_from_string(input: &str, arena: &mut Arena, symbols: &mut SymbolTable) -> ReaderResult {
    let rt = Readtable::new();
    Reader::new(input, arena, symbols, &rt, None).read()
}

/// Read all expressions from a string
pub fn read_all(input: &str, arena: &mut Arena, symbols: &mut SymbolTable) -> Result<Vec<NodeId>, ReaderError> {
    let rt = Readtable::new();
    let mut reader = Reader::new(input, arena, symbols, &rt, None);
    let mut results = Vec::new();
    
    loop {
        reader.skip_whitespace();
        if reader.input.peek().is_none() {
            break;
        }
        results.push(reader.read()?);
    }
    
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolTable;
    use crate::arena::Arena;
    
    #[test]
    fn test_read_integer() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("42", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(42)) => {}
            _ => panic!("Expected integer 42"),
        }
    }
    
    #[test]
    fn test_read_float() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("3.14", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Float(f)) => assert!((f - 3.14).abs() < 0.001),
            _ => panic!("Expected float 3.14"),
        }
    }
    
    #[test]
    fn test_read_symbol() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("foo", &mut arena, &mut symbols).unwrap();
        
        // Symbol is Leaf(Symbol(id)) - naked symbol representation
        match arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Symbol(_)) => {}
            _ => panic!("Expected symbol (Leaf(Symbol))"),
        }
    }
    
    #[test]
    fn test_read_nil() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("nil", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Nil) => {}
            _ => panic!("Expected NIL"),
        }
    }
    
    #[test]
    fn test_read_list() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("(1 2 3)", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Fork(_, _) => {}
            _ => panic!("Expected list (Fork)"),
        }
    }
    
    #[test]
    fn test_read_empty_list() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("()", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Nil) => {}
            _ => panic!("Expected empty list (NIL)"),
        }
    }
    
    #[test]
    fn test_read_quote() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("'foo", &mut arena, &mut symbols).unwrap();
        
        // Should be (quote foo)
        match arena.get_unchecked(result) {
            Node::Fork(_, _) => {}
            _ => panic!("Expected quoted form"),
        }
    }
    
    #[test]
    fn test_read_keyword() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let _result = read_from_string(":test", &mut arena, &mut symbols).unwrap();
        
        // Keyword should be interned in KEYWORD package
        // Check symbols table
        let kw = symbols.find_package("KEYWORD").unwrap();
        let pkg = symbols.get_package(kw).unwrap();
        assert!(pkg.find_external("TEST").is_some());
    }
    
    #[test]
    fn test_read_nested_list() {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let result = read_from_string("(a (b c) d)", &mut arena, &mut symbols).unwrap();
        
        match arena.get_unchecked(result) {
            Node::Fork(_, _) => {}
            _ => panic!("Expected nested list"),
        }
    }
}
