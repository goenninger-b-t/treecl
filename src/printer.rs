// TreeCL Printer - Expression Output
//
// Implements ANSI CL print functions.

use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolTable, SymbolId};

/// Print options
#[derive(Debug, Clone)]
pub struct PrintOptions {
    /// Print readably (escape special chars)
    pub escape: bool,
    /// Print with package prefixes
    pub package_prefix: bool,
    /// Maximum depth to print
    pub max_depth: usize,
    /// Maximum list length to print
    pub max_length: usize,
    /// Pretty print
    pub pretty: bool,
}

impl Default for PrintOptions {
    fn default() -> Self {
        Self {
            escape: true,
            package_prefix: true,
            max_depth: 100,
            max_length: 1000,
            pretty: false,
        }
    }
}

impl PrintOptions {
    /// For prin1 (readable)
    pub fn prin1() -> Self {
        Self::default()
    }
    
    /// For princ (human-readable)
    pub fn princ() -> Self {
        Self {
            escape: false,
            ..Self::default()
        }
    }
}

/// The TreeCL Printer
pub struct Printer<'a> {
    arena: &'a Arena,
    symbols: &'a SymbolTable,
    output: String,
    options: PrintOptions,
    current_depth: usize,
}

impl<'a> Printer<'a> {
    pub fn new(arena: &'a Arena, symbols: &'a SymbolTable, options: PrintOptions) -> Self {
        Self {
            arena,
            symbols,
            output: String::new(),
            options,
            current_depth: 0,
        }
    }
    
    /// Print an expression to string
    pub fn print(&mut self, node: NodeId) -> &str {
        self.print_node(node);
        &self.output
    }
    
    fn print_node(&mut self, node: NodeId) {
        if self.current_depth > self.options.max_depth {
            self.output.push_str("...");
            return;
        }
        
        self.current_depth += 1;
        
        // Check for symbolic combinators first
        if let Some(name) = self.detect_combinator(node) {
            self.output.push_str(name);
            self.current_depth -= 1;
            return;
        }
        
        match self.arena.get_unchecked(node).clone() {
            Node::Leaf(val) => self.print_leaf(val),
            Node::Stem(inner) => self.print_stem(inner),
            Node::Fork(_car, _cdr) => self.print_list(node),
        }
        
        self.current_depth -= 1;
    }
    
    /// Detect if a node matches a known combinator pattern
    fn detect_combinator(&self, node: NodeId) -> Option<&'static str> {
        // Check for K = Fork(Nil, Nil)
        if self.is_k(node) {
            return Some("K");
        }
        
        // Check for I = Fork(K, K)
        if let Node::Fork(left, right) = self.arena.get_unchecked(node) {
            if self.is_k(*left) && self.is_k(*right) {
                return Some("I");
            }
        }
        
        None
    }
    
    /// Check if node is K = Fork(Nil, Nil)
    fn is_k(&self, node: NodeId) -> bool {
        if let Node::Fork(left, right) = self.arena.get_unchecked(node) {
            matches!(
                (self.arena.get_unchecked(*left), self.arena.get_unchecked(*right)),
                (Node::Leaf(OpaqueValue::Nil), Node::Leaf(OpaqueValue::Nil))
            )
        } else {
            false
        }
    }
    
    fn print_leaf(&mut self, val: OpaqueValue) {
        match val {
            OpaqueValue::Nil => self.output.push_str("NIL"),
            OpaqueValue::Integer(n) => {
                self.output.push_str(&n.to_string());
            }
            OpaqueValue::Float(f) => {
                if f.is_nan() {
                    self.output.push_str("NaN");
                } else if f.is_infinite() {
                    if f.is_sign_positive() {
                        self.output.push_str("+Inf");
                    } else {
                        self.output.push_str("-Inf");
                    }
                } else {
                    self.output.push_str(&format!("{}", f));
                }
            }
            OpaqueValue::String(s) => {
                if self.options.escape {
                    self.output.push('"');
                    // Simple escape
                    for c in s.chars() {
                        if c == '"' || c == '\\' {
                            self.output.push('\\');
                        }
                        self.output.push(c);
                    }
                    self.output.push('"');
                } else {
                    self.output.push_str(&s);
                }
            }
            OpaqueValue::VectorHandle(h) => {
                self.output.push_str(&format!("#<vector:{}>", h));
            }
            OpaqueValue::ForeignPtr(ptr) => {
                self.output.push_str(&format!("#<foreign:{:?}>", ptr));
            }
            OpaqueValue::Closure(id) => {
                self.output.push_str(&format!("#<closure:{}>", id));
            }
            OpaqueValue::Generic(id) => {
                self.output.push_str(&format!("#<generic:{}>", id));
            }
            OpaqueValue::Instance(id) => {
                self.output.push_str(&format!("#<instance:{}>", id));
            }
            OpaqueValue::Class(id) => {
                self.output.push_str(&format!("#<class:{}>", id));
            }
            OpaqueValue::Symbol(id) => {
                let sym_id = SymbolId(id);
                if let Some(sym) = self.symbols.get_symbol(sym_id) {
                    if sym.is_keyword() {
                        self.output.push(':');
                        self.output.push_str(&sym.name);
                    } else if self.options.package_prefix {
                         if let Some(pkg_id) = sym.package {
                            if let Some(pkg) = self.symbols.get_package(pkg_id) {
                                if pkg.name != "CL-USER" && pkg.name != "COMMON-LISP" {
                                    self.output.push_str(&pkg.name);
                                    self.output.push(':');
                                }
                            }
                        }
                        self.output.push_str(&sym.name);
                    } else {
                         self.output.push_str(&sym.name);
                    }
                } else {
                    self.output.push_str(&format!("#<symbol:{}>", id));
                }
            }
            OpaqueValue::BigInt(n) => {
                self.output.push_str(&n.to_string());
            }
        }
    }
    
    fn print_stem(&mut self, inner: NodeId) {
        // Handle legacy Stem(Leaf(Integer)) just in case or for internal use
        if let Node::Leaf(OpaqueValue::Integer(id)) = self.arena.get_unchecked(inner).clone() {
            self.output.push_str(&format!("#<stem-int:{}>", id));
            return;
        }
        
        // Generic stem (K combinator)
        self.output.push_str("#<K ");
        self.print_node(inner);
        self.output.push('>');
    }
    
    fn print_list(&mut self, node: NodeId) {
        self.output.push('(');
        
        let mut current = node;
        let mut first = true;
        let mut count = 0;
        
        loop {
            if count >= self.options.max_length {
                self.output.push_str(" ...");
                break;
            }
            
            match self.arena.get_unchecked(current).clone() {
                Node::Fork(car, cdr) => {
                    if !first {
                        self.output.push(' ');
                    }
                    first = false;
                    
                    self.print_node(car);
                    current = cdr;
                    count += 1;
                }
                Node::Leaf(OpaqueValue::Nil) => {
                    // Proper list end
                    break;
                }
                _ => {
                    // Improper list
                    self.output.push_str(" . ");
                    self.print_node(current);
                    break;
                }
            }
        }
        
        self.output.push(')');
    }
}

/// Print expression to string (like prin1-to-string)
pub fn print_to_string(arena: &Arena, symbols: &SymbolTable, node: NodeId) -> String {
    let mut printer = Printer::new(arena, symbols, PrintOptions::prin1());
    printer.print(node).to_string()
}

/// Print expression without escapes (like princ-to-string)
pub fn princ_to_string(arena: &Arena, symbols: &SymbolTable, node: NodeId) -> String {
    let mut printer = Printer::new(arena, symbols, PrintOptions::princ());
    printer.print(node).to_string()
}

/// Simple format function (subset of CL format)
pub fn format(arena: &Arena, symbols: &SymbolTable, control: &str, args: &[NodeId]) -> String {
    let mut output = String::new();
    let mut chars = control.chars().peekable();
    let mut arg_idx = 0;
    
    while let Some(c) = chars.next() {
        if c == '~' {
            match chars.next() {
                Some('A') | Some('a') => {
                    // ~A: Aesthetic (princ)
                    if arg_idx < args.len() {
                        output.push_str(&princ_to_string(arena, symbols, args[arg_idx]));
                        arg_idx += 1;
                    }
                }
                Some('S') | Some('s') => {
                    // ~S: Standard (prin1)
                    if arg_idx < args.len() {
                        output.push_str(&print_to_string(arena, symbols, args[arg_idx]));
                        arg_idx += 1;
                    }
                }
                Some('D') | Some('d') => {
                    // ~D: Decimal
                    if arg_idx < args.len() {
                        output.push_str(&print_to_string(arena, symbols, args[arg_idx]));
                        arg_idx += 1;
                    }
                }
                Some('%') => {
                    // ~%: Newline
                    output.push('\n');
                }
                Some('~') => {
                    // ~~: Literal tilde
                    output.push('~');
                }
                Some('&') => {
                    // ~&: Fresh line (newline if not at column 0)
                    if !output.ends_with('\n') && !output.is_empty() {
                        output.push('\n');
                    }
                }
                Some(c) => {
                    // Unknown directive, copy literally
                    output.push('~');
                    output.push(c);
                }
                None => {
                    output.push('~');
                }
            }
        } else {
            output.push(c);
        }
    }
    
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::Arena;
    use crate::symbol::SymbolTable;
    
    #[test]
    fn test_print_integer() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        let node = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        
        assert_eq!(print_to_string(&arena, &symbols, node), "42");
    }
    
    #[test]
    fn test_print_float() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        let node = arena.alloc(Node::Leaf(OpaqueValue::Float(3.14)));
        
        let s = print_to_string(&arena, &symbols, node);
        assert!(s.starts_with("3.14"));
    }
    
    #[test]
    fn test_print_nil() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        let node = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        
        assert_eq!(print_to_string(&arena, &symbols, node), "NIL");
    }
    
    #[test]
    fn test_print_list() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        
        let nil = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        let a = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let c = arena.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        
        let list = arena.alloc(Node::Fork(c, nil));
        let list = arena.alloc(Node::Fork(b, list));
        let list = arena.alloc(Node::Fork(a, list));
        
        assert_eq!(print_to_string(&arena, &symbols, list), "(1 2 3)");
    }
    
    #[test]
    fn test_print_dotted_pair() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        
        let a = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let pair = arena.alloc(Node::Fork(a, b));
        
        assert_eq!(print_to_string(&arena, &symbols, pair), "(1 . 2)");
    }
    
    #[test]
    fn test_format_basic() {
        let arena = Arena::new();
        let symbols = SymbolTable::new();
        
        let result = format(&arena, &symbols, "Hello~%World", &[]);
        assert_eq!(result, "Hello\nWorld");
    }
    
    #[test]
    fn test_format_with_args() {
        let mut arena = Arena::new();
        let symbols = SymbolTable::new();
        
        let num = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let result = format(&arena, &symbols, "Value: ~D", &[num]);
        assert_eq!(result, "Value: 42");
    }
}
