// TreeCL Reader - S-Expression Parser
//
// Implements ANSI CL reader with readtable support.

use crate::arena::{Arena, Node};
use crate::arrays::ArrayStore;
use crate::readtable::{Readtable, ReadtableCase, SyntaxType};
use crate::symbol::{SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};
use std::cell::RefCell;
use std::collections::HashMap;
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

pub struct ReaderOptions {
    pub read_base: u32,
    pub read_eval: bool,
    pub read_suppress: bool,
    pub preserve_whitespace: bool,
    pub features: Vec<String>,
}

impl Default for ReaderOptions {
    fn default() -> Self {
        Self {
            read_base: 10,
            read_eval: true,
            read_suppress: false,
            preserve_whitespace: false,
            features: vec![
                "ANSI-CL".to_string(),
                "COMMON-LISP".to_string(),
                "TREECL".to_string(),
                "IEEE-FLOATING-POINT".to_string(),
                "X86-64".to_string(),
                "LITTLE-ENDIAN".to_string(),
            ],
        }
    }
}

pub struct ReadEvalContext {
    pub proc_ptr: *mut crate::process::Process,
    pub globals_ptr: *const crate::context::GlobalContext,
    pub env_ptr: *const crate::eval::Environment,
}

thread_local! {
    static READ_EVAL_CONTEXT: RefCell<Option<ReadEvalContext>> = RefCell::new(None);
}

pub fn set_read_eval_context(ctx: Option<ReadEvalContext>) {
    READ_EVAL_CONTEXT.with(|cell| {
        *cell.borrow_mut() = ctx;
    });
}

/// The TreeCL Reader
pub struct Reader<'a> {
    input: Peekable<Chars<'a>>,
    arena: &'a mut Arena,
    symbols: &'a mut SymbolTable,
    readtable: &'a Readtable,
    arrays: Option<&'a mut ArrayStore>,
    nil_node: NodeId,
    read_base: u32,
    read_eval: bool,
    read_suppress: bool,
    preserve_whitespace: bool,
    features: Vec<String>,
    label_map: HashMap<u32, NodeId>,
}

impl<'a> Reader<'a> {
    pub fn new(
        input: &'a str,
        arena: &'a mut Arena,
        symbols: &'a mut SymbolTable,
        readtable: &'a Readtable,
        arrays: Option<&'a mut ArrayStore>,
    ) -> Self {
        Self::new_with_options(
            input,
            arena,
            symbols,
            readtable,
            arrays,
            ReaderOptions::default(),
        )
    }

    pub fn new_with_options(
        input: &'a str,
        arena: &'a mut Arena,
        symbols: &'a mut SymbolTable,
        readtable: &'a Readtable,
        arrays: Option<&'a mut ArrayStore>,
        options: ReaderOptions,
    ) -> Self {
        // Create or get NIL node
        let nil_node = arena.alloc(Node::Leaf(OpaqueValue::Nil));

        Self {
            input: input.chars().peekable(),
            arena,
            symbols,
            readtable,
            arrays,
            nil_node,
            read_base: options.read_base,
            read_eval: options.read_eval,
            read_suppress: options.read_suppress,
            preserve_whitespace: options.preserve_whitespace,
            features: options
                .features
                .into_iter()
                .map(|s| s.to_uppercase())
                .collect(),
            label_map: HashMap::new(),
        }
    }

    /// Read a single expression
    pub fn read(&mut self) -> ReaderResult {
        self.skip_whitespace();

        match self.input.peek() {
            None => Err(ReaderError::UnexpectedEof),
            Some(&c) => {
                let syntax = self.readtable.get_syntax_type(c);
                let result = match syntax {
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
                                    Err(ReaderError::InvalidChar(format!(
                                        "Macro not implemented: {}",
                                        ch
                                    )))
                                }
                            }
                        }
                    }
                    SyntaxType::Whitespace => {
                        self.input.next();
                        self.read()
                    }
                    _ => self.read_atom(), // Constituent, Escape
                };

                let mut out = result?;

                if self.read_suppress {
                    out = self.nil_node;
                }

                if !self.preserve_whitespace {
                    self.skip_whitespace();
                }

                Ok(out)
            }
        }
    }

    /// Skip whitespace and comments
    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.input.peek() {
            if self.readtable.is_whitespace(c) {
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

    /// Skip a possibly nested block comment (#| ... |#)
    fn skip_block_comment(&mut self) -> Result<(), ReaderError> {
        let mut depth = 1usize;
        while let Some(c) = self.input.next() {
            match c {
                '#' => {
                    if self.input.peek() == Some(&'|') {
                        self.input.next();
                        depth += 1;
                    }
                }
                '|' => {
                    if self.input.peek() == Some(&'#') {
                        self.input.next();
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                        if depth == 0 {
                            return Ok(());
                        }
                    }
                }
                _ => {}
            }
        }
        Err(ReaderError::UnexpectedEof)
    }

    fn read_eval_form(&mut self, form: NodeId) -> ReaderResult {
        let result = READ_EVAL_CONTEXT.with(|cell| {
            cell.borrow().as_ref().map(|ctx| unsafe {
                let proc = &mut *ctx.proc_ptr;
                let globals = &*ctx.globals_ptr;
                let env = &*ctx.env_ptr;
                let mut interp = crate::eval::Interpreter::new(proc, globals);
                interp.eval(form, env)
            })
        });

        match result {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => Err(ReaderError::InvalidChar(format!(
                "READ-EVAL error: {:?}",
                e
            ))),
            None => Err(ReaderError::InvalidChar(
                "READ-EVAL context not available".to_string(),
            )),
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
        let sym_name = if splice {
            "UNQUOTE-SPLICING"
        } else {
            "UNQUOTE"
        };
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
            Some(&'.') => {
                // #. read-time eval
                self.input.next();
                if self.read_suppress {
                    let _ = self.read()?;
                    return Ok(self.nil_node);
                }
                if !self.read_eval {
                    return Err(ReaderError::InvalidChar(
                        "READ-EVAL is disabled".to_string(),
                    ));
                }
                let form = self.read()?;
                self.read_eval_form(form)
            }
            Some(&'|') => {
                // #| ... |# block comment (possibly nested)
                self.input.next();
                self.skip_block_comment()?;
                self.read()
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
            Some(&'x') | Some(&'X') => {
                // #x... Hex
                self.input.next();
                self.read_radix(16)
            }
            Some(&'o') | Some(&'O') => {
                // #o... Octal
                self.input.next();
                self.read_radix(8)
            }
            Some(&'b') | Some(&'B') => {
                // #b... Binary
                self.input.next();
                self.read_radix(2)
            }
            Some(&'p') | Some(&'P') => {
                // #P"..." Pathname
                self.input.next();
                // Expect string
                let form = self.read()?;
                // For now, just return valid node. Pathname support might be missing.
                // We could wrap it or just return the string/form.
                // If we return the string, (truename "foo") usually works.
                Ok(form)
            }
            Some(&c) if c.is_ascii_digit() => {
                // #nA, #nR, etc.
                self.read_number_dispatch()
            }
            Some(&'+') => {
                // #+ feature-expr form
                self.input.next();
                if self.read_feature_check()? {
                    self.read()
                } else {
                    // Skip next form
                    let _ = self.read()?;
                    self.read()
                }
            }
            Some(&'-') => {
                // #- feature-expr form
                self.input.next();
                if !self.read_feature_check()? {
                    self.read()
                } else {
                    // Skip next form
                    let _ = self.read()?;
                    self.read()
                }
            }
            Some(&c) => Err(ReaderError::UnexpectedChar(c)),
        }
    }

    /// Read number in specific radix
    fn read_radix(&mut self, radix: u32) -> ReaderResult {
        // Read token
        let s = self.read_symbol_name()?;
        // We can reuse read_symbol_name which reads until delimiter
        // Then parse with radix

        if let Ok(n) = i64::from_str_radix(&s, radix) {
            Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n))))
        } else if let Some(bn) = num_bigint::BigInt::parse_bytes(s.as_bytes(), radix) {
            Ok(self.arena.alloc(Node::Leaf(OpaqueValue::BigInt(bn))))
        } else {
            Err(ReaderError::InvalidNumber(format!(
                "Invalid radix {} number: {}",
                radix, s
            )))
        }
    }

    /// Read and evaluate a feature expression
    fn read_feature_check(&mut self) -> Result<bool, ReaderError> {
        let feature_expr = self.read()?;
        Ok(self.eval_feature(feature_expr))
    }

    /// Evaluate a feature expression against *FEATURES* (hardcoded for now)
    fn eval_feature(&mut self, node_id: NodeId) -> bool {
        let features = &self.features;
        match self.arena.get_unchecked(node_id) {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                if let Some(name) = self.symbols.symbol_name(crate::symbol::SymbolId(*id)) {
                    let name = name.to_uppercase();
                    features.iter().any(|f| f == &name)
                } else {
                    false
                }
            }
            Node::Fork(car, cdr) => {
                // (not x), (or ...), (and ...)
                if let Node::Leaf(OpaqueValue::Symbol(op_id)) = self.arena.get_unchecked(*car) {
                    if let Some(op_name) = self.symbols.symbol_name(crate::symbol::SymbolId(*op_id))
                    {
                        match op_name.to_uppercase().as_str() {
                            "NOT" => {
                                // (not x) - expect one arg
                                if let Node::Fork(arg, _) = self.arena.get_unchecked(*cdr) {
                                    !self.eval_feature(*arg)
                                } else {
                                    false
                                }
                            }
                            "OR" => {
                                // (or ...) - any true
                                let mut current = *cdr;
                                loop {
                                    // Extract item and next to end borrow
                                    let (item, next) = match self.arena.get_unchecked(current) {
                                        Node::Fork(item, next) => (*item, *next),
                                        _ => break,
                                    };

                                    if self.eval_feature(item) {
                                        return true;
                                    }
                                    current = next;
                                }
                                false
                            }
                            "AND" => {
                                // (and ...) - all true
                                let mut current = *cdr;
                                loop {
                                    let (item, next) = match self.arena.get_unchecked(current) {
                                        Node::Fork(item, next) => (*item, *next),
                                        _ => break,
                                    };

                                    if !self.eval_feature(item) {
                                        return false;
                                    }
                                    current = next;
                                }
                                true
                            }
                            _ => false,
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Read a character literal: #\x or #\space
    fn read_character(&mut self) -> ReaderResult {
        let name = self.read_token_with_case(ReadtableCase::Preserve)?;
        let ch = if name.is_empty() {
            // Fallback: single character after #\
            if let Some(c) = self.input.next() {
                c
            } else {
                return Err(ReaderError::UnexpectedEof);
            }
        } else {
            match name.to_uppercase().as_str() {
                "SPACE" => ' ',
                "NEWLINE" => '\n',
                "TAB" => '\t',
                "RETURN" => '\r',
                "LINEFEED" => '\n',
                "PAGE" => '\x0c',
                "RUBOUT" => '\x7f',
                "BACKSPACE" => '\x08',
                "NULL" => '\0',
                s if s.len() == 1 => s.chars().next().unwrap(),
                _ => return Err(ReaderError::InvalidChar(name)),
            }
        };

        // Store character as integer (code point)
        Ok(self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Integer(ch as i64))))
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
            Ok(self
                .arena
                .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
        } else {
            Err(ReaderError::InvalidChar(
                "Vectors not supported without ArrayStore".to_string(),
            ))
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
            Ok(self
                .arena
                .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
        } else {
            Err(ReaderError::InvalidChar(
                "Vectors not supported without ArrayStore".to_string(),
            ))
        }
    }

    /// Error on unmatched ]
    pub fn read_right_bracket(&mut self, _char: char) -> ReaderResult {
        Err(ReaderError::UnexpectedChar(']'))
    }

    /// Read an uninterned symbol: #:foo
    fn read_uninterned_symbol(&mut self) -> ReaderResult {
        let name = self.read_symbol_name()?;
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
        let s = self.read_symbol_name()?;
        self.parse_atom(&s)
    }

    /// Read atom with a prefix character
    fn read_atom_with_prefix(&mut self, prefix: char) -> ReaderResult {
        let mut s = String::new();
        s.push(prefix);
        s.push_str(&self.read_symbol_name()?);
        self.parse_atom(&s)
    }

    /// Read a symbol name (until delimiter)
    fn read_token_with_case(&mut self, case_mode: ReadtableCase) -> Result<String, ReaderError> {
        let mut chars: Vec<(char, bool)> = Vec::new();
        let mut in_multi_escape = false;

        while let Some(&c) = self.input.peek() {
            if in_multi_escape {
                match c {
                    '|' => {
                        self.input.next();
                        in_multi_escape = false;
                        continue;
                    }
                    '\\' => {
                        self.input.next();
                        if let Some(escaped) = self.input.next() {
                            chars.push((escaped, true));
                            continue;
                        } else {
                            return Err(ReaderError::UnexpectedEof);
                        }
                    }
                    _ => {
                        self.input.next();
                        chars.push((c, true));
                        continue;
                    }
                }
            }

            let syntax = self.readtable.get_syntax_type(c);
            match syntax {
                SyntaxType::Whitespace | SyntaxType::TerminatingMacro => break,
                SyntaxType::SingleEscape => {
                    self.input.next();
                    if let Some(escaped) = self.input.next() {
                        chars.push((escaped, true));
                    } else {
                        return Err(ReaderError::UnexpectedEof);
                    }
                }
                SyntaxType::MultiEscape => {
                    self.input.next();
                    in_multi_escape = true;
                }
                _ => {
                    self.input.next();
                    chars.push((c, false));
                }
            }
        }

        if in_multi_escape {
            return Err(ReaderError::UnexpectedEof);
        }

        let mut has_upper = false;
        let mut has_lower = false;
        for (ch, escaped) in &chars {
            if *escaped {
                continue;
            }
            if ch.is_uppercase() {
                has_upper = true;
            } else if ch.is_lowercase() {
                has_lower = true;
            }
        }

        let mut out = String::new();
        let invert_to_upper = case_mode == ReadtableCase::Invert && has_lower && !has_upper;
        let invert_to_lower = case_mode == ReadtableCase::Invert && has_upper && !has_lower;

        for (ch, escaped) in chars {
            if escaped {
                out.push(ch);
                continue;
            }

            let mut push_converted = |c: char, to_upper: bool| {
                if to_upper {
                    for uc in c.to_uppercase() {
                        out.push(uc);
                    }
                } else {
                    for lc in c.to_lowercase() {
                        out.push(lc);
                    }
                }
            };

            match case_mode {
                ReadtableCase::Preserve => out.push(ch),
                ReadtableCase::Upcase => push_converted(ch, true),
                ReadtableCase::Downcase => push_converted(ch, false),
                ReadtableCase::Invert => {
                    if invert_to_upper {
                        push_converted(ch, true);
                    } else if invert_to_lower {
                        push_converted(ch, false);
                    } else {
                        out.push(ch);
                    }
                }
            }
        }

        Ok(out)
    }

    fn read_symbol_name(&mut self) -> Result<String, ReaderError> {
        let case_mode = self.readtable.readtable_case();
        self.read_token_with_case(case_mode)
    }

    /// Parse an atom string as number or symbol
    fn parse_atom(&mut self, s: &str) -> ReaderResult {
        // Check for NIL
        if s == "NIL" {
            return Ok(self.nil_node);
        }

        // Try integer (respect read-base)
        if self.read_base == 10 {
            if let Ok(n) = s.parse::<i64>() {
                return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n))));
            }
        } else if let Ok(n) = i64::from_str_radix(s, self.read_base) {
            return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n))));
        }

        // Try big integer
        if self.read_base == 10 {
            if let Ok(bn) = s.parse::<num_bigint::BigInt>() {
                return Ok(self.arena.alloc(Node::Leaf(OpaqueValue::BigInt(bn))));
            }
        } else if let Some(bn) = num_bigint::BigInt::parse_bytes(s.as_bytes(), self.read_base) {
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
                (&s[..pos], &s[pos + 2..])
            } else {
                (&s[..pos], &s[pos + 1..])
            };

            if let Some(pkg_id) = self.symbols.find_package(pkg_name) {
                let sym_id = self.symbols.intern_in(sym_name, pkg_id);
                return self.symbol_to_node(sym_id);
            }
        }

        // Regular symbol in current package
        let sym_id = self.symbols.intern(s);
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
pub fn read_all(
    input: &str,
    arena: &mut Arena,
    symbols: &mut SymbolTable,
) -> Result<Vec<NodeId>, ReaderError> {
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
    use crate::arena::Arena;
    use crate::symbol::SymbolTable;

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
