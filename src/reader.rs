// TreeCL Reader - S-Expression Parser
//
// Implements ANSI CL reader with readtable support.

use crate::arena::{Arena, Node};
use crate::arrays::ArrayStore;
use crate::readtable::{Readtable, ReadtableCase, SyntaxType};
use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};
use num_traits::{Signed, ToPrimitive};
use std::cell::RefCell;
use std::collections::HashMap;

struct ReaderInput {
    chars: Vec<char>,
    index: usize,
}

impl ReaderInput {
    fn new(input: &str) -> Self {
        Self {
            chars: input.chars().collect(),
            index: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.index).copied()
    }

    fn next(&mut self) -> Option<char> {
        if self.index < self.chars.len() {
            let c = self.chars[self.index];
            self.index += 1;
            Some(c)
        } else {
            None
        }
    }

    fn unread(&mut self) {
        if self.index > 0 {
            self.index -= 1;
        }
    }

    fn position(&self) -> usize {
        self.index
    }
}

/// Reader error types
#[derive(Debug, Clone)]
pub enum ReaderError {
    UnexpectedEof,
    UnexpectedChar(char),
    UnbalancedParen,
    InvalidNumber(String),
    InvalidChar(String),
    Unsuppressible(String),
}

impl std::fmt::Display for ReaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "Unexpected end of input"),
            Self::UnexpectedChar(c) => write!(f, "Unexpected character: '{}'", c),
            Self::UnbalancedParen => write!(f, "Unbalanced parentheses"),
            Self::InvalidNumber(s) => write!(f, "Invalid number: {}", s),
            Self::InvalidChar(s) => write!(f, "Invalid character: {}", s),
            Self::Unsuppressible(s) => write!(f, "Reader error: {}", s),
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
    input: ReaderInput,
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
    label_map: HashMap<u64, NodeId>,
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
            input: ReaderInput::new(input),
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

    pub fn position(&self) -> usize {
        self.input.position()
    }

    /// Read a single expression
    pub fn read(&mut self) -> ReaderResult {
        self.skip_whitespace();

        match self.input.peek() {
            None => Err(ReaderError::UnexpectedEof),
            Some(c) => {
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

                        if let Some(func) = self.readtable.get_macro_character(ch) {
                            return func(self, ch);
                        }
                        if let Some(func) = self.readtable.get_lisp_macro(ch) {
                            return self.read_lisp_macro(func, ch);
                        }
                        if ch != '#' && self.readtable.is_dispatch_macro_character(ch) {
                            return self.read_dispatch_table(ch);
                        }

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
                            _ => Err(ReaderError::InvalidChar(format!(
                                "Macro not implemented: {}",
                                ch
                            ))),
                        }
                    }
                    SyntaxType::Whitespace => {
                        self.input.next();
                        self.read()
                    }
                    _ => self.read_atom(), // Constituent, Escape
                };

                let mut out = match result {
                    Ok(v) => v,
                    Err(e) => {
                        if self.read_suppress {
                            let unsuppressible = matches!(e, ReaderError::Unsuppressible(_))
                                || matches!(e, ReaderError::UnexpectedChar(')'));
                            if !unsuppressible {
                                while self.input.next().is_some() {}
                                return Ok(self.nil_node);
                            }
                        }
                        return Err(e);
                    }
                };

                if self.read_suppress {
                    out = self.nil_node;
                }

                Ok(out)
            }
        }
    }

    pub fn eof_after_whitespace(&mut self) -> bool {
        self.skip_whitespace();
        self.input.peek().is_none()
    }

    pub fn read_delimited_list(&mut self, delim: char) -> ReaderResult {
        let mut elements = Vec::new();
        loop {
            self.skip_whitespace();
            match self.input.peek() {
                None => return Err(ReaderError::UnexpectedEof),
                Some(c) if c == delim => {
                    self.input.next();
                    break;
                }
                _ => elements.push(self.read()?),
            }
        }

        let mut result = self.nil_node;
        for elem in elements.into_iter().rev() {
            result = self.arena.alloc(Node::Fork(elem, result));
        }
        Ok(result)
    }

    /// Skip whitespace and comments
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.input.peek() {
            if self.readtable.is_whitespace(c) {
                self.input.next();
            } else {
                break;
            }
        }
    }

    /// Skip line comment (;...)
    pub(crate) fn skip_line_comment(&mut self) {
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
                    if self.input.peek() == Some('|') {
                        self.input.next();
                        depth += 1;
                    }
                }
                '|' => {
                    if self.input.peek() == Some('#') {
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
    pub(crate) fn read_list(&mut self) -> ReaderResult {
        self.skip_whitespace();

        if self.input.peek() == Some(')') {
            self.input.next();
            return Ok(self.nil_node);
        }

        let mut elements = Vec::new();
        let mut dotted_cdr = None;

        loop {
            self.skip_whitespace();

            match self.input.peek() {
                None => return Err(ReaderError::UnbalancedParen),
                Some(')') => {
                    self.input.next();
                    break;
                }
                Some('.') => {
                    // Check for dotted pair
                    self.input.next();
                    if let Some(c) = self.input.peek() {
                        if c.is_whitespace() || c == ')' {
                            // Dotted pair
                            self.skip_whitespace();
                            dotted_cdr = Some(self.read()?);
                            self.skip_whitespace();
                            if self.input.peek() != Some(')') {
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
    pub(crate) fn read_quote(&mut self) -> ReaderResult {
        let expr = self.read()?;
        let quote_sym = self.make_symbol("QUOTE");
        Ok(self.list(&[quote_sym, expr]))
    }

    /// Read a quasiquoted expression: `x -> (quasiquote x)
    pub(crate) fn read_quasiquote(&mut self) -> ReaderResult {
        let expr = self.read()?;
        let qq_sym = self.make_symbol("QUASIQUOTE");
        Ok(self.list(&[qq_sym, expr]))
    }

    /// Read an unquoted expression: ,x or ,@x
    pub(crate) fn read_unquote(&mut self) -> ReaderResult {
        let splice = self.input.peek() == Some('@');
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
    pub(crate) fn read_string(&mut self) -> ReaderResult {
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
    pub(crate) fn read_dispatch(&mut self) -> ReaderResult {
        match self.input.peek() {
            None => Err(ReaderError::UnexpectedEof),
            Some('\'') => {
                // #'fn -> (function fn)
                self.input.next();
                let name = self.read()?;
                let func_sym = self.make_symbol("FUNCTION");
                Ok(self.list(&[func_sym, name]))
            }
            Some('\\') => {
                // #\char
                self.input.next();
                self.read_character()
            }
            Some('.') => {
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
            Some('|') => {
                // #| ... |# block comment (possibly nested)
                self.input.next();
                self.skip_block_comment()?;
                self.read()
            }
            Some('(') => {
                // #(...) -> vector
                self.read_vector()
            }
            Some(':') => {
                // #:uninterned-symbol
                self.input.next();
                self.read_uninterned_symbol()
            }
            Some('x') | Some('X') => {
                // #x... Hex
                self.input.next();
                self.read_radix(16)
            }
            Some('o') | Some('O') => {
                // #o... Octal
                self.input.next();
                self.read_radix(8)
            }
            Some('b') | Some('B') => {
                // #b... Binary
                self.input.next();
                self.read_radix(2)
            }
            Some('p') | Some('P') => {
                // #P"..." Pathname
                self.input.next();
                // Expect string
                let form = self.read()?;
                // For now, just return valid node. Pathname support might be missing.
                // We could wrap it or just return the string/form.
                // If we return the string, (truename "foo") usually works.
                Ok(form)
            }
            Some('*') => {
                // #* bit-vector
                self.input.next();
                self.read_bit_vector(None)
            }
            Some('a') | Some('A') => {
                // #A requires a numeric prefix
                self.input.next();
                Err(ReaderError::InvalidChar(
                    "Missing rank for #A".to_string(),
                ))
            }
            Some('c') | Some('C') => {
                // #C complex
                self.input.next();
                self.read_complex()
            }
            Some('s') | Some('S') => {
                // #S structure
                self.input.next();
                self.read_structure()
            }
            Some(c) if c.is_ascii_digit() => {
                // #nA, #nR, etc.
                self.read_number_dispatch()
            }
            Some('+') => {
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
            Some('-') => {
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
            Some(c) => {
                if self.read_suppress && (c.is_whitespace() || c == ')' || c == '<') {
                    Err(ReaderError::Unsuppressible(format!(
                        "Invalid dispatch macro: #{}",
                        c
                    )))
                } else {
                    let sub = self.input.next().unwrap();
                    if let Some(func) = self.readtable.get_dispatch_macro_character('#', sub) {
                        return self.read_lisp_dispatch_macro(func, sub, None);
                    }
                    Err(ReaderError::UnexpectedChar(sub))
                }
            }
        }
    }

    fn read_dispatch_table(&mut self, disp: char) -> ReaderResult {
        let mut num_str = String::new();
        while let Some(c) = self.input.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        let num_arg = if num_str.is_empty() {
            None
        } else {
            let n: i64 = num_str
                .parse()
                .map_err(|_| ReaderError::InvalidNumber(num_str.clone()))?;
            Some(n)
        };

        let sub = self.input.next().ok_or(ReaderError::UnexpectedEof)?;
        if let Some(func) = self.readtable.get_dispatch_macro_character(disp, sub) {
            self.read_lisp_dispatch_macro(func, sub, num_arg)
        } else {
            Err(ReaderError::UnexpectedChar(sub))
        }
    }

    fn read_lisp_macro(&mut self, func: NodeId, ch: char) -> ReaderResult {
        let char_node = self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Char(ch)));
        let args_list = self.list(&[self.nil_node, char_node]);

        let result = READ_EVAL_CONTEXT.with(|cell| {
            cell.borrow().as_ref().map(|ctx| unsafe {
                let proc = &mut *ctx.proc_ptr;
                let globals = &*ctx.globals_ptr;
                let env = &*ctx.env_ptr;
                let mut interp = crate::eval::Interpreter::new(proc, globals);
                interp.apply_values(func, args_list, env)
            })
        });

        match result {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => Err(ReaderError::InvalidChar(format!(
                "Reader macro error: {:?}",
                e
            ))),
            None => Err(ReaderError::InvalidChar(
                "Reader macro context not available".to_string(),
            )),
        }
    }

    fn read_lisp_dispatch_macro(
        &mut self,
        func: NodeId,
        ch: char,
        num_arg: Option<i64>,
    ) -> ReaderResult {
        let char_node = self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Char(ch)));
        let num_node = if let Some(n) = num_arg {
            self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n)))
        } else {
            self.nil_node
        };
        let args_list = self.list(&[self.nil_node, char_node, num_node]);

        let result = READ_EVAL_CONTEXT.with(|cell| {
            cell.borrow().as_ref().map(|ctx| unsafe {
                let proc = &mut *ctx.proc_ptr;
                let globals = &*ctx.globals_ptr;
                let env = &*ctx.env_ptr;
                let mut interp = crate::eval::Interpreter::new(proc, globals);
                interp.apply_values(func, args_list, env)
            })
        });

        match result {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => Err(ReaderError::InvalidChar(format!(
                "Reader macro error: {:?}",
                e
            ))),
            None => Err(ReaderError::InvalidChar(
                "Reader macro context not available".to_string(),
            )),
        }
    }

    fn apply_read_function(&mut self, func: NodeId, args: &[NodeId]) -> ReaderResult {
        let args_list = self.list(args);
        let result = READ_EVAL_CONTEXT.with(|cell| {
            cell.borrow().as_ref().map(|ctx| unsafe {
                let proc = &mut *ctx.proc_ptr;
                let globals = &*ctx.globals_ptr;
                let env = &*ctx.env_ptr;
                let mut interp = crate::eval::Interpreter::new(proc, globals);
                interp.apply_values(func, args_list, env)
            })
        });

        match result {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => Err(ReaderError::InvalidChar(format!(
                "Reader macro error: {:?}",
                e
            ))),
            None => Err(ReaderError::InvalidChar(
                "Reader macro context not available".to_string(),
            )),
        }
    }

    fn read_bit_vector(&mut self, len_opt: Option<usize>) -> ReaderResult {
        let mut bits: Vec<char> = Vec::new();
        while let Some(c) = self.input.peek() {
            if c == '0' || c == '1' {
                self.input.next();
                bits.push(c);
            } else {
                break;
            }
        }

        if let Some(len) = len_opt {
            if len == 0 {
                if !bits.is_empty() {
                    return Err(ReaderError::InvalidChar(
                        "Too many bits for #0*".to_string(),
                    ));
                }
            } else {
                if bits.is_empty() {
                    return Err(ReaderError::InvalidChar(
                        "Bit vector literal requires at least one bit".to_string(),
                    ));
                }
                if bits.len() > len {
                    return Err(ReaderError::InvalidChar(
                        "Too many bits for bit-vector length".to_string(),
                    ));
                }
                if bits.len() < len {
                    let fill = *bits.last().unwrap();
                    while bits.len() < len {
                        bits.push(fill);
                    }
                }
            }
        }

        if let Some(store) = self.arrays.as_mut() {
            let mut nodes = Vec::with_capacity(bits.len());
            for b in bits {
                let val = if b == '1' { 1 } else { 0 };
                nodes.push(self.arena.alloc(Node::Leaf(OpaqueValue::Integer(val))));
            }
            let dims = vec![nodes.len()];
            let vec_id = store.alloc_array(dims, nodes, crate::arrays::ArrayElementType::Bit, None);
            Ok(self
                .arena
                .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
        } else {
            Err(ReaderError::InvalidChar(
                "Bit-vectors not supported without ArrayStore".to_string(),
            ))
        }
    }

    fn read_array(&mut self, rank: usize) -> ReaderResult {
        if self.arrays.is_none() {
            return Err(ReaderError::InvalidChar(
                "Arrays not supported without ArrayStore".to_string(),
            ));
        }
        let contents = self.read()?;
        self.array_from_contents(rank, contents)
    }

    fn array_from_contents(&mut self, rank: usize, contents: NodeId) -> ReaderResult {
        let (dims, elements) = self.collect_array_elements(rank, contents)?;
        let store = self.arrays.as_mut().ok_or_else(|| {
            ReaderError::InvalidChar("Arrays not supported without ArrayStore".to_string())
        })?;
        let vec_id = store.alloc_array(dims, elements, crate::arrays::ArrayElementType::T, None);
        Ok(self
            .arena
            .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
    }

    fn collect_array_elements(
        &mut self,
        rank: usize,
        contents: NodeId,
    ) -> Result<(Vec<usize>, Vec<NodeId>), ReaderError> {
        if rank == 0 {
            return Ok((Vec::new(), vec![contents]));
        }

        let elements = self.sequence_to_vec(contents)?;
        if rank == 1 {
            return Ok((vec![elements.len()], elements));
        }

        if elements.is_empty() {
            return Ok((vec![0; rank], Vec::new()));
        }

        let outer_len = elements.len();
        let mut all_elements = Vec::new();
        let mut sub_dims: Option<Vec<usize>> = None;
        for elem in elements {
            let (dims, sub) = self.collect_array_elements(rank - 1, elem)?;
            if let Some(existing) = &sub_dims {
                if *existing != dims {
                    return Err(ReaderError::InvalidChar(
                        "Non-rectangular #A contents".to_string(),
                    ));
                }
            } else {
                sub_dims = Some(dims);
            }
            all_elements.extend(sub);
        }
        let mut dims = Vec::with_capacity(rank);
        dims.push(outer_len);
        dims.extend(sub_dims.unwrap_or_default());
        Ok((dims, all_elements))
    }

    fn sequence_to_vec(&mut self, node: NodeId) -> Result<Vec<NodeId>, ReaderError> {
        match self.arena.get_unchecked(node).clone() {
            Node::Leaf(OpaqueValue::Nil) => Ok(Vec::new()),
            Node::Fork(_, _) => {
                let mut out = Vec::new();
                let mut current = node;
                loop {
                    match self.arena.get_unchecked(current).clone() {
                        Node::Fork(h, t) => {
                            out.push(h);
                            current = t;
                        }
                        Node::Leaf(OpaqueValue::Nil) => break,
                        _ => {
                            return Err(ReaderError::InvalidChar(
                                "Improper list in #A initial contents".to_string(),
                            ))
                        }
                    }
                }
                Ok(out)
            }
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                let store = self.arrays.as_ref().ok_or_else(|| {
                    ReaderError::InvalidChar("Arrays not supported without ArrayStore".to_string())
                })?;
                let arr = store
                    .get(crate::arrays::VectorId(id))
                    .ok_or_else(|| {
                        ReaderError::InvalidChar("Invalid vector handle".to_string())
                    })?;
                Ok(arr.elements_for_sequence())
            }
            Node::Leaf(OpaqueValue::String(s)) => {
                let mut out = Vec::new();
                for ch in s.chars() {
                    out.push(self.arena.alloc(Node::Leaf(OpaqueValue::Char(ch))));
                }
                Ok(out)
            }
            _ => Err(ReaderError::InvalidChar(
                "Invalid initial contents for #A".to_string(),
            )),
        }
    }

    fn read_complex(&mut self) -> ReaderResult {
        let form = self.read()?;
        let (real, imag) = self.expect_pair(form)?;
        if self.is_zero_number(imag) {
            return Ok(real);
        }

        let sym_id = self.symbols.intern_in("COMPLEX", PackageId(1));
        let func = self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)));
        self.apply_read_function(func, &[real, imag])
    }

    fn read_structure(&mut self) -> ReaderResult {
        let form = self.read()?;
        let (name, rest) = self.expect_list_head(form)?;
        let struct_sym = self.symbol_from_designator(name)?;
        let struct_name = self
            .symbols
            .symbol_name(struct_sym)
            .ok_or_else(|| ReaderError::InvalidChar("Invalid structure name".to_string()))?
            .to_string();
        let pkg_id = self
            .symbols
            .symbol_package(struct_sym)
            .unwrap_or_else(|| self.symbols.current_package());

        let mut args = Vec::new();
        if !matches!(self.arena.get_unchecked(rest), Node::Leaf(OpaqueValue::Nil)) {
            let elems = self.sequence_to_vec(rest)?;
            if elems.len() % 2 != 0 {
                return Err(ReaderError::InvalidChar(
                    "Odd number of slot/value pairs in #S".to_string(),
                ));
            }
            for chunk in elems.chunks(2) {
                let key = chunk[0];
                let val = chunk[1];
                let kw = self.keyword_from_designator(key)?;
                args.push(kw);
                args.push(val);
            }
        }

        let ctor_name = format!("MAKE-{}", struct_name);
        let ctor_sym = self.symbols.intern_in(&ctor_name, pkg_id);
        let ctor_node = self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Symbol(ctor_sym.0)));
        self.apply_read_function(ctor_node, &args)
    }

    fn expect_pair(&mut self, node: NodeId) -> Result<(NodeId, NodeId), ReaderError> {
        match self.arena.get_unchecked(node).clone() {
            Node::Fork(a, rest) => match self.arena.get_unchecked(rest).clone() {
                Node::Fork(b, tail) => match self.arena.get_unchecked(tail).clone() {
                    Node::Leaf(OpaqueValue::Nil) => Ok((a, b)),
                    _ => Err(ReaderError::InvalidChar(
                        "Complex literal must have exactly two elements".to_string(),
                    )),
                },
                _ => Err(ReaderError::InvalidChar(
                    "Complex literal must be a list".to_string(),
                )),
            },
            _ => Err(ReaderError::InvalidChar(
                "Complex literal must be a list".to_string(),
            )),
        }
    }

    fn expect_list_head(&mut self, node: NodeId) -> Result<(NodeId, NodeId), ReaderError> {
        match self.arena.get_unchecked(node).clone() {
            Node::Fork(head, tail) => Ok((head, tail)),
            _ => Err(ReaderError::InvalidChar(
                "Structure literal must be a list".to_string(),
            )),
        }
    }

    fn symbol_from_designator(&mut self, node: NodeId) -> Result<SymbolId, ReaderError> {
        match self.arena.get_unchecked(node).clone() {
            Node::Leaf(OpaqueValue::Symbol(id)) => Ok(SymbolId(id)),
            Node::Leaf(OpaqueValue::String(s)) => Ok(self.symbols.intern(&s)),
            Node::Leaf(OpaqueValue::Char(ch)) => Ok(self.symbols.intern(&ch.to_string())),
            Node::Leaf(OpaqueValue::Integer(n)) => {
                let ch = std::char::from_u32(n as u32).ok_or_else(|| {
                    ReaderError::InvalidChar("Invalid character designator".to_string())
                })?;
                Ok(self.symbols.intern(&ch.to_string()))
            }
            _ => Err(ReaderError::InvalidChar(
                "Invalid structure name".to_string(),
            )),
        }
    }

    fn keyword_from_designator(&mut self, node: NodeId) -> Result<NodeId, ReaderError> {
        let sym_id = match self.arena.get_unchecked(node).clone() {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let (is_keyword, name) = {
                    let sym = self
                        .symbols
                        .get_symbol(SymbolId(id))
                        .ok_or_else(|| ReaderError::InvalidChar("Invalid symbol".to_string()))?;
                    (sym.is_keyword(), sym.name.clone())
                };
                if is_keyword {
                    SymbolId(id)
                } else {
                    self.symbols.intern_keyword(&name)
                }
            }
            Node::Leaf(OpaqueValue::String(s)) => self.symbols.intern_keyword(&s),
            Node::Leaf(OpaqueValue::Char(ch)) => self.symbols.intern_keyword(&ch.to_string()),
            Node::Leaf(OpaqueValue::Integer(n)) => {
                let ch = std::char::from_u32(n as u32).ok_or_else(|| {
                    ReaderError::InvalidChar("Invalid character designator".to_string())
                })?;
                self.symbols.intern_keyword(&ch.to_string())
            }
            _ => {
                return Err(ReaderError::InvalidChar(
                    "Invalid slot name designator".to_string(),
                ))
            }
        };
        Ok(self
            .arena
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
    }

    fn is_zero_number(&self, node: NodeId) -> bool {
        match self.arena.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Integer(n)) => *n == 0,
            Node::Leaf(OpaqueValue::BigInt(n)) => n == &num_bigint::BigInt::from(0),
            Node::Leaf(OpaqueValue::Ratio(n, _d)) => n == &num_bigint::BigInt::from(0),
            Node::Leaf(OpaqueValue::Float(f)) => *f == 0.0,
            _ => false,
        }
    }

    /// Read number in specific radix
    fn read_radix(&mut self, radix: u32) -> ReaderResult {
        // Read token
        let s = self.read_symbol_name()?;
        if let Some((num_str, denom_str)) = Self::split_ratio(&s) {
            return match self.parse_ratio(num_str, denom_str, radix)? {
                Some(node) => Ok(node),
                None => Err(ReaderError::InvalidNumber(format!(
                    "Invalid radix {} number: {}",
                    radix, s
                ))),
            };
        }

        if let Some(node) = self.parse_integer_node(&s, radix) {
            return Ok(node);
        }

        Err(ReaderError::InvalidNumber(format!(
            "Invalid radix {} number: {}",
            radix, s
        )))
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
        let (name, _) = self.read_token_with_case(ReadtableCase::Preserve)?;
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

        Ok(self.arena.alloc(Node::Leaf(OpaqueValue::Char(ch))))
    }

    /// Read a vector literal: #(1 2 3)
    fn read_vector(&mut self) -> ReaderResult {
        self.skip_whitespace();

        let mut elements = Vec::new();

        loop {
            self.skip_whitespace();
            match self.input.peek() {
                None => return Err(ReaderError::UnbalancedParen),
                Some(')') => {
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
                Some(']') => {
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
        let mut num_str = String::new();
        while let Some(c) = self.input.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                self.input.next();
            } else {
                break;
            }
        }

        let n: u64 = num_str
            .parse()
            .map_err(|_| ReaderError::InvalidNumber(num_str.clone()))?;

        let dispatch = self.input.next().ok_or(ReaderError::UnexpectedEof)?;
        match dispatch {
            '=' => {
                let placeholder = self.arena.alloc(Node::Leaf(OpaqueValue::Unbound));
                self.label_map.insert(n, placeholder);
                let obj = self.read()?;
                if obj != placeholder {
                    let node = self.arena.get_unchecked(obj).clone();
                    self.arena.overwrite(placeholder, node);
                }
                Ok(placeholder)
            }
            '#' => {
                if let Some(&node) = self.label_map.get(&n) {
                    Ok(node)
                } else {
                    Err(ReaderError::InvalidChar(format!(
                        "Undefined label: #{}#",
                        n
                    )))
                }
            }
            'R' | 'r' => {
                if n < 2 || n > 36 {
                    return Err(ReaderError::InvalidNumber(format!(
                        "Invalid radix: {}",
                        n
                    )));
                }
                let token = self.read_symbol_name()?;
                if let Some((num_str, denom_str)) = Self::split_ratio(&token) {
                    return match self.parse_ratio(num_str, denom_str, n as u32)? {
                        Some(node) => Ok(node),
                        None => Err(ReaderError::InvalidNumber(token)),
                    };
                }
                if let Some(node) = self.parse_integer_node(&token, n as u32) {
                    return Ok(node);
                }
                Err(ReaderError::InvalidNumber(token))
            }
            '*' => {
                let len = usize::try_from(n).map_err(|_| {
                    ReaderError::InvalidNumber(format!("Invalid length: {}", n))
                })?;
                self.read_bit_vector(Some(len))
            }
            'A' | 'a' => {
                let rank = usize::try_from(n).map_err(|_| {
                    ReaderError::InvalidNumber(format!("Invalid rank: {}", n))
                })?;
                self.read_array(rank)
            }
            _ => {
                if let Some(func) = self.readtable.get_dispatch_macro_character('#', dispatch) {
                    let num_arg = i64::try_from(n).map_err(|_| {
                        ReaderError::InvalidNumber(format!("Invalid numeric argument: {}", n))
                    })?;
                    self.read_lisp_dispatch_macro(func, dispatch, Some(num_arg))
                } else {
                    Err(ReaderError::UnexpectedChar(dispatch))
                }
            }
        }
    }

    /// Read an atom (number or symbol)
    fn read_atom(&mut self) -> ReaderResult {
        let (s, escaped) = self.read_symbol_name_with_escapes()?;
        self.parse_atom(&s, escaped)
    }

    /// Read atom with a prefix character
    fn read_atom_with_prefix(&mut self, prefix: char) -> ReaderResult {
        let mut s = String::new();
        s.push(prefix);
        let (rest, escaped) = self.read_symbol_name_with_escapes()?;
        s.push_str(&rest);
        self.parse_atom(&s, escaped)
    }

    /// Read a symbol name (until delimiter)
    fn read_token_with_case(
        &mut self,
        case_mode: ReadtableCase,
    ) -> Result<(String, bool), ReaderError> {
        let mut chars: Vec<(char, bool)> = Vec::new();
        let mut in_multi_escape = false;
        let mut saw_escape = false;

        while let Some(c) = self.input.peek() {
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
                SyntaxType::Whitespace => {
                    if !self.preserve_whitespace {
                        self.input.next();
                    }
                    break;
                }
                SyntaxType::TerminatingMacro => break,
                SyntaxType::SingleEscape => {
                    saw_escape = true;
                    self.input.next();
                    if let Some(escaped) = self.input.next() {
                        chars.push((escaped, true));
                    } else {
                        return Err(ReaderError::UnexpectedEof);
                    }
                }
                SyntaxType::MultiEscape => {
                    saw_escape = true;
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

        let escaped = saw_escape;
        Ok((out, escaped))
    }

    fn read_symbol_name(&mut self) -> Result<String, ReaderError> {
        let case_mode = self.readtable.readtable_case();
        Ok(self.read_token_with_case(case_mode)?.0)
    }

    fn read_symbol_name_with_escapes(&mut self) -> Result<(String, bool), ReaderError> {
        let case_mode = self.readtable.readtable_case();
        self.read_token_with_case(case_mode)
    }

    /// Parse an atom string as number or symbol
    fn parse_atom(&mut self, s: &str, escaped: bool) -> ReaderResult {
        if !escaped {
            if s == "NIL" {
                return Ok(self.nil_node);
            }

            if s.chars().all(|c| c == '.') {
                return Err(ReaderError::InvalidChar("Invalid dot token".to_string()));
            }

            if let Some(num) = self.parse_number(s)? {
                return Ok(num);
            }

            if s.starts_with(':') {
                let key_name = &s[1..];
                let sym_id = self.symbols.intern_keyword(key_name);
                return self.symbol_to_node(sym_id);
            }

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
        }

        let sym_id = self.symbols.intern(s);
        self.symbol_to_node(sym_id)
    }

    fn parse_number(&mut self, s: &str) -> Result<Option<NodeId>, ReaderError> {
        if let Some((num_str, denom_str)) = Self::split_ratio(s) {
            match self.parse_ratio(num_str, denom_str, self.read_base)? {
                Some(node) => return Ok(Some(node)),
                None => {}
            }
        }

        if self.read_base == 10 && self.looks_like_float(s) {
            if let Some(f) = self.parse_float_token(s) {
                return Ok(Some(self.arena.alloc(Node::Leaf(OpaqueValue::Float(f)))));
            }
        }

        if let Some(node) = self.parse_integer_node(s, self.read_base) {
            return Ok(Some(node));
        }

        Ok(None)
    }

    fn split_ratio(s: &str) -> Option<(&str, &str)> {
        let mut parts = s.split('/');
        let first = parts.next()?;
        let second = parts.next()?;
        if parts.next().is_some() {
            return None;
        }
        if first.is_empty() || second.is_empty() {
            return None;
        }
        Some((first, second))
    }

    fn parse_ratio(
        &mut self,
        num_str: &str,
        denom_str: &str,
        base: u32,
    ) -> Result<Option<NodeId>, ReaderError> {
        let (neg, num_digits) = Self::split_sign(num_str);
        if denom_str.starts_with('+') || denom_str.starts_with('-') {
            return Ok(None);
        }

        let mut numerator = match self.parse_bigint_digits(num_digits, base) {
            Some(v) => v,
            None => return Ok(None),
        };
        let mut denominator = match self.parse_bigint_digits(denom_str, base) {
            Some(v) => v,
            None => return Ok(None),
        };

        if denominator == num_bigint::BigInt::from(0) {
            return Err(ReaderError::InvalidNumber(
                "Division by zero".to_string(),
            ));
        }

        if neg {
            numerator = -numerator;
        }

        if denominator.is_negative() {
            numerator = -numerator;
            denominator = -denominator;
        }

        let mut a = numerator.abs();
        let mut b = denominator.abs();
        while b != num_bigint::BigInt::from(0) {
            let r = &a % &b;
            a = b;
            b = r;
        }
        if a != num_bigint::BigInt::from(0) {
            numerator /= &a;
            denominator /= &a;
        }

        if denominator == num_bigint::BigInt::from(1) {
            return Ok(Some(self.bigint_to_node(numerator)));
        }

        Ok(Some(
            self.arena
                .alloc(Node::Leaf(OpaqueValue::Ratio(numerator, denominator))),
        ))
    }

    fn split_sign(s: &str) -> (bool, &str) {
        if let Some(rest) = s.strip_prefix('-') {
            (true, rest)
        } else if let Some(rest) = s.strip_prefix('+') {
            (false, rest)
        } else {
            (false, s)
        }
    }

    fn parse_bigint_digits(&self, s: &str, base: u32) -> Option<num_bigint::BigInt> {
        let s = s.to_ascii_lowercase();
        num_bigint::BigInt::parse_bytes(s.as_bytes(), base)
    }

    fn bigint_to_node(&mut self, n: num_bigint::BigInt) -> NodeId {
        if let Some(v) = n.to_i64() {
            self.arena.alloc(Node::Leaf(OpaqueValue::Integer(v)))
        } else {
            self.arena.alloc(Node::Leaf(OpaqueValue::BigInt(n)))
        }
    }

    fn parse_integer_node(&mut self, s: &str, base: u32) -> Option<NodeId> {
        let (neg, digits) = Self::split_sign(s);
        if digits.is_empty() {
            return None;
        }
        let mut n = self.parse_bigint_digits(digits, base)?;
        if neg {
            n = -n;
        }
        Some(self.bigint_to_node(n))
    }

    fn looks_like_float(&self, s: &str) -> bool {
        s.contains('.')
            || s.chars().any(|c| {
                matches!(
                    c,
                    'e' | 'E' | 'd' | 'D' | 's' | 'S' | 'f' | 'F' | 'l' | 'L'
                )
            })
    }

    fn parse_float_token(&self, s: &str) -> Option<f64> {
        let mut chars = s.chars().peekable();
        let mut sign = String::new();
        if let Some(&c) = chars.peek() {
            if c == '+' || c == '-' {
                sign.push(c);
                chars.next();
            }
        }

        let rest: String = chars.collect();
        if rest.is_empty() {
            return None;
        }

        let mut marker_idx = None;
        let mut marker_char = 'e';
        for (idx, c) in rest.char_indices() {
            if matches!(c, 'e' | 'E' | 'd' | 'D' | 's' | 'S' | 'f' | 'F' | 'l' | 'L') {
                marker_idx = Some(idx);
                marker_char = c;
                break;
            }
        }

        let (mantissa, exponent) = if let Some(idx) = marker_idx {
            let (left, right) = rest.split_at(idx);
            if right.len() < marker_char.len_utf8() + 1 {
                return None;
            }
            let exp_str = &right[marker_char.len_utf8()..];
            if exp_str.is_empty() {
                return None;
            }
            (left, Some(exp_str))
        } else {
            (rest.as_str(), None)
        };

        let mut saw_digit = false;
        let mut saw_dot = false;
        for c in mantissa.chars() {
            if c == '.' {
                if saw_dot {
                    return None;
                }
                saw_dot = true;
            } else if c.is_ascii_digit() {
                saw_digit = true;
            } else {
                return None;
            }
        }
        if !saw_digit {
            return None;
        }

        if marker_idx.is_none() && !saw_dot {
            return None;
        }

        let mut normalized = String::new();
        normalized.push_str(&sign);
        normalized.push_str(mantissa);

        if let Some(exp_str) = exponent {
            let mut exp_chars = exp_str.chars();
            let mut exp_sign = String::new();
            let first = exp_chars.next()?;
            if first == '+' || first == '-' {
                exp_sign.push(first);
            } else {
                exp_sign.push(first);
            }
            let rest_exp: String = exp_chars.collect();
            let exp_digits = if exp_sign == "+" || exp_sign == "-" {
                rest_exp
            } else {
                let mut tmp = exp_sign.clone();
                tmp.push_str(&rest_exp);
                exp_sign = String::new();
                tmp
            };
            if exp_digits.is_empty() || !exp_digits.chars().all(|c| c.is_ascii_digit()) {
                return None;
            }
            normalized.push('e');
            if !exp_sign.is_empty() {
                normalized.push_str(&exp_sign);
            }
            normalized.push_str(&exp_digits);
        }

        normalized.parse::<f64>().ok()
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
