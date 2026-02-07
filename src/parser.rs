use crate::arena::{Graph, Node, NodeId};

use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Symbol(String),
    String(String),
}

struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() || c == ',' {
                self.chars.next();
                continue;
            }
            match c {
                '(' => {
                    self.chars.next();
                    return Some(Token::LParen);
                }
                ')' => {
                    self.chars.next();
                    return Some(Token::RParen);
                }
                ';' => {
                    // Comment
                    while let Some(&c) = self.chars.peek() {
                        if c == '\n' { break; }
                        self.chars.next();
                    }
                    continue;
                }
                '"' => {
                    // String literal
                    self.chars.next(); // eat "
                    let mut s = String::new();
                    while let Some(&c) = self.chars.peek() {
                        if c == '"' {
                            self.chars.next(); // eat "
                            return Some(Token::String(s));
                        }
                        if c == '\\' {
                             self.chars.next(); // eat \
                             if let Some(&next_c) = self.chars.peek() {
                                 match next_c {
                                     'n' => s.push('\n'),
                                     't' => s.push('\t'),
                                     '"' => s.push('"'),
                                     '\\' => s.push('\\'),
                                     _ => s.push(next_c),
                                 }
                                 self.chars.next(); // eat escaped char
                             }
                        } else {
                             s.push(c);
                             self.chars.next();
                        }
                    }
                    // EOF inside string?
                    return Some(Token::String(s));
                }
                _ => {
                    // Symbol
                    let mut s = String::new();
                    while let Some(&c) = self.chars.peek() {
                        if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                            break;
                        }
                        s.push(c);
                        self.chars.next();
                    }
                    return Some(Token::Symbol(s));
                }
            }
        }
        None
    }
}

use crate::fastmap::HashMap;

pub struct Parser<'a> {
    undo: Option<Token>,
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            undo: None,
            lexer: Lexer::new(input),
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if self.undo.is_none() {
            self.undo = self.lexer.next_token();
        }
        self.undo.as_ref()
    }

    fn consume(&mut self) -> Option<Token> {
        if let Some(t) = self.undo.take() {
            Some(t)
        } else {
            self.lexer.next_token()
        }
    }

    fn parse_list_inner(&mut self, g: &mut Graph, env: Option<&HashMap<String, NodeId>>, bound: &[String]) -> Result<crate::compiler::CompileTerm, String> {
        use crate::compiler::CompileTerm;
        use crate::parser::Token;
        
        // Check if special form
        // Peek first token
        if let Some(Token::Symbol(s)) = self.peek() {
            if s == "fn" {
                self.consume(); // eat fn
                // (fn x body)
                let param = match self.consume() {
                    Some(Token::Symbol(p)) => p,
                    _ => return Err("Expected param symbol after fn".to_string()),
                };
                
                let mut new_bound = bound.to_vec();
                new_bound.push(param.clone());
                
                let body = self.parse_expr(g, env, &new_bound)?;
                
                match self.consume() {
                    Some(Token::RParen) => return Ok(CompileTerm::Lam(param, Box::new(body))),
                    _ => return Err("Expected ) after fn body".to_string()),
                }
            }
        }
        
        // Application
        let head = self.parse_expr(g, env, bound)?; // Removed mut head
        let mut args = Vec::new();
        
        loop {
            if let Some(Token::RParen) = self.peek() {
                self.consume();
                break;
            }
            if self.peek().is_none() {
                 return Err("Unexpected EOF inside list".to_string());
            }
            args.push(self.parse_expr(g, env, bound)?);
        }
        
        let mut res = head;
        for arg in args {
            res = CompileTerm::App(Box::new(res), Box::new(arg));
        }
        Ok(res)
    }

    pub fn parse_expr(&mut self, g: &mut Graph, env: Option<&HashMap<String, NodeId>>, bound: &[String]) -> Result<crate::compiler::CompileTerm, String> {
        use crate::compiler::CompileTerm;
        match self.consume() {
            Some(Token::Symbol(s)) => {
                // Check bound vars first
                if bound.contains(&s) {
                    return Ok(CompileTerm::Var(s));
                }
                
                // Literals
                 if s == "n" {
                      return Ok(CompileTerm::Const(g.add(Node::Leaf)));
                 }
                 use num_bigint::BigInt;
                 if let Ok(n) = s.parse::<BigInt>() {
                      let id = crate::engine::encode_int(g, &n);
                      return Ok(CompileTerm::Const(id));
                 }
                 
                 // Try parsing as Float
                 if let Ok(f) = s.parse::<f64>() {
                      return Ok(CompileTerm::Const(g.add(Node::Float(f))));
                 }
                 
                 // Env lookup
                 if let Some(e) = env {
                    if let Some(&id) = e.get(&s) {
                         return Ok(CompileTerm::Const(id));
                    }
                 }
                 
                 Err(format!("Unknown symbol: {}", s))
            }
            Some(Token::String(s)) => {
                let id = crate::engine::encode_str(g, &s);
                Ok(CompileTerm::Const(id))
            }
            Some(Token::LParen) => {
                self.parse_list_inner(g, env, bound)
            }
            Some(Token::RParen) => Err("Unexpected )".to_string()),
            None => Err("Unexpected EOF".to_string()),
        }
    }

    pub fn parse_toplevel(&mut self, g: &mut Graph, env: Option<&HashMap<String, NodeId>>) -> Result<ParseResult, String> {
        // Check for (def name value)
        match self.peek() {
            Some(Token::LParen) => {
                self.consume(); // eat (
                
                // Peek next
                if let Some(Token::Symbol(s)) = self.peek() {
                    if s == "def" {
                        self.consume(); // eat def
                        
                        // Parse name
                        let name = match self.consume() {
                            Some(Token::Symbol(s)) => s,
                            _ => return Err("Expected symbol after def".to_string()),
                        };
                        
                        let expr = self.parse_expr(g, env, &[])?;
                        let val = crate::compiler::compile(g, expr)?;
                        
                        match self.consume() {
                            Some(Token::RParen) => return Ok(ParseResult::Def(name, val)),
                            _ => return Err("Expected ) after def".to_string()),
                        }
                    }
                }
                
                // Not special form, proceed as Term application
                // We already consumed '(', parse_list_inner handles the rest
                let expr = self.parse_list_inner(g, env, &[])?;
                let val = crate::compiler::compile(g, expr)?;
                Ok(ParseResult::Term(val))
            }
            _ => {
                // Not a list, simple term
                let expr = self.parse_expr(g, env, &[])?;
                let val = crate::compiler::compile(g, expr)?;
                Ok(ParseResult::Term(val))
            }
        }
    }
}

pub enum ParseResult {
    Term(NodeId),
    Def(String, NodeId),
}
