use crate::arena::{Arena, Node};
use crate::arrays::ArrayStore;
use crate::hashtables::HashTableStore;
use crate::search::{reduce, EvalContext};
use crate::symbol::{SymbolId, SymbolTable};
use crate::tree_calculus;
use crate::types::{NodeId, OpaqueValue};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    Leaf,
    Stem,
    Fork,
}

pub struct ShapeClassifier {
    arena: Arena,
    ctx: EvalContext,
    triage_apply: NodeId,
    leaf_shape: NodeId,
    stem_shape: NodeId,
    fork_shape: NodeId,
}

impl ShapeClassifier {
    pub fn new() -> Self {
        let mut arena = Arena::new();
        let ctx = EvalContext::new();
        let delta = tree_calculus::delta(&mut arena);
        let triage = tree_calculus::triage_comb(&mut arena);
        let k_node = tree_calculus::k(&mut arena);

        let tag_leaf = tree_calculus::numeral(&mut arena, 0);
        let tag_stem = tree_calculus::numeral(&mut arena, 1);
        let tag_fork = tree_calculus::numeral(&mut arena, 2);

        let f0 = tag_leaf;
        let f1 = tree_calculus::app(&mut arena, k_node, tag_stem);
        let kk = tree_calculus::app(&mut arena, k_node, tag_fork);
        let f2 = tree_calculus::app(&mut arena, k_node, kk);

        let triage_f0 = tree_calculus::app(&mut arena, triage, f0);
        let triage_f0_f1 = tree_calculus::app(&mut arena, triage_f0, f1);
        let triage_apply = tree_calculus::app(&mut arena, triage_f0_f1, f2);

        let leaf_shape = delta;
        let stem_shape = tree_calculus::app(&mut arena, delta, delta);
        let fork_shape = tree_calculus::app(&mut arena, k_node, delta);

        Self {
            arena,
            ctx,
            triage_apply,
            leaf_shape,
            stem_shape,
            fork_shape,
        }
    }

    pub fn classify(&mut self, source: &Arena, node: NodeId) -> Shape {
        let shape_node = match source.get_unchecked(node) {
            Node::Leaf(_) => self.leaf_shape,
            Node::Stem(_) => self.stem_shape,
            Node::Fork(_, _) => self.fork_shape,
        };

        let term = tree_calculus::app(&mut self.arena, self.triage_apply, shape_node);
        let reduced = reduce(&mut self.arena, term, &mut self.ctx);

        match tree_calculus::decode_nat(&self.arena, reduced) {
            Some(0) => Shape::Leaf,
            Some(1) => Shape::Stem,
            Some(2) => Shape::Fork,
            _ => match source.get_unchecked(node) {
                Node::Leaf(_) => Shape::Leaf,
                Node::Stem(_) => Shape::Stem,
                Node::Fork(_, _) => Shape::Fork,
            },
        }
    }
}

pub fn literal_equal(
    arena: &Arena,
    arrays: &ArrayStore,
    hashtables: &HashTableStore,
    a: NodeId,
    b: NodeId,
) -> bool {
    let mut shape = ShapeClassifier::new();
    literal_equal_internal(arena, arrays, hashtables, &mut shape, a, b)
}

pub fn match_pattern(
    arena: &Arena,
    arrays: &ArrayStore,
    hashtables: &HashTableStore,
    symbols: &SymbolTable,
    quote_sym: SymbolId,
    pattern: NodeId,
    value: NodeId,
) -> Option<HashMap<SymbolId, NodeId>> {
    let mut matcher = PatternMatcher::new(arena, arrays, hashtables, symbols, quote_sym);
    if matcher.match_node(pattern, value, true) {
        Some(matcher.bindings)
    } else {
        None
    }
}

struct PatternMatcher<'a> {
    arena: &'a Arena,
    arrays: &'a ArrayStore,
    hashtables: &'a HashTableStore,
    symbols: &'a SymbolTable,
    quote_sym: SymbolId,
    bindings: HashMap<SymbolId, NodeId>,
    bind_stack: Vec<SymbolId>,
    shape: ShapeClassifier,
}

impl<'a> PatternMatcher<'a> {
    fn new(
        arena: &'a Arena,
        arrays: &'a ArrayStore,
        hashtables: &'a HashTableStore,
        symbols: &'a SymbolTable,
        quote_sym: SymbolId,
    ) -> Self {
        Self {
            arena,
            arrays,
            hashtables,
            symbols,
            quote_sym,
            bindings: HashMap::new(),
            bind_stack: Vec::new(),
            shape: ShapeClassifier::new(),
        }
    }

    fn rollback(&mut self, checkpoint: usize) {
        while self.bind_stack.len() > checkpoint {
            if let Some(sym) = self.bind_stack.pop() {
                self.bindings.remove(&sym);
            }
        }
    }

    fn is_nil(&self, node: NodeId) -> bool {
        matches!(self.arena.get_unchecked(node), Node::Leaf(OpaqueValue::Nil))
    }

    fn symbol_name(&self, sym: SymbolId) -> Option<&str> {
        self.symbols.symbol_name(sym)
    }

    fn is_keyword(&self, sym: SymbolId) -> bool {
        self.symbols
            .get_symbol(sym)
            .map(|s| s.is_keyword())
            .unwrap_or(false)
    }

    fn is_wildcard(&self, sym: SymbolId) -> bool {
        self.symbol_name(sym)
            .map(|name| name == "_")
            .unwrap_or(false)
    }

    fn quoted_literal(&self, pattern: NodeId) -> Option<NodeId> {
        let Node::Fork(head, tail) = self.arena.get_unchecked(pattern) else {
            return None;
        };
        let Node::Leaf(OpaqueValue::Symbol(sym)) = self.arena.get_unchecked(*head) else {
            return None;
        };
        if SymbolId(*sym) != self.quote_sym {
            return None;
        }
        match self.arena.get_unchecked(*tail) {
            Node::Fork(arg, rest) if self.is_nil(*rest) => Some(*arg),
            _ => None,
        }
    }

    fn match_symbol(&mut self, sym: SymbolId, value: NodeId, allow_bind: bool) -> bool {
        if !allow_bind {
            return self.match_literal_symbol(sym, value);
        }
        if self.is_wildcard(sym) {
            return true;
        }
        if self.is_keyword(sym) {
            return self.match_literal_symbol(sym, value);
        }
        if let Some(bound) = self.bindings.get(&sym) {
            return self.match_node_literal(*bound, value);
        }
        self.bindings.insert(sym, value);
        self.bind_stack.push(sym);
        true
    }

    fn match_literal_symbol(&self, sym: SymbolId, value: NodeId) -> bool {
        match self.arena.get_unchecked(value) {
            Node::Leaf(OpaqueValue::Symbol(val_sym)) => *val_sym == sym.0,
            _ => false,
        }
    }

    fn match_vector(&mut self, pat_vec: u32, value: NodeId, allow_bind: bool) -> bool {
        let Node::Leaf(OpaqueValue::VectorHandle(val_vec)) = self.arena.get_unchecked(value) else {
            return false;
        };
        let Some(pat_items) = self.arrays.get(crate::arrays::VectorId(pat_vec)) else {
            return false;
        };
        let Some(val_items) = self.arrays.get(crate::arrays::VectorId(*val_vec)) else {
            return false;
        };
        if pat_items.len() != val_items.len() {
            return false;
        }
        let checkpoint = self.bind_stack.len();
        for (p, v) in pat_items.iter().zip(val_items.iter()) {
            if !self.match_node(*p, *v, allow_bind) {
                self.rollback(checkpoint);
                return false;
            }
        }
        true
    }

    fn match_map_key(&mut self, key_pat: NodeId, key_val: NodeId) -> bool {
        if let Node::Leaf(OpaqueValue::Symbol(sym)) = self.arena.get_unchecked(key_pat) {
            let sym_id = SymbolId(*sym);
            if self.is_wildcard(sym_id) {
                return false;
            }
            if self.is_keyword(sym_id) {
                return self.match_literal_symbol(sym_id, key_val);
            }
            if let Some(bound) = self.bindings.get(&sym_id) {
                return self.match_node_literal(*bound, key_val);
            }
            return false;
        }
        self.match_node(key_pat, key_val, false)
    }

    fn match_map(&mut self, pat_map: u32, value: NodeId, allow_bind: bool) -> bool {
        let Node::Leaf(OpaqueValue::HashHandle(val_map)) = self.arena.get_unchecked(value) else {
            return false;
        };
        let Some(pat_table) = self.hashtables.get(crate::types::HashHandle(pat_map)) else {
            return false;
        };
        let Some(val_table) = self.hashtables.get(crate::types::HashHandle(*val_map)) else {
            return false;
        };
        if pat_table.entries.is_empty() {
            return true;
        }

        let checkpoint = self.bind_stack.len();
        let mut used = vec![false; val_table.entries.len()];

        for (p_key, p_val) in &pat_table.entries {
            let mut matched = false;
            for (idx, (v_key, v_val)) in val_table.entries.iter().enumerate() {
                if used[idx] {
                    continue;
                }
                let attempt_checkpoint = self.bind_stack.len();
                if self.match_map_key(*p_key, *v_key)
                    && self.match_node(*p_val, *v_val, allow_bind)
                {
                    used[idx] = true;
                    matched = true;
                    break;
                }
                self.rollback(attempt_checkpoint);
            }
            if !matched {
                self.rollback(checkpoint);
                return false;
            }
        }
        true
    }

    fn match_node(&mut self, pattern: NodeId, value: NodeId, allow_bind: bool) -> bool {
        if !allow_bind && pattern == value {
            return true;
        }
        if let Some(lit) = self.quoted_literal(pattern) {
            return self.match_node(lit, value, false);
        }

        match self.shape.classify(self.arena, pattern) {
            Shape::Leaf => match self.arena.get_unchecked(pattern) {
                Node::Leaf(OpaqueValue::Symbol(sym)) => {
                    self.match_symbol(SymbolId(*sym), value, allow_bind)
                }
                Node::Leaf(OpaqueValue::VectorHandle(vec_id)) => {
                    self.match_vector(*vec_id, value, allow_bind)
                }
                Node::Leaf(OpaqueValue::HashHandle(map_id)) => {
                    self.match_map(*map_id, value, allow_bind)
                }
                Node::Leaf(_) => self.match_node_literal(pattern, value),
                _ => false,
            },
            Shape::Stem => {
                if self.shape.classify(self.arena, value) != Shape::Stem {
                    return false;
                }
                match (self.arena.get_unchecked(pattern), self.arena.get_unchecked(value)) {
                    (Node::Stem(p_inner), Node::Stem(v_inner)) => {
                        let checkpoint = self.bind_stack.len();
                        let ok = self.match_node(*p_inner, *v_inner, allow_bind);
                        if !ok {
                            self.rollback(checkpoint);
                        }
                        ok
                    }
                    _ => false,
                }
            }
            Shape::Fork => {
                if self.shape.classify(self.arena, value) != Shape::Fork {
                    return false;
                }
                match (self.arena.get_unchecked(pattern), self.arena.get_unchecked(value)) {
                    (Node::Fork(p_left, p_right), Node::Fork(v_left, v_right)) => {
                        let checkpoint = self.bind_stack.len();
                        if self.match_node(*p_left, *v_left, allow_bind)
                            && self.match_node(*p_right, *v_right, allow_bind)
                        {
                            true
                        } else {
                            self.rollback(checkpoint);
                            false
                        }
                    }
                    _ => false,
                }
            }
        }
    }

    fn match_node_literal(&self, pattern: NodeId, value: NodeId) -> bool {
        let mut shape = ShapeClassifier::new();
        literal_equal_internal(
            self.arena,
            self.arrays,
            self.hashtables,
            &mut shape,
            pattern,
            value,
        )
    }
}

fn literal_equal_internal(
    arena: &Arena,
    arrays: &ArrayStore,
    hashtables: &HashTableStore,
    shape: &mut ShapeClassifier,
    pattern: NodeId,
    value: NodeId,
) -> bool {
    if pattern == value {
        return true;
    }
    let shape_pat = shape.classify(arena, pattern);
    let shape_val = shape.classify(arena, value);
    if shape_pat != shape_val {
        return false;
    }
    match shape_pat {
        Shape::Leaf => match (arena.get_unchecked(pattern), arena.get_unchecked(value)) {
            (Node::Leaf(OpaqueValue::VectorHandle(a)), Node::Leaf(OpaqueValue::VectorHandle(b))) => {
                let Some(a_items) = arrays.get(crate::arrays::VectorId(*a)) else {
                    return false;
                };
                let Some(b_items) = arrays.get(crate::arrays::VectorId(*b)) else {
                    return false;
                };
                if a_items.len() != b_items.len() {
                    return false;
                }
                a_items.iter().zip(b_items.iter()).all(|(a_item, b_item)| {
                    literal_equal_internal(arena, arrays, hashtables, shape, *a_item, *b_item)
                })
            }
            (Node::Leaf(OpaqueValue::HashHandle(a)), Node::Leaf(OpaqueValue::HashHandle(b))) => {
                let Some(a_table) = hashtables.get(crate::types::HashHandle(*a)) else {
                    return false;
                };
                let Some(b_table) = hashtables.get(crate::types::HashHandle(*b)) else {
                    return false;
                };
                if a_table.entries.len() != b_table.entries.len() {
                    return false;
                }
                a_table.entries.iter().all(|(ak, av)| {
                    b_table.entries.iter().any(|(bk, bv)| {
                        literal_equal_internal(arena, arrays, hashtables, shape, *ak, *bk)
                            && literal_equal_internal(arena, arrays, hashtables, shape, *av, *bv)
                    })
                })
            }
            (Node::Leaf(a), Node::Leaf(b)) => a == b,
            _ => false,
        },
        Shape::Stem => match (arena.get_unchecked(pattern), arena.get_unchecked(value)) {
            (Node::Stem(a), Node::Stem(b)) => {
                literal_equal_internal(arena, arrays, hashtables, shape, *a, *b)
            }
            _ => false,
        },
        Shape::Fork => match (arena.get_unchecked(pattern), arena.get_unchecked(value)) {
            (Node::Fork(a1, a2), Node::Fork(b1, b2)) => {
                literal_equal_internal(arena, arrays, hashtables, shape, *a1, *b1)
                    && literal_equal_internal(arena, arrays, hashtables, shape, *a2, *b2)
            }
            _ => false,
        },
    }
}
