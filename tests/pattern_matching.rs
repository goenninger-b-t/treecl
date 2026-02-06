use treecl::arena::Node;
use treecl::context::GlobalContext;
use treecl::hashtables::{HashTable, TestMode};
use treecl::process::{Pid, Process};
use treecl::symbol::{PackageId, SymbolId};
use treecl::types::{NodeId, OpaqueValue};

fn new_process() -> (GlobalContext, Process) {
    let globals = GlobalContext::new();
    let proc = Process::new(
        Pid {
            node: 0,
            id: 1,
            serial: 0,
        },
        NodeId(0),
        &globals,
    );
    (globals, proc)
}

fn sym_node(proc: &mut Process, sym: SymbolId) -> NodeId {
    proc.arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)))
}

#[test]
fn pattern_repeated_variable_matches() {
    let (globals, mut proc) = new_process();
    let sym_x = globals.symbols.write().unwrap().intern("X");

    let x_node = sym_node(&mut proc, sym_x);
    let pattern = proc.make_list(&[x_node, x_node]);

    let one = proc.make_integer(1);
    let value_ok = proc.make_list(&[one, one]);

    let two = proc.make_integer(2);
    let value_bad = proc.make_list(&[one, two]);

    let symbols = globals.symbols.read().unwrap();
    let quote_sym = globals.special_forms.quote;

    let bindings = treecl::pattern::match_pattern(
        &proc.arena.inner,
        &proc.arrays,
        &proc.hashtables,
        &symbols,
        quote_sym,
        pattern,
        value_ok,
    )
    .expect("pattern should match");

    assert_eq!(bindings.get(&sym_x), Some(&one));

    assert!(treecl::pattern::match_pattern(
        &proc.arena.inner,
        &proc.arrays,
        &proc.hashtables,
        &symbols,
        quote_sym,
        pattern,
        value_bad,
    )
    .is_none());
}

#[test]
fn pattern_wildcard_and_keyword() {
    let (globals, mut proc) = new_process();
    let wildcard = globals.symbols.write().unwrap().intern("_");
    let kw_ok = globals
        .symbols
        .write()
        .unwrap()
        .intern_in("OK", PackageId(0));
    let kw_no = globals
        .symbols
        .write()
        .unwrap()
        .intern_in("NO", PackageId(0));

    let wildcard_node = sym_node(&mut proc, wildcard);
    let kw_ok_node = sym_node(&mut proc, kw_ok);
    let kw_no_node = sym_node(&mut proc, kw_no);

    let pattern = proc.make_list(&[wildcard_node, kw_ok_node]);
    let forty_two = proc.make_integer(42);
    let value_ok = proc.make_list(&[forty_two, kw_ok_node]);
    let value_bad = proc.make_list(&[forty_two, kw_no_node]);

    let symbols = globals.symbols.read().unwrap();
    let quote_sym = globals.special_forms.quote;

    let bindings = treecl::pattern::match_pattern(
        &proc.arena.inner,
        &proc.arrays,
        &proc.hashtables,
        &symbols,
        quote_sym,
        pattern,
        value_ok,
    )
    .expect("pattern should match");

    assert!(bindings.is_empty());

    assert!(treecl::pattern::match_pattern(
        &proc.arena.inner,
        &proc.arrays,
        &proc.hashtables,
        &symbols,
        quote_sym,
        pattern,
        value_bad,
    )
    .is_none());
}

#[test]
fn pattern_quote_literal() {
    let (globals, mut proc) = new_process();
    let sym_x = globals.symbols.write().unwrap().intern("X");

    let quote_node = sym_node(&mut proc, globals.special_forms.quote);
    let x_node = sym_node(&mut proc, sym_x);
    let pattern = proc.make_list(&[quote_node, x_node]);

    let symbols = globals.symbols.read().unwrap();
    let quote_sym = globals.special_forms.quote;

    let bindings = treecl::pattern::match_pattern(
        &proc.arena.inner,
        &proc.arrays,
        &proc.hashtables,
        &symbols,
        quote_sym,
        pattern,
        x_node,
    )
    .expect("quoted literal should match");

    assert!(bindings.is_empty());
}

#[test]
fn pattern_vector_and_map() {
    let (globals, mut proc) = new_process();
    let sym_x = globals.symbols.write().unwrap().intern("X");

    let x_node = sym_node(&mut proc, sym_x);
    let one = proc.make_integer(1);
    let two = proc.make_integer(2);
    let three = proc.make_integer(3);

    let vec_pat = proc
        .arrays
        .alloc_from_vec(vec![x_node, two]);
    let vec_val = proc
        .arrays
        .alloc_from_vec(vec![one, two]);

    let pat_vec_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_pat.0)));
    let val_vec_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_val.0)));

    let quote_sym = globals.special_forms.quote;
    {
        let symbols = globals.symbols.read().unwrap();
        let bindings = treecl::pattern::match_pattern(
            &proc.arena.inner,
            &proc.arrays,
            &proc.hashtables,
            &symbols,
            quote_sym,
            pat_vec_node,
            val_vec_node,
        )
        .expect("vector pattern should match");

        assert_eq!(bindings.get(&sym_x), Some(&one));
    }

    let kw_a = globals
        .symbols
        .write()
        .unwrap()
        .intern_in("A", PackageId(0));
    let kw_b = globals
        .symbols
        .write()
        .unwrap()
        .intern_in("B", PackageId(0));
    let kw_c = globals
        .symbols
        .write()
        .unwrap()
        .intern_in("C", PackageId(0));

    let key_a = sym_node(&mut proc, kw_a);
    let key_b = sym_node(&mut proc, kw_b);
    let key_c = sym_node(&mut proc, kw_c);

    let mut pat_table = HashTable::new(TestMode::Equal);
    pat_table.insert(key_a, x_node, &proc.arena.inner);
    pat_table.insert(key_b, two, &proc.arena.inner);

    let mut val_table = HashTable::new(TestMode::Equal);
    val_table.insert(key_b, two, &proc.arena.inner);
    val_table.insert(key_a, one, &proc.arena.inner);
    val_table.insert(key_c, three, &proc.arena.inner);

    let pat_handle = proc.hashtables.alloc(pat_table);
    let val_handle = proc.hashtables.alloc(val_table);

    let pat_map_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::HashHandle(pat_handle.0)));
    let val_map_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::HashHandle(val_handle.0)));

    {
        let symbols = globals.symbols.read().unwrap();
        let bindings = treecl::pattern::match_pattern(
            &proc.arena.inner,
            &proc.arrays,
            &proc.hashtables,
            &symbols,
            quote_sym,
            pat_map_node,
            val_map_node,
        )
        .expect("map pattern should match");

        assert_eq!(bindings.get(&sym_x), Some(&one));
    }
}
