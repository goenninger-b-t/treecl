use treecl::arena::Node;
use treecl::context::GlobalContext;
use treecl::eval::{ControlSignal, Environment, Interpreter};
use treecl::process::{Pid, Process};
use treecl::types::{NodeId, OpaqueValue};

fn new_process() -> (GlobalContext, Process) {
    let mut globals = GlobalContext::new();
    treecl::primitives::register_primitives(&mut globals);
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

fn eval_string(
    input: &str,
    proc: &mut Process,
    globals: &GlobalContext,
) -> Result<NodeId, ControlSignal> {
    let expr = treecl::reader::read_from_string(
        input,
        &mut proc.arena.inner,
        &mut *globals.symbols.write().unwrap(),
    )
    .unwrap();
    let mut interpreter = Interpreter::new(proc, globals);
    interpreter.eval(expr, &Environment::new())
}

fn list_to_vec(proc: &Process, list: NodeId) -> Vec<NodeId> {
    let mut items = Vec::new();
    let mut current = list;
    loop {
        match proc.arena.inner.get_unchecked(current) {
            Node::Fork(head, tail) => {
                items.push(*head);
                current = *tail;
            }
            Node::Leaf(OpaqueValue::Nil) => break,
            _ => panic!("expected proper list"),
        }
    }
    items
}

fn assert_int(proc: &Process, node: NodeId, expected: i64) {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Integer(val)) => assert_eq!(*val, expected),
        other => panic!("expected integer, got {:?}", other),
    }
}

#[test]
fn macro_destructuring_nested_optional_key() {
    let (globals, mut proc) = new_process();

    let program = "(progn\
        (defmacro m ((a &optional b &key (c 9)) &optional (d 5))\
          (list 'list a b c d))\
        (m (1 2 :c 3) 4))";

    let result = eval_string(program, &mut proc, &globals).expect("macro eval failed");
    let items = list_to_vec(&proc, result);
    assert_eq!(items.len(), 4);
    assert_int(&proc, items[0], 1);
    assert_int(&proc, items[1], 2);
    assert_int(&proc, items[2], 3);
    assert_int(&proc, items[3], 4);
}

#[test]
fn macro_destructuring_defaults() {
    let (globals, mut proc) = new_process();

    let program = "(progn\
        (defmacro m ((a &optional b &key (c 9)) &optional (d 5))\
          (list 'list a b c d))\
        (m (1)))";

    let result = eval_string(program, &mut proc, &globals).expect("macro eval failed");
    let items = list_to_vec(&proc, result);
    assert_eq!(items.len(), 4);
    assert_int(&proc, items[0], 1);
    assert!(matches!(
        proc.arena.inner.get_unchecked(items[1]),
        Node::Leaf(OpaqueValue::Nil)
    ));
    assert_int(&proc, items[2], 9);
    assert_int(&proc, items[3], 5);
}

#[test]
fn macro_destructuring_unknown_keyword_rejected() {
    let (globals, mut proc) = new_process();

    let program = "(progn\
        (defmacro m ((a &key b))\
          (list 'list a b))\
        (m (1 :x 2)))";

    let result = eval_string(program, &mut proc, &globals);
    assert!(matches!(result, Err(ControlSignal::Error(_))));
}
