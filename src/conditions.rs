// TreeCL Condition System - Handlers and Restarts
//
// Implements ANSI CL condition/handler/restart semantics.

use crate::symbol::SymbolId;
use crate::types::NodeId;
use std::collections::HashMap;

/// A condition type (class-like, but simpler)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConditionType(pub u32);

/// A restart
#[derive(Debug, Clone)]
pub struct Restart {
    pub name: SymbolId,
    pub report: Option<String>,
    pub interactive: Option<NodeId>,
    pub test: Option<NodeId>,
    pub function: NodeId,
}

/// A handler binding
#[derive(Debug, Clone)]
pub struct Handler {
    /// Condition type to handle
    pub condition_type: ConditionType,
    /// Handler function
    pub function: NodeId,
}

/// A condition instance
#[derive(Debug, Clone, PartialEq)]
pub struct Condition {
    pub condition_type: ConditionType,
    pub slots: HashMap<SymbolId, NodeId>,
    pub format_control: Option<String>,
    pub format_arguments: Vec<NodeId>,
}

/// The condition system runtime
pub struct ConditionSystem {
    /// Stack of handler clusters (each HANDLER-BIND pushes a cluster)
    handler_stack: Vec<Vec<Handler>>,
    /// Stack of restart clusters (each RESTART-CASE pushes a cluster)
    restart_stack: Vec<Vec<Restart>>,
    /// Built-in condition types
    pub condition_type: ConditionType,
    pub warning_type: ConditionType,
    pub error_type: ConditionType,
    pub serious_condition_type: ConditionType,
    pub simple_condition_type: ConditionType,
    pub simple_error_type: ConditionType,
    pub simple_warning_type: ConditionType,
    /// Type inheritance
    type_parents: HashMap<ConditionType, Vec<ConditionType>>,
}

impl ConditionSystem {
    pub fn new() -> Self {
        let mut sys = Self {
            handler_stack: Vec::new(),
            restart_stack: Vec::new(),
            condition_type: ConditionType(0),
            warning_type: ConditionType(1),
            error_type: ConditionType(2),
            serious_condition_type: ConditionType(3),
            simple_condition_type: ConditionType(4),
            simple_error_type: ConditionType(5),
            simple_warning_type: ConditionType(6),
            type_parents: HashMap::new(),
        };

        // Set up type hierarchy
        // condition <- warning
        sys.type_parents
            .insert(ConditionType(1), vec![ConditionType(0)]);
        // condition <- serious-condition <- error
        sys.type_parents
            .insert(ConditionType(3), vec![ConditionType(0)]);
        sys.type_parents
            .insert(ConditionType(2), vec![ConditionType(3)]);
        // simple-condition <- condition
        sys.type_parents
            .insert(ConditionType(4), vec![ConditionType(0)]);
        // simple-error <- simple-condition, error
        sys.type_parents
            .insert(ConditionType(5), vec![ConditionType(4), ConditionType(2)]);
        // simple-warning <- simple-condition, warning
        sys.type_parents
            .insert(ConditionType(6), vec![ConditionType(4), ConditionType(1)]);

        sys
    }

    /// Push a new handler cluster
    pub fn push_handlers(&mut self, handlers: Vec<Handler>) {
        self.handler_stack.push(handlers);
    }

    /// Pop a handler cluster
    pub fn pop_handlers(&mut self) {
        self.handler_stack.pop();
    }

    /// Push a new restart cluster
    pub fn push_restarts(&mut self, restarts: Vec<Restart>) {
        self.restart_stack.push(restarts);
    }

    /// Pop a restart cluster
    pub fn pop_restarts(&mut self) {
        self.restart_stack.pop();
    }

    /// Check if condition type A is a subtype of B
    pub fn subtypep(&self, a: ConditionType, b: ConditionType) -> bool {
        if a == b {
            return true;
        }

        if let Some(parents) = self.type_parents.get(&a) {
            for &parent in parents {
                if self.subtypep(parent, b) {
                    return true;
                }
            }
        }

        false
    }

    pub fn handler_stack(&self) -> &Vec<Vec<Handler>> {
        &self.handler_stack
    }

    pub fn restart_stack(&self) -> &Vec<Vec<Restart>> {
        &self.restart_stack
    }

    /// Find applicable handlers for a condition
    pub fn find_handlers(&self, condition: &Condition) -> Vec<&Handler> {
        let mut result = Vec::new();

        // Search from innermost to outermost
        for cluster in self.handler_stack.iter().rev() {
            for handler in cluster {
                if self.subtypep(condition.condition_type, handler.condition_type) {
                    result.push(handler);
                }
            }
        }

        result
    }

    /// Find all active restarts
    pub fn find_restarts(&self) -> Vec<&Restart> {
        let mut result = Vec::new();

        for cluster in self.restart_stack.iter().rev() {
            for restart in cluster {
                result.push(restart);
            }
        }

        result
    }

    /// Find a restart by name
    pub fn find_restart(&self, name: SymbolId) -> Option<&Restart> {
        for cluster in self.restart_stack.iter().rev() {
            for restart in cluster {
                if restart.name == name {
                    return Some(restart);
                }
            }
        }
        None
    }

    /// Make a simple condition
    pub fn make_condition(&self, typ: ConditionType) -> Condition {
        Condition {
            condition_type: typ,
            slots: HashMap::new(),
            format_control: None,
            format_arguments: Vec::new(),
        }
    }

    /// Make a simple error with format string
    pub fn make_simple_error(&self, format: &str, args: Vec<NodeId>) -> Condition {
        Condition {
            condition_type: self.simple_error_type,
            slots: HashMap::new(),
            format_control: Some(format.to_string()),
            format_arguments: args,
        }
    }

    /// Make a simple warning with format string
    pub fn make_simple_warning(&self, format: &str, args: Vec<NodeId>) -> Condition {
        Condition {
            condition_type: self.simple_warning_type,
            slots: HashMap::new(),
            format_control: Some(format.to_string()),
            format_arguments: args,
        }
    }
    /// Get GC roots (functions in handlers and restarts)
    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        for cluster in &self.handler_stack {
            for handler in cluster {
                roots.push(handler.function);
            }
        }

        for cluster in &self.restart_stack {
            for restart in cluster {
                roots.push(restart.function);
                if let Some(node) = restart.interactive {
                    roots.push(node);
                }
                if let Some(node) = restart.test {
                    roots.push(node);
                }
            }
        }
        roots
    }
}

impl Default for ConditionSystem {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_condition_type_hierarchy() {
        let sys = ConditionSystem::new();

        // Error is a subtype of serious-condition
        assert!(sys.subtypep(sys.error_type, sys.serious_condition_type));

        // Error is a subtype of condition
        assert!(sys.subtypep(sys.error_type, sys.condition_type));

        // Warning is a subtype of condition
        assert!(sys.subtypep(sys.warning_type, sys.condition_type));

        // Error is not a subtype of warning
        assert!(!sys.subtypep(sys.error_type, sys.warning_type));
    }

    #[test]
    fn test_handler_binding() {
        let mut sys = ConditionSystem::new();

        sys.push_handlers(vec![Handler {
            condition_type: sys.error_type,
            function: NodeId(1),
        }]);

        let error = sys.make_condition(sys.error_type);
        let handlers = sys.find_handlers(&error);

        assert_eq!(handlers.len(), 1);
        assert_eq!(handlers[0].function, NodeId(1));

        sys.pop_handlers();
        assert!(sys.find_handlers(&error).is_empty());
    }

    #[test]
    fn test_restart_binding() {
        let mut sys = ConditionSystem::new();

        let restart_name = SymbolId(42);

        sys.push_restarts(vec![Restart {
            name: restart_name,
            report: Some("Continue anyway".to_string()),
            interactive: None,
            test: None,
            function: NodeId(10),
        }]);

        let restart = sys.find_restart(restart_name);
        assert!(restart.is_some());
        assert_eq!(restart.unwrap().function, NodeId(10));

        sys.pop_restarts();
        assert!(sys.find_restart(restart_name).is_none());
    }

    #[test]
    fn test_nested_handlers() {
        let mut sys = ConditionSystem::new();

        sys.push_handlers(vec![Handler {
            condition_type: sys.condition_type,
            function: NodeId(1),
        }]);

        sys.push_handlers(vec![Handler {
            condition_type: sys.error_type,
            function: NodeId(2),
        }]);

        let error = sys.make_condition(sys.error_type);
        let handlers = sys.find_handlers(&error);

        // Should find both handlers (error is subtype of condition)
        // Inner handler should come first
        assert_eq!(handlers.len(), 2);
        assert_eq!(handlers[0].function, NodeId(2));
        assert_eq!(handlers[1].function, NodeId(1));
    }
}
