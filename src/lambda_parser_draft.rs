
pub fn parse_lambda_list(&mut self, list_node: NodeId) -> Result<ParsedLambdaList, String> {
    let list_vec = self.cons_to_vec(list_node);
    let mut parsed = ParsedLambdaList::default();

    let mut mode = LambdaListMode::Req;

    // Symbols for keywords
    let syms = self.globals.special_forms.clone();
    // Need to identify &optional, &rest, &key, &aux, &allow-other-keys
    // Problem: Globals doesn't expose them directly?
    // We usually lookup symbol names.

    let mut iter = list_vec.iter();
    while let Some(node) = iter.next() {
        // Check if keyword
        let sym = self.node_to_symbol(*node);

        if let Some(s) = sym {
            if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(s) {
                match name {
                    "&OPTIONAL" => {
                        mode = LambdaListMode::Opt;
                        continue;
                    }
                    "&REST" => {
                        mode = LambdaListMode::Rest;
                        continue;
                    }
                    "&KEY" => {
                        mode = LambdaListMode::Key;
                        continue;
                    }
                    "&AUX" => {
                        mode = LambdaListMode::Aux;
                        continue;
                    }
                    "&ALLOW-OTHER-KEYS" => {
                        if mode != LambdaListMode::Key {
                            return Err("&ALLOW-OTHER-KEYS must follow &KEY".into());
                        }
                        parsed.allow_other_keys = true;
                        continue;
                    }
                    _ => {}
                }
            }
        }

        match mode {
            LambdaListMode::Req => {
                if let Some(s) = self.node_to_symbol(*node) {
                    parsed.req.push(s);
                } else {
                    return Err(format!(
                        "Required argument must be a symbol, got {:?}",
                        node
                    ));
                }
            }
            LambdaListMode::Opt => {
                // Symbol or (var [init [supplied-p]])
                if let Some(s) = self.node_to_symbol(*node) {
                    parsed.opt.push((s, self.process.make_nil(), None));
                } else {
                    // List
                    let parts = self.cons_to_vec(*node);
                    if parts.is_empty() {
                        return Err("Empty optional spec".into());
                    }
                    let var = self
                        .node_to_symbol(parts[0])
                        .ok_or("Optional var must be symbol")?;
                    let init = if parts.len() > 1 {
                        parts[1]
                    } else {
                        self.process.make_nil()
                    };
                    let sup = if parts.len() > 2 {
                        self.node_to_symbol(parts[2])
                    } else {
                        None
                    };
                    parsed.opt.push((var, init, sup));
                }
            }
            LambdaListMode::Rest => {
                if parsed.rest.is_some() {
                    return Err("Multiple &rest arguments".into());
                }
                let s = self
                    .node_to_symbol(*node)
                    .ok_or("&rest argument must be a symbol")?;
                parsed.rest = Some(s);
            }
            LambdaListMode::Key => {
                // Symbol or (var [init [supplied-p]]) or ((keyword var) [init [supplied-p]])
                if let Some(s) = self.node_to_symbol(*node) {
                    // Keyword is derived from var name
                    let name = self
                        .globals
                        .symbols
                        .read()
                        .unwrap()
                        .symbol_name(s)
                        .unwrap()
                        .to_string();
                    // We need a keyword symbol.
                    // Simplification: Match arguments by keyword package symbol with same name?
                    // Or strict: :NAME
                    parsed.key.push((s, s, self.process.make_nil(), None)); // (key, var, ...) using same symbol for key logic for now? No needs Keyword.
                                                                            // Wait, for keys, the matching key is a KEYWORD symbol.
                                                                            // But we store the PARAMETER symbol (var).
                                                                            // We'll resolve the keyword at binding time or now?
                                                                            // Let's resolve now. `intern_keyword(name)`?
                                                                            // But we cannot mutate globals here easily.
                                                                            // We'll store the VAR symbol, and derive the key at bind time?
                                                                            // Better: Store both.
                } else {
                    // List
                    let parts = self.cons_to_vec(*node);
                    let spec = parts[0]; // var or (key var)

                    let (key_sym, var_sym) = if let Some(s) = self.node_to_symbol(spec) {
                        (s, s) // key is derived later
                    } else {
                        let spec_parts = self.cons_to_vec(spec);
                        let k = self
                            .node_to_symbol(spec_parts[0])
                            .ok_or("Key spec key must be symbol")?;
                        let v = self
                            .node_to_symbol(spec_parts[1])
                            .ok_or("Key spec var must be symbol")?;
                        (k, v)
                    };

                    let init = if parts.len() > 1 {
                        parts[1]
                    } else {
                        self.process.make_nil()
                    };
                    let sup = if parts.len() > 2 {
                        self.node_to_symbol(parts[2])
                    } else {
                        None
                    };

                    parsed.key.push((key_sym, var_sym, init, sup));
                }
            }
            LambdaListMode::Aux => {
                // Symbol or (var [init])
                if let Some(s) = self.node_to_symbol(*node) {
                    parsed.aux.push((s, self.process.make_nil()));
                } else {
                    let parts = self.cons_to_vec(*node);
                    let var = self
                        .node_to_symbol(parts[0])
                        .ok_or("Aux var must be symbol")?;
                    let init = if parts.len() > 1 {
                        parts[1]
                    } else {
                        self.process.make_nil()
                    };
                    parsed.aux.push((var, init));
                }
            }
        }
    }

    Ok(parsed)
}

enum LambdaListMode {
    Req,
    Opt,
    Rest,
    Key,
    Aux,
}
