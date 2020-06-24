// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;
use crate::{
    function_target::FunctionTargetData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
};
use spec_lang::{
    ast::{
        Condition,
        ConditionKind,
        Exp,
        Spec,
        Value,
        Operation,
        LocalVarDecl,
    },
    env::{
        NodeId,
        Loc,
        ConditionInfo,
        FunctionEnv,
        StructEnv,
        FieldEnv,
        VerificationScope,
        ALWAYS_ABORTS_TEST_PRAGMA,
        CONST_EXP_TEST_PRAGMA,
    },
    ty::{
        Type,
        BOOL_TYPE,
        ADDRESS_TYPE,
        RANGE_TYPE,
    },
    symbol::Symbol,
};

/// A function target processor which instruments specifications and code for the purpose
/// of specification testing.
pub struct TestInstrumenter {
    verification_scope: VerificationScope,
}

impl TestInstrumenter {
    /// Creates a new test instrumenter.
    pub fn new(verification_scope: VerificationScope) -> Box<Self> {
        Box::new(TestInstrumenter { verification_scope })
    }
}

impl FunctionTargetProcessor for TestInstrumenter {
    /// Implements the FunctionTargetProcessor trait.
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv<'_>,
        mut data: FunctionTargetData,
    ) -> FunctionTargetData {
        if !func_env.should_verify(self.verification_scope) {
            // Do not instrument if function is in verification scope.
            return data;
        }
        if func_env.is_pragma_true(ALWAYS_ABORTS_TEST_PRAGMA, || false) {
            self.instrument_always_aborts(func_env, &mut data);
        }
        if func_env.is_pragma_true(CONST_EXP_TEST_PRAGMA, || false) {
            self.instrument_const_exp(func_env, &mut data);
        }
        data
    }
}

// ==============================================================================
// Aborts If Test Instrumentation

impl TestInstrumenter {
    /// Instrument the function to check whether it always aborts. This drops existing spec
    /// conditions and adds a single `aborts_if true` condition. This is marked as "negative",
    /// letting the boogie wrapper check whether it was not violated, this way identifying whether
    /// a function always aborts.
    fn instrument_always_aborts(&self, func_env: &FunctionEnv<'_>, data: &mut FunctionTargetData) {
        let mut conds = vec![];
        // Keep the preconditions
        conds.append(&mut self.get_smoke_test_preconditions(func_env));
        // Override specification with `aborts_if true`.
        let cond = self.make_condition(
            func_env.get_loc(),
            ConditionKind::EnsuresSmokeTest,
            self.make_abort_flag_bool_exp(func_env),
        );
        let cond_loc = cond.loc.clone();
        conds.push(cond);
        let spec = Spec {
            conditions: conds,
            properties: Default::default(),
            on_impl: Default::default(),
        };
        data.rewritten_spec = Some(spec);
        // Add ConditionInfo to global environment for backend error reporting.
        let info = ConditionInfo {
            message: "function always aborts".to_string(),
            omit_trace: true,    // no error trace needed
            negative_cond: true, // this is a negative condition: we report above error if it passes
        };
        // Register the condition info for location we assigned to the condition. This way the
        // backend will find it.
        func_env.module_env.env.set_condition_info(cond_loc, info);
    }
}

// ==============================================================================
// Constant global struct expression Instrumentation

impl TestInstrumenter {
    /// Instrument the function to check whether there are constant global expressions.
    fn instrument_const_exp(&self, func_env: &FunctionEnv<'_>, data: &mut FunctionTargetData) {
        let mut conds = vec![];
        // Keep the precondtions
        conds.append(&mut self.get_smoke_test_preconditions(func_env));
        // For every struct, add condition that struct fields don't change
        let struct_envs = func_env
            .module_env
            .get_structs();
        for struct_env in struct_envs {
            // TODO: Why is this 1 when it's empty?
            if struct_env.get_field_count() == 1 {
                continue;
            }
            // Check if the struct generics are contained in the function's
            let func_type_params_set = func_env
                .get_named_type_parameters()
                .iter()
                .map(|tp| tp.0)
                .collect::<BTreeSet<Symbol>>();
            let contains_params = struct_env
                .get_named_type_parameters()
                .iter()
                .fold(true, |acc, tp| {
                    acc && func_type_params_set.contains(&tp.0)
                });
            if !contains_params {
                continue;
            }
            let struct_fields_unchanged_exp = self.all_fields_unchanged_exp(func_env, &struct_env, struct_env.get_loc());
            let cond = self.make_condition(
                struct_env.get_loc(),
                ConditionKind::EnsuresSmokeTest,
                struct_fields_unchanged_exp,
            );
            let info = ConditionInfo {
                message: format!("one of the fields of struct {} never changes", struct_env.get_name().display(struct_env.symbol_pool())),
                omit_trace: true,
                negative_cond: true,
            };
            func_env.module_env.env.set_condition_info(cond.loc.clone(), info);
            conds.push(cond);
        }
        let spec = Spec {
            conditions: conds,
            properties: Default::default(),
            on_impl: Default::default(),
        };
        data.rewritten_spec = Some(spec);
    }
}


// ==============================================================================
// Helpers

impl TestInstrumenter {
    /// Helper to return the preconditions of the `func_env` as a list of
    /// `RequiresSmokeTest` conditions.
    /// These conditions are assumed at the top level `_verify` function only.
    fn get_smoke_test_preconditions(&self, func_env: &FunctionEnv<'_>) -> Vec<Condition> {
        let mut conds = vec![];
        for cond in &func_env.get_spec().conditions {
            match cond.kind {
                ConditionKind::Requires | ConditionKind::RequiresModule => {
                    let st_requires = Condition {
                        loc: cond.loc.clone(),
                        kind: ConditionKind::RequiresSmokeTest,
                        exp: cond.exp.clone(),
                    };
                    conds.push(st_requires);
                }
                _ => ()
            }
        }
        conds
    }

    /// Condition that all fields of a struct are unchanged
    fn all_fields_unchanged_exp(&self, func_env: &FunctionEnv<'_>, struct_env: &StructEnv<'_>, loc: Loc) -> Exp {
        // `addr` bound variable in the quantifier
        let addr_id = self.new_node_id(func_env, loc.clone(), ADDRESS_TYPE.clone());
        let addr_symbol = func_env
            .symbol_pool()
            .make("addr");
        let addr_var = Exp::LocalVar(addr_id, addr_symbol.clone());
        // List of constraints that state the fields of a struct never change
        let mut unchanged_cons = vec![];
        // Generate a constraint for each field of a struct
        for field_env in struct_env.get_fields() {
            let global_value = self.make_global_exp(func_env, struct_env.get_type(), addr_var.clone(), loc.clone());
            let global_field_value = self.make_field_select(func_env, struct_env, &field_env, global_value, loc.clone());
            unchanged_cons
                .push(self.make_value_unchanged_exp(func_env, global_field_value, loc.clone()));
        }
        // Create the quantifier body
        let disj_id = self.new_node_id(func_env, loc.clone(), BOOL_TYPE.clone());
        let disj_exp = if unchanged_cons.len() > 1 {
            Exp::Call(disj_id, Operation::Or, unchanged_cons)
        } else {
            unchanged_cons[0].clone()
        };
        let global_exists = self.make_global_exists_exp(func_env, struct_env.get_type(), addr_var.clone(), loc.clone());
        let old_global_exists = self.make_old_exp(func_env, global_exists, loc.clone());
        let body = self.make_implies_exp(func_env, old_global_exists, disj_exp, loc.clone());
        // Create the existential quantifier
        let addr_decl_id = self.new_node_id(func_env, loc.clone(), ADDRESS_TYPE.clone());
        let vars = vec![LocalVarDecl{ id: addr_decl_id, name: addr_symbol, binding: None }];
        self.make_exists_exp(func_env, vars, body, loc.clone())
    }

    /// Creates an expression for imply: `ante` ==> `conc`
    fn make_implies_exp(&self, func_env: &FunctionEnv<'_>, ante: Exp, conc: Exp, loc: Loc) -> Exp {
        let imply_id = self.new_node_id(func_env, loc.clone(), BOOL_TYPE.clone());
        Exp::Call(imply_id, Operation::Implies, vec![ante, conc])
    }

    /// Field select
    fn make_field_select(&self, func_env: &FunctionEnv<'_>, struct_env: &StructEnv<'_>, field_env: &FieldEnv<'_>, exp: Exp, loc: Loc) -> Exp {
        let select_field_id = self.new_node_id(func_env, loc, field_env.get_type());
        let field_select_op = Operation::Select(func_env.module_env.get_id(), struct_env.get_id(), field_env.get_id());
        Exp::Call(select_field_id, field_select_op, vec![exp])
    }

    /// Create existential quantifier
    fn make_exists_exp(&self, func_env: &FunctionEnv<'_>, vars: Vec<LocalVarDecl>, body: Exp, loc: Loc) -> Exp {
        let exists_id = self.new_node_id(func_env, loc.clone(), BOOL_TYPE.clone());
        let bound_id = self.new_node_id(func_env, loc.clone(), RANGE_TYPE.clone());
        let bound_exp = Exp::Value(bound_id, Value::Bool(true));    // dummy
        let lambda_id = self.new_node_id(func_env, loc.clone(), BOOL_TYPE.clone());
        Exp::Call(exists_id, Operation::Any, vec![bound_exp, Exp::Lambda(lambda_id, vars, Box::new(body))])
    }

    /// Helper to create exists<T>(addr)
    fn make_global_exists_exp(&self, func_env: &FunctionEnv<'_>, param_type: Type, addr: Exp, loc: Loc) -> Exp {
        let global_exists_id = self.new_node_id(func_env, loc, BOOL_TYPE.clone());
        func_env.module_env.set_node_instantiation(&global_exists_id, param_type);
        Exp::Call(global_exists_id, Operation::Exists, vec![addr])
    }

    /// Helper to create global<T>(addr)
    fn make_global_exp(&self, func_env: &FunctionEnv<'_>, param_type: Type, addr: Exp, loc: Loc) -> Exp {
        let global_id = self.new_node_id(func_env, loc, param_type.clone());
        func_env.module_env.set_node_instantiation(&global_id, param_type);
        Exp::Call(global_id, Operation::Global, vec![addr])
    }

    /// Helper to create the value == old(value) check
    fn make_value_unchanged_exp(&self, func_env: &FunctionEnv<'_>, exp: Exp, loc: Loc) -> Exp {
        // old(value)
        let old_value = self.make_old_exp(func_env, exp.clone(), loc.clone());
        // value == old(value)
        let compare_id = self.new_node_id(func_env, loc.clone(), BOOL_TYPE.clone());
        Exp::Call(compare_id, Operation::Eq, vec![old_value, exp.clone()])
    }

    /// Helper to create an old expression
    fn make_old_exp(&self, func_env: &FunctionEnv<'_>, exp: Exp, loc: Loc) -> Exp {
        let old_id = self.new_node_id(func_env, loc.clone(), func_env.module_env.get_node_type(exp.node_id()));
        Exp::Call(old_id, Operation::Old, vec![exp])
    }

    /// Helper to create the $abort_flag variable.
    fn make_abort_flag_bool_exp(&self, func_env: &FunctionEnv<'_>) -> Exp {
        let node_id = self.new_node_id(func_env, func_env.get_loc(), BOOL_TYPE.clone());
        let symbol_id = func_env
            .symbol_pool()
            .make("$Boolean($abort_flag)");
        Exp::LocalVar(node_id, symbol_id)
    }

    /// Helper to create fresh node id for an expression
    fn new_node_id(&self, func_env: &FunctionEnv<'_>, loc: Loc, typ: Type) -> NodeId {
        func_env.module_env.new_node(loc, typ)
    }

    /// Helper to create a specification condition.
    fn make_condition(
        &self,
        loc: Loc,
        kind: ConditionKind,
        exp: Exp,
    ) -> Condition {
        Condition {
            loc,
            kind,
            exp,
        }
    }
}
