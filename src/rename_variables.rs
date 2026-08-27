use std::collections::HashMap;

use wavelet_elab::{
    Expr, Op, Program, Stmt, Tail, UntypedVar,
    logic::{
        region::{Interval, Region},
        semantic::solver::Idx,
    },
};

pub(crate) fn rename_program_variables(program: &mut Program<UntypedVar>) {
    for definition in &mut program.defs {
        let mut renamer = VariableRenamer::default();

        for (index, parameter) in definition.params.iter_mut().enumerate() {
            let old_name = parameter.name.clone();
            let new_name = format!("arg{index}");
            renamer.names.insert(old_name, new_name.clone());
            parameter.name = new_name;
        }

        for allocated in &mut definition.alloc_arrays {
            *allocated = renamer.rename_name(allocated);
        }
        for capability in &mut definition.caps {
            capability.array = renamer.rename_name(&capability.array);
            capability.uniq = capability
                .uniq
                .as_ref()
                .map(|region| renamer.rename_region(region));
            capability.shrd = capability
                .shrd
                .as_ref()
                .map(|region| renamer.rename_region(region));
        }
        renamer.rename_expr(&mut definition.body);
    }
}

#[derive(Default)]
struct VariableRenamer {
    names: HashMap<String, String>,
    next_local: usize,
}

impl VariableRenamer {
    fn rename_name(&mut self, name: &str) -> String {
        if let Some(renamed) = self.names.get(name) {
            return renamed.clone();
        }

        let renamed = format!("v{}", self.next_local);
        self.next_local += 1;
        self.names.insert(name.to_string(), renamed.clone());
        renamed
    }

    fn rename_var(&mut self, variable: &mut UntypedVar) {
        variable.0 = self.rename_name(&variable.0);
    }

    fn rename_expr(&mut self, expression: &mut Expr<UntypedVar>) {
        for statement in &mut expression.stmts {
            self.rename_stmt(statement);
        }
        self.rename_tail(&mut expression.tail);
    }

    fn rename_stmt(&mut self, statement: &mut Stmt<UntypedVar>) {
        match statement {
            Stmt::LetVal { var, .. } => self.rename_var(var),
            Stmt::LetOp { vars, op, .. } => {
                for variable in vars {
                    self.rename_var(variable);
                }
                self.rename_op(op);
            }
            Stmt::LetCall { vars, args, .. } => {
                for argument in args {
                    self.rename_var(argument);
                }
                for variable in vars {
                    self.rename_var(variable);
                }
            }
        }
    }

    fn rename_op(&mut self, operation: &mut Op<UntypedVar>) {
        match operation {
            Op::Load { array, index, .. } => {
                self.rename_var(array);
                self.rename_var(index);
            }
            Op::Store {
                array,
                index,
                value,
                ..
            } => {
                self.rename_var(array);
                self.rename_var(index);
                self.rename_var(value);
            }
            _ => {}
        }
    }

    fn rename_tail(&mut self, tail: &mut Tail<UntypedVar>) {
        match tail {
            Tail::RetVar(variable) => self.rename_var(variable),
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => {
                self.rename_var(cond);
                self.rename_expr(then_e);
                self.rename_expr(else_e);
            }
            Tail::TailCall { args, .. } => {
                for argument in args {
                    self.rename_var(argument);
                }
            }
        }
    }

    fn rename_region(&mut self, region: &Region) -> Region {
        Region::from_intervals(
            region
                .iter()
                .map(|interval| {
                    Interval::bounded(
                        self.rename_idx(&interval.lo),
                        self.rename_idx(&interval.hi),
                    )
                })
                .collect(),
        )
    }

    fn rename_idx(&mut self, index: &Idx) -> Idx {
        match index {
            Idx::Const(value) => Idx::Const(*value),
            Idx::Var(name) => Idx::Var(self.rename_name(name)),
            Idx::Add(lhs, rhs) => Idx::Add(
                Box::new(self.rename_idx(lhs)),
                Box::new(self.rename_idx(rhs)),
            ),
            Idx::Sub(lhs, rhs) => Idx::Sub(
                Box::new(self.rename_idx(lhs)),
                Box::new(self.rename_idx(rhs)),
            ),
            Idx::Mul(lhs, rhs) => Idx::Mul(
                Box::new(self.rename_idx(lhs)),
                Box::new(self.rename_idx(rhs)),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use wavelet_elab::{
        Expr, FnDef, Op, Program, Stmt, Tail, Ty, TypedVar, UntypedVar,
        ir::{ArrayLen, Signedness},
        logic::{
            cap::CapPattern,
            region::Region,
            semantic::solver::Idx,
        },
    };

    use super::rename_program_variables;

    #[test]
    fn renames_parameters_locals_and_capability_variables() {
        let mut program = Program {
            defs: vec![FnDef {
                name: wavelet_elab::FnName("read".to_string()),
                params: vec![
                    TypedVar {
                        name: "old_array".to_string(),
                        ty: Ty::RefUniq {
                            elem: Box::new(Ty::Int(Signedness::Signed)),
                            len: ArrayLen::Const(10),
                        },
                    },
                    TypedVar {
                        name: "old_index".to_string(),
                        ty: Ty::Int(Signedness::Signed),
                    },
                ],
                alloc_arrays: vec!["old_array".to_string()],
                caps: vec![CapPattern {
                    array: "old_array".to_string(),
                    len: ArrayLen::Const(10),
                    uniq: None,
                    shrd: Some(Region::from_bounded(
                        Idx::Var("old_index".to_string()),
                        Idx::Add(
                            Box::new(Idx::Var("old_index".to_string())),
                            Box::new(Idx::Const(1)),
                        ),
                    )),
                }],
                returns: Ty::Int(Signedness::Signed),
                body: Expr {
                    stmts: vec![Stmt::LetOp {
                        vars: vec![UntypedVar("old_result".to_string())],
                        op: Op::Load {
                            array: UntypedVar("old_array".to_string()),
                            index: UntypedVar("old_index".to_string()),
                            len: ArrayLen::Const(10),
                        },
                        fence: false,
                    }],
                    tail: Tail::RetVar(UntypedVar("old_result".to_string())),
                },
            }],
        };

        rename_program_variables(&mut program);

        let definition = &program.defs[0];
        assert_eq!(definition.params[0].name, "arg0");
        assert_eq!(definition.params[1].name, "arg1");
        assert_eq!(definition.alloc_arrays, ["arg0"]);
        assert_eq!(definition.caps[0].array, "arg0");
        let interval = definition.caps[0].shrd.as_ref().unwrap().iter().next().unwrap();
        assert_eq!(interval.lo, Idx::Var("arg1".to_string()));
        let Stmt::LetOp { vars, op, .. } = &definition.body.stmts[0] else {
            unreachable!()
        };
        assert_eq!(vars[0].0, "v0");
        let Op::Load { array, index, .. } = op else {
            unreachable!()
        };
        assert_eq!(array.0, "arg0");
        assert_eq!(index.0, "arg1");
        assert_eq!(definition.body.tail, Tail::RetVar(UntypedVar("v0".to_string())));
    }
}
