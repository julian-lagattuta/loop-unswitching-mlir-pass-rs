use std::{collections::HashMap, rc::Rc};

use melior::{
    Context,
    dialect::DialectRegistry,
    ir::{BlockLike, Module, RegionLike, Value, ValueLike, operation::OperationLike},
    utility::register_all_dialects,
};

use super::capabilities::{
    CapabilityExpr, CapabilityOp, CapabilityType, Pattern, block_capabilities,
    find_parent_iterator, format_capabilities, generate_expr, z3_for_loop_viability,
};

    fn test_context() -> Context {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new_with_registry(&registry, false);
    for dialect in ["memref", "arith", "func", "scf"] {
        context.get_or_load_dialect(dialect);
    }
        context
    }

    #[test]
    fn value_to_wavelet_ty_handles_integer_signedness_bool_and_index() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(
                        %signless: i32,
                        %signed: si32,
                        %unsigned: ui32,
                        %flag: i1,
                        %index: index
                    ) {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let ty = |index| {
            let value: Value<'_, '_> = block.argument(index).unwrap().into();
            super::value_to_wavelet_ty(&value)
        };

        assert_eq!(
            ty(0),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
        assert_eq!(
            ty(1),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
        assert_eq!(
            ty(2),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Unsigned
            )
        );
        assert_eq!(ty(3), wavelet_elab::Ty::Bool);
        assert_eq!(
            ty(4),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
    }

    #[test]
    fn value_to_wavelet_ty_maps_static_memrefs_to_mutable_arrays() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<32xui32>) {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        assert_eq!(
            super::value_to_wavelet_ty(&array),
            wavelet_elab::Ty::RefUniq {
                elem: Box::new(wavelet_elab::Ty::Int(
                    wavelet_elab::ir::Signedness::Unsigned
                )),
                len: wavelet_elab::ir::ArrayLen::Const(32),
            }
        );
    }

    #[test]
    #[should_panic(expected = "Wavelet only supports one-dimensional arrays")]
    fn value_to_wavelet_ty_rejects_multidimensional_memrefs() {
        let context = test_context();
        let module = Module::parse(
            &context,
            "module { func.func @test(%array: memref<4x8xi32>) { return } }",
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        super::value_to_wavelet_ty(&array);
    }

    #[test]
    #[should_panic(expected = "Wavelet does not support dynamically sized arrays")]
    fn value_to_wavelet_ty_rejects_dynamic_memrefs() {
        let context = test_context();
        let module = Module::parse(
            &context,
            "module { func.func @test(%array: memref<?xi32>) { return } }",
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        super::value_to_wavelet_ty(&array);
    }

    #[test]
    fn operation_to_wavelet_builds_comparison_and_boolean_xor_statements() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%lhs: i32, %rhs: i32, %flag: i1) {
                        %greater = arith.cmpi sgt, %lhs, %rhs : i32
                        %true = arith.constant true
                        %not = arith.xori %flag, %true : i1
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let greater = block.first_operation().unwrap();
        let not = greater.next_in_block().unwrap().next_in_block().unwrap();

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(greater, "arith.cmpi").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(op, wavelet_elab::Op::SignedLessThan);
        assert_eq!(vars.len(), 3);
        assert_eq!(
            vars[0],
            wavelet_elab::UntypedVar(super::value_to_name(&greater.operand(1).unwrap()))
        );
        assert_eq!(
            vars[1],
            wavelet_elab::UntypedVar(super::value_to_name(&greater.operand(0).unwrap()))
        );
        assert_eq!(
            vars[2],
            wavelet_elab::UntypedVar(super::value_to_name(
                &greater.result(0).unwrap().into()
            ))
        );
        assert!(!fence);

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(not, "arith.xori").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(op, wavelet_elab::Op::NotEqual);
        assert_eq!(vars.len(), 3);
        assert_eq!(
            vars[0],
            wavelet_elab::UntypedVar(super::value_to_name(&not.operand(0).unwrap()))
        );
        assert_eq!(
            vars[1],
            wavelet_elab::UntypedVar(super::value_to_name(&not.operand(1).unwrap()))
        );
        assert_eq!(
            vars[2],
            wavelet_elab::UntypedVar(super::value_to_name(&not.result(0).unwrap().into()))
        );
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_supports_exportable_arithmetic_operations() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%x: i32, %y: i32, %a: i1, %b: i1) {
                        %add = arith.addi %x, %y : i32
                        %sub = arith.subi %x, %y : i32
                        %mul = arith.muli %x, %y : i32
                        %sdiv = arith.divsi %x, %y : i32
                        %udiv = arith.divui %x, %y : i32
                        %bitand = arith.andi %x, %y : i32
                        %bitor = arith.ori %x, %y : i32
                        %bitxor = arith.xori %x, %y : i32
                        %shl = arith.shli %x, %y : i32
                        %ashr = arith.shrsi %x, %y : i32
                        %lshr = arith.shrui %x, %y : i32
                        %and = arith.andi %a, %b : i1
                        %or = arith.ori %a, %b : i1
                        %xor = arith.xori %a, %b : i1
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let expected = [
            wavelet_elab::Op::Add,
            wavelet_elab::Op::Sub,
            wavelet_elab::Op::Mul,
            wavelet_elab::Op::Sdiv,
            wavelet_elab::Op::Udiv,
            wavelet_elab::Op::BitAnd,
            wavelet_elab::Op::BitOr,
            wavelet_elab::Op::BitXor,
            wavelet_elab::Op::Shl,
            wavelet_elab::Op::Ashr,
            wavelet_elab::Op::Lshr,
            wavelet_elab::Op::And,
            wavelet_elab::Op::Or,
            wavelet_elab::Op::NotEqual,
        ];

        let mut operation = block.first_operation();
        for expected_op in expected {
            let current = operation.unwrap();
            let identifier = current.name();
            let name = identifier.as_string_ref().as_str().unwrap();
            let wavelet_elab::Stmt::LetOp { vars, op, fence } =
                super::operation_to_wavelet(current, name).unwrap()
            else {
                unreachable!()
            };
            assert_eq!(op, expected_op);
            assert_eq!(vars.len(), 3);
            assert!(!fence);
            operation = current.next_in_block();
        }
    }

    #[test]
    fn operation_to_wavelet_builds_integer_and_boolean_constants() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test() {
                        %integer = arith.constant -7 : i32
                        %boolean = arith.constant true
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let integer = block.first_operation().unwrap();
        let boolean = integer.next_in_block().unwrap();

        let wavelet_elab::Stmt::LetVal { val, fence, .. } =
            super::operation_to_wavelet(integer, "arith.constant").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(val, wavelet_elab::Val::Int(-7));
        assert!(!fence);

        let wavelet_elab::Stmt::LetVal { val, fence, .. } =
            super::operation_to_wavelet(boolean, "arith.constant").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(val, wavelet_elab::Val::Bool(true));
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_builds_memref_load_and_store_statements() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<16xi32>, %index: index, %value: i32) {
                        %loaded = memref.load %array[%index] : memref<16xi32>
                        memref.store %value, %array[%index] : memref<16xi32>
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let load = block.first_operation().unwrap();
        let store = load.next_in_block().unwrap();

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(load, "memref.load").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            vars,
            vec![wavelet_elab::UntypedVar(super::value_to_name(
                &load.result(0).unwrap().into()
            ))]
        );
        let wavelet_elab::Op::Load { array, index, len } = op else {
            unreachable!()
        };
        assert_eq!(array, wavelet_elab::UntypedVar(super::value_to_name(&load.operand(0).unwrap())));
        assert_eq!(index, wavelet_elab::UntypedVar(super::value_to_name(&load.operand(1).unwrap())));
        assert_eq!(len, wavelet_elab::ir::ArrayLen::Const(16));
        assert!(!fence);

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(store, "memref.store").unwrap()
        else {
            unreachable!()
        };
        assert!(vars.is_empty());
        let wavelet_elab::Op::Store {
            array,
            index,
            value,
            len,
        } = op
        else {
            unreachable!()
        };
        assert_eq!(array, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(1).unwrap())));
        assert_eq!(index, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(2).unwrap())));
        assert_eq!(value, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(0).unwrap())));
        assert_eq!(len, wavelet_elab::ir::ArrayLen::Const(16));
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_treats_distinct_objects_as_a_noop() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<16xi32>) {
                        %distinct = memref.distinct_objects %array : memref<16xi32>
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let distinct_objects = block.first_operation().unwrap();

        assert!(
            super::operation_to_wavelet(distinct_objects, "memref.distinct_objects").is_none()
        );
    }

    #[test]
    #[should_panic(expected = "unsupported MLIR operation: arith.negf")]
    fn operation_to_wavelet_panics_for_unsupported_operations() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%value: f32) {
                        %negated = arith.negf %value : f32
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let unsupported = block.first_operation().unwrap();

        super::operation_to_wavelet(unsupported, "arith.negf");
    }

    #[test]
    fn operation_to_wavelet_builds_function_calls() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func private @callee(memref<4xi32>, i32) -> i32
                    func.func @caller(%array: memref<4xi32>, %value: i32) -> i32 {
                        %result = func.call @callee(%array, %value) : (memref<4xi32>, i32) -> i32
                        return %result : i32
                    }
                }
            "#,
        )
        .unwrap();
        let caller = module.body().first_operation().unwrap().next_in_block().unwrap();
        let block = caller.first_region().unwrap().first_block().unwrap();
        let call = block.first_operation().unwrap();

        let wavelet_elab::Stmt::LetCall {
            vars,
            func,
            args,
            fence,
        } = super::operation_to_wavelet(call, "func.call").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(func, wavelet_elab::FnName("callee".to_string()));
        assert_eq!(
            vars,
            vec![wavelet_elab::UntypedVar(super::value_to_name(
                &call.result(0).unwrap().into()
            ))]
        );
        assert_eq!(
            args,
            vec![
                wavelet_elab::UntypedVar(super::value_to_name(&call.operand(1).unwrap())),
                wavelet_elab::UntypedVar(super::value_to_name(&call.operand(0).unwrap())),
            ]
        );
        assert!(!fence);
    }

    #[test]
    fn block_to_wavelet_builds_value_and_unit_returns() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @value_return(%value: i32) -> i32 {
                        return %value : i32
                    }
                    func.func @unit_return() {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let value_function = module.body().first_operation().unwrap();
        let unit_function = value_function.next_in_block().unwrap();
        let value_block = value_function
            .first_region()
            .unwrap()
            .first_block()
            .unwrap();
        let unit_block = unit_function
            .first_region()
            .unwrap()
            .first_block()
            .unwrap();

        let mut program = wavelet_elab::Program::new();
        let value_expr = super::block_to_wavelet(value_block, &mut program, None);
        let wavelet_elab::Tail::RetVar(value) = value_expr.tail
        else {
            unreachable!()
        };
        assert_eq!(
            value,
            wavelet_elab::UntypedVar(super::value_to_name(
                &value_block.first_operation().unwrap().operand(0).unwrap()
            ))
        );

        let unit_expr = super::block_to_wavelet(unit_block, &mut program, None);
        let wavelet_elab::Tail::RetVar(value) = unit_expr.tail
        else {
            unreachable!()
        };
        assert_eq!(value, wavelet_elab::UntypedVar("_unit_ret".to_string()));
        assert!(matches!(
            unit_expr.stmts.as_slice(),
            [wavelet_elab::Stmt::LetVal {
                val: wavelet_elab::Val::Unit,
                ..
            }]
        ));
    }

    fn bin_op<'c, 'a>(
    operation: CapabilityOp,
    lhs: CapabilityExpr<'c, 'a>,
    rhs: CapabilityExpr<'c, 'a>,
) -> CapabilityExpr<'c, 'a> {
    CapabilityExpr::BinOp {
        operation,
        operands: (Rc::new(lhs), Rc::new(rhs)),
    }
}

#[test]
fn constant_propagate_evaluates_constant_trees() {
    let expression = bin_op(
        CapabilityOp::Mult,
        bin_op(
            CapabilityOp::Add,
            CapabilityExpr::Constant(2),
            CapabilityExpr::Constant(3),
        ),
        bin_op(
            CapabilityOp::Sub,
            CapabilityExpr::Constant(10),
            CapabilityExpr::Constant(4),
        ),
    );

    assert_eq!(expression.constant_propagate(), Some(30));
    assert!(matches!(
        expression.simplified(),
        CapabilityExpr::Constant(30)
    ));
    assert_eq!(expression.to_string(), "30");

    let overflow = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Constant(i64::MAX),
        CapabilityExpr::Constant(1),
    );
    assert_eq!(overflow.constant_propagate(), None);
}

#[test]
fn promote_replaces_variables_and_only_selected_blackboxes() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %other: index) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        scf.for %i = %c0 to %end step %c1 {
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let other_value: Value<'_, '_> = body.argument(1).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let iterator: Value<'_, '_> = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    let expression = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Variable(iterator),
        bin_op(
            CapabilityOp::Add,
            CapabilityExpr::Blackbox(iterator),
            CapabilityExpr::Blackbox(other_value),
        ),
    );
    let expression = expression
        .promote(&CapabilityExpr::Constant(7), Some(for_loop))
        .unwrap();

    let CapabilityExpr::BinOp { operands, .. } = &expression else {
        panic!("promotion should preserve the outer binary operation");
    };
    assert!(matches!(operands.0.as_ref(), CapabilityExpr::Constant(7)));
    let CapabilityExpr::BinOp { operands, .. } = operands.1.as_ref() else {
        panic!("promotion should preserve the nested binary operation");
    };
    assert!(
        matches!(operands.0.as_ref(), CapabilityExpr::Variable(value)
            if value.to_raw().ptr == iterator.to_raw().ptr)
    );
    assert!(
        matches!(operands.1.as_ref(), CapabilityExpr::Blackbox(value)
            if value.to_raw().ptr == other_value.to_raw().ptr)
    );
    assert_eq!(expression.to_string(), "7 + i + arg1");

    let simple_symbolic = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Variable(iterator),
        CapabilityExpr::Constant(5),
    );
    assert_eq!(simple_symbolic.to_string(), "i + 5");

    let no_blackbox_promotion = CapabilityExpr::Blackbox(end_value)
        .promote(&CapabilityExpr::Constant(9), None)
        .unwrap();
    assert!(matches!(no_blackbox_promotion, CapabilityExpr::Blackbox(_)));
}

#[test]
fn generate_expr_classifies_values_relative_to_target_loop() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %initial: index) -> index {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %folded = arith.addi %c2, %c3 : index
                        %outside_math = arith.addi %end, %c1 : index
                        %outside = arith.index_cast %end : index to i64
                        %result = scf.for %i = %c0 to %end step %c1
                            iter_args(%carried = %initial) -> index {
                            %supported = arith.addi %i, %c1 : index
                            %inside = arith.index_cast %i : index to i64
                            %next = arith.addi %carried, %c1 : index
                            scf.yield %next : index
                        }
                        return %result : index
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let mut add_results = vec![];
    let (outside, for_loop) = loop {
        let ident = current.name();
        let name = ident.as_string_ref().as_str().unwrap();
        if name == "arith.addi" {
            add_results.push(current.result(0).unwrap().into());
        } else if name == "arith.index_cast" {
            let outside = current.result(0).unwrap().into();
            current = current.next_in_block().unwrap();
            while current.name().as_string_ref().as_str().unwrap() != "scf.for" {
                current = current.next_in_block().unwrap();
            }
            break (outside, current);
        }
        current = current.next_in_block().unwrap();
    };
    let folded = add_results[0];
    let outside_math = add_results[1];
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iterator: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let supported: Value<'_, '_> = loop_body
        .first_operation()
        .unwrap()
        .result(0)
        .unwrap()
        .into();
    let inside: Value<'_, '_> = loop_body
        .first_operation()
        .unwrap()
        .next_in_block()
        .unwrap()
        .result(0)
        .unwrap()
        .into();

    assert!(matches!(
        generate_expr(end_value, Some(for_loop)),
        Some(CapabilityExpr::Blackbox(value))
            if value.to_raw().ptr == end_value.to_raw().ptr
    ));
    assert!(matches!(
        generate_expr(iterator, Some(for_loop)),
        Some(CapabilityExpr::Variable(value))
            if value.to_raw().ptr == iterator.to_raw().ptr
    ));
    assert!(generate_expr(carried, Some(for_loop)).is_none());
    assert_eq!(
        generate_expr(folded, Some(for_loop))
            .unwrap()
            .constant_propagate(),
        Some(5)
    );
    assert!(matches!(
        generate_expr(outside_math, Some(for_loop)),
        Some(CapabilityExpr::Blackbox(value))
            if value.to_raw().ptr == outside_math.to_raw().ptr
    ));
    assert!(matches!(
        generate_expr(outside, Some(for_loop)),
        Some(CapabilityExpr::Blackbox(value))
            if value.to_raw().ptr == outside.to_raw().ptr
    ));
    assert!(matches!(
        generate_expr(supported, Some(for_loop)),
        Some(CapabilityExpr::BinOp { .. })
    ));
    assert!(generate_expr(inside, Some(for_loop)).is_none());
    assert!(
        CapabilityExpr::Blackbox(inside)
            .promote(&CapabilityExpr::Constant(0), Some(for_loop))
            .is_none()
    );
}

#[test]
fn z3_detects_increasing_decreasing_and_poison_patterns() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %factor: index) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        scf.for %i = %c0 to %end step %c1 {
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let factor_value: Value<'_, '_> = body.argument(1).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let iterator: Value<'_, '_> = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    let increasing = CapabilityExpr::Variable(iterator);
    assert_eq!(
        z3_for_loop_viability(&increasing, &increasing, &end_value),
        Pattern::Increasing
    );

    let decreasing = bin_op(
        CapabilityOp::Sub,
        CapabilityExpr::Constant(0),
        CapabilityExpr::Variable(iterator),
    );
    assert_eq!(
        z3_for_loop_viability(&decreasing, &decreasing, &end_value),
        Pattern::Decreasing
    );

    let square = bin_op(
        CapabilityOp::Mult,
        CapabilityExpr::Variable(iterator),
        CapabilityExpr::Variable(iterator),
    );
    assert_eq!(
        z3_for_loop_viability(&square, &square, &end_value),
        Pattern::Increasing
    );

    let shifted = bin_op(
        CapabilityOp::Sub,
        CapabilityExpr::Variable(iterator),
        CapabilityExpr::Constant(1),
    );
    let non_monotonic = bin_op(CapabilityOp::Mult, shifted.clone(), shifted);
    assert_eq!(
        z3_for_loop_viability(&non_monotonic, &non_monotonic, &end_value),
        Pattern::Poison
    );

    let parameterized = bin_op(
        CapabilityOp::Mult,
        CapabilityExpr::Variable(iterator),
        CapabilityExpr::Blackbox(factor_value),
    );
    assert_eq!(
        z3_for_loop_viability(&parameterized, &parameterized, &end_value),
        Pattern::Poison
    );
}

#[test]
fn block_capabilities_promotes_loop_access_and_finds_parent_iterator() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @read(%array: memref<8xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c0 to %c4 step %c1 {
                            %value = memref.load %array[%i] : memref<8xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iterator: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let load = loop_body.first_operation().unwrap();
    let found_iterator = find_parent_iterator(load).unwrap();
    assert_eq!(found_iterator.to_raw().ptr, iterator.to_raw().ptr);

    let mut capabilities = vec![];
    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert!(matches!(start, CapabilityExpr::Constant(0)));
    assert_eq!(end.constant_propagate(), Some(3));

    let loop_capabilities = capability_map.get(&for_loop.to_raw().ptr).unwrap();
    println!(
        "shared loop capabilities: [{}]",
        format_capabilities(loop_capabilities)
    );
    assert_eq!(loop_capabilities.len(), 1);
    assert_eq!(loop_capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = loop_capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.to_string(), "i");
    assert_eq!(end.constant_propagate(), Some(3));
}

#[test]
fn for_loop_parameters_include_upper_bound_and_symbolic_step() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%array: memref<16xi32>, %lower: index, %upper: index, %step: index, %value: i32) {
                        scf.for %i = %lower to %upper step %step {
                            memref.store %value, %array[%i] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                    func.func @constant_step(%array: memref<16xi32>, %lower: index, %upper: index, %value: i32) {
                        %c1 = arith.constant 1 : index
                        scf.for %i = %lower to %upper step %c1 {
                            memref.store %value, %array[%i] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let lower: Value<'_, '_> = body.argument(1).unwrap().into();
    let upper: Value<'_, '_> = body.argument(2).unwrap().into();
    let step: Value<'_, '_> = body.argument(3).unwrap().into();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();

    let (upper_parameter, step_parameter) = super::for_loop_parameter_values(for_loop);

    let super::ForLoopParameterValue::Variable(upper_parameter) = upper_parameter else {
        unreachable!()
    };
    let super::ForLoopParameterValue::Variable(step_parameter) = step_parameter else {
        unreachable!()
    };
    assert_eq!(upper_parameter.name, super::value_to_name(&upper));
    assert_eq!(step_parameter.name, super::value_to_name(&step));
    assert_ne!(upper_parameter.name, super::value_to_name(&lower));

    let constant_step_function = function.next_in_block().unwrap();
    let constant_step_body = constant_step_function
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let constant_step_loop = super::util::BlockIter::new(constant_step_body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let (constant_upper, constant_step) = super::for_loop_parameter_values(constant_step_loop);
    assert!(matches!(constant_upper, super::ForLoopParameterValue::Variable(_)));
    assert!(matches!(constant_step, super::ForLoopParameterValue::Constant(1)));
}

#[test]
fn for_loop_function_parameters_include_unused_iter_args() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%lower: index, %upper: index, %initial: i32) -> i32 {
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %lower to %upper step %c1
                            iter_args(%carried = %initial) -> i32 {
                            %next = arith.constant 7 : i32
                            scf.yield %next : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iteration: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let (upper_bound, step) = super::for_loop_parameter_values(for_loop);

    let parameters = super::for_loop_function_parameters(for_loop, &upper_bound, &step);

    assert!(parameters
        .iter()
        .any(|parameter| parameter.name == super::value_to_name(&iteration)));
    assert!(parameters
        .iter()
        .any(|parameter| parameter.name == super::value_to_name(&carried)));
}

#[test]
fn block_to_wavelet_uses_scf_yield_as_the_loop_body_tail() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%initial: i32) -> i32 {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %c0 to %c1 step %c1
                            iter_args(%carried = %initial) -> i32 {
                            scf.yield %carried : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let yielded = loop_body.first_operation().unwrap().operand(0).unwrap();
    let mut program = wavelet_elab::Program::new();

    let expression = super::block_to_wavelet(loop_body, &mut program, None);

    assert_eq!(
        expression.tail,
        wavelet_elab::Tail::RetVar(wavelet_elab::UntypedVar(super::value_to_name(&yielded)))
    );
}

#[test]
fn block_to_wavelet_makes_a_directly_yielded_if_the_tail() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%condition: i1, %initial: i32) -> i32 {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %c0 to %c1 step %c1
                            iter_args(%carried = %initial) -> i32 {
                            %selected = scf.if %condition -> i32 {
                                %then_value = arith.constant 7 : i32
                                scf.yield %then_value : i32
                            } else {
                                %else_value = arith.constant 9 : i32
                                scf.yield %else_value : i32
                            }
                            scf.yield %selected : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iteration: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let iteration = wavelet_elab::UntypedVar(super::value_to_name(&iteration));
    let carried = wavelet_elab::UntypedVar(super::value_to_name(&carried));
    let next_iteration = wavelet_elab::UntypedVar("next_iteration".to_string());
    let function_name = wavelet_elab::FnName("loop".to_string());
    let information = super::TailCallInformation {
        function_name: function_name.clone(),
        parameters: vec![
            wavelet_elab::TypedVar {
                name: iteration.0.clone(),
                ty: wavelet_elab::Ty::Int(wavelet_elab::ir::Signedness::Signed),
            },
            wavelet_elab::TypedVar {
                name: carried.0.clone(),
                ty: wavelet_elab::Ty::Int(wavelet_elab::ir::Signedness::Signed),
            },
        ],
        iteration_argument: iteration,
        next_iteration: next_iteration.clone(),
        carried_argument: Some(carried),
    };
    let mut program = wavelet_elab::Program::new();

    let expression = super::block_to_wavelet(loop_body, &mut program, Some(&information));

    let wavelet_elab::Tail::IfElse { then_e, else_e, .. } = expression.tail else {
        unreachable!()
    };
    for branch in [*then_e, *else_e] {
        let yielded = match branch.stmts.last().unwrap() {
            wavelet_elab::Stmt::LetVal { var, .. } => var.clone(),
            _ => unreachable!(),
        };
        let wavelet_elab::Tail::TailCall { func, args } = branch.tail else {
            unreachable!()
        };
        assert_eq!(func, function_name);
        assert_eq!(args[0], next_iteration);
        assert_eq!(args[1], yielded);
    }
}

#[test]
fn block_capabilities_tracks_increasing_and_decreasing_unique_loop_caps() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%increasing: memref<4xi32>, %decreasing: memref<4xi32>, %value: i32) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c2 to %c4 step %c1 {
                            memref.store %value, %increasing[%i] : memref<4xi32>
                            scf.yield
                        }
                        scf.for %i = %c0 to %c4 step %c1 {
                            %index = arith.subi %c3, %i : index
                            memref.store %value, %decreasing[%index] : memref<4xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let loops: Vec<_> = super::util::BlockIter::new(body)
        .filter(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .collect();
    let mut capability_map = HashMap::new();
    let mut capabilities = Vec::new();

    block_capabilities(body, &mut capability_map, &mut capabilities);

    let increasing = capability_map.get(&loops[0].to_raw().ptr).unwrap();
    println!(
        "increasing loop capabilities: [{}]",
        format_capabilities(increasing)
    );
    assert_eq!(increasing.len(), 2);
    assert_eq!(increasing[0].capability_type, CapabilityType::Uniq);
    assert_eq!(increasing[1].capability_type, CapabilityType::Shrd);
    let (uniq_start, uniq_end) = increasing[0].capability_expr.as_ref().unwrap();
    let (shrd_start, shrd_end) = increasing[1].capability_expr.as_ref().unwrap();
    assert_eq!(uniq_start.to_string(), "i");
    assert_eq!(uniq_end.constant_propagate(), Some(3));
    assert_eq!(shrd_start.constant_propagate(), Some(2));
    assert_eq!(shrd_end.to_string(), "i - 1");

    let decreasing = capability_map.get(&loops[1].to_raw().ptr).unwrap();
    println!(
        "decreasing loop capabilities: [{}]",
        format_capabilities(decreasing)
    );
    assert_eq!(decreasing.len(), 2);
    assert_eq!(decreasing[0].capability_type, CapabilityType::Uniq);
    assert_eq!(decreasing[1].capability_type, CapabilityType::Shrd);
    let (uniq_start, uniq_end) = decreasing[0].capability_expr.as_ref().unwrap();
    let (shrd_start, shrd_end) = decreasing[1].capability_expr.as_ref().unwrap();
    assert_eq!(uniq_start.constant_propagate(), Some(0));
    assert_eq!(uniq_end.to_string(), "3 - i");
    assert_eq!(shrd_start.to_string(), "3 - i + 1");
    assert_eq!(shrd_end.constant_propagate(), Some(3));
}

#[test]
fn block_capabilities_keeps_poison_for_loop_caps_poisoned() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%array: memref<16xi32>, %value: i32) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c0 to %c4 step %c1 {
                            %shifted = arith.subi %i, %c1 : index
                            %index = arith.muli %shifted, %shifted : index
                            memref.store %value, %array[%index] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let mut capability_map = HashMap::new();
    let mut capabilities = Vec::new();

    block_capabilities(body, &mut capability_map, &mut capabilities);

    let loop_capabilities = capability_map.get(&for_loop.to_raw().ptr).unwrap();
    println!(
        "poisoned loop capabilities: [{}]",
        format_capabilities(loop_capabilities)
    );
    assert_eq!(loop_capabilities.len(), 1);
    assert_eq!(loop_capabilities[0].capability_type, CapabilityType::Uniq);
    assert!(loop_capabilities[0].capability_expr.is_none());
}

#[test]
fn block_capabilities_handles_flattened_2d_array_access() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @read_2d(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            scf.for %j = %c0 to %c10 step %c1 {
                                %width = arith.constant 10 : index
                                %row = arith.muli %i, %width : index
                                %index = arith.addi %row, %j : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}

#[test]
fn block_capabilities_handles_nested_quadratic_access() {
    let context = test_context();
    let module = Module::parse(&context, include_str!("../complicated_access.mlir")).unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Uniq);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(7));
    assert_eq!(end.constant_propagate(), Some(232));
}

#[test]
fn block_capabilities_handles_increasing_then_decreasing_accesses() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @bidirectional_access(%array: memref<11xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c10 = arith.constant 10 : index
                        %c11 = arith.constant 11 : index
                        scf.for %i = %c0 to %c11 step %c1 {
                            %increasing = memref.load %array[%i] : memref<11xi32>
                            %decreasing_index = arith.subi %c10, %i : index
                            %decreasing = memref.load %array[%decreasing_index] : memref<11xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 2);
    for capability in &capabilities {
        assert_eq!(capability.capability_type, CapabilityType::Shrd);
        let (start, end) = capability.capability_expr.as_ref().unwrap();
        assert_eq!(start.constant_propagate(), Some(0));
        assert_eq!(end.constant_propagate(), Some(10));
    }
}

#[test]
fn block_capabilities_handles_increasing_intervals_with_decreasing_indices() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @increasing_intervals(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c9 = arith.constant 9 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            %interval_start = arith.muli %i, %c10 : index
                            scf.for %j = %c0 to %c10 step %c1 {
                                %decreasing_index = arith.subi %c9, %j : index
                                %index = arith.addi %interval_start, %decreasing_index : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}

#[test]
fn block_capabilities_handles_decreasing_intervals_with_increasing_indices() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @decreasing_intervals(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c9 = arith.constant 9 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            %decreasing_interval = arith.subi %c9, %i : index
                            %interval_start = arith.muli %decreasing_interval, %c10 : index
                            scf.for %j = %c0 to %c10 step %c1 {
                                %index = arith.addi %interval_start, %j : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}
