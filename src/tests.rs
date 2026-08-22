    use super::*;

    fn test_context() -> Context {
        let registry = DialectRegistry::new();
        register_all_dialects(&registry);
        let context = Context::new_with_registry(&registry, false);
        for dialect in ["memref", "arith", "func", "scf"] {
            context.get_or_load_dialect(dialect);
        }
        context
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
        assert!(matches!(operands.0.as_ref(), CapabilityExpr::Variable(value)
            if value.to_raw().ptr == iterator.to_raw().ptr));
        assert!(matches!(operands.1.as_ref(), CapabilityExpr::Blackbox(value)
            if value.to_raw().ptr == other_value.to_raw().ptr));
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
        let supported: Value<'_, '_> = loop_body.first_operation().unwrap().result(0).unwrap().into();
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
        assert!(CapabilityExpr::Blackbox(inside)
            .promote(&CapabilityExpr::Constant(0), Some(for_loop))
            .is_none());
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
        block_capabilities(body, &mut capabilities);

        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
        let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
        assert!(matches!(start, CapabilityExpr::Constant(0)));
        assert_eq!(end.constant_propagate(), Some(3));
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

        block_capabilities(body, &mut capabilities);

        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
        let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
        assert_eq!(start.constant_propagate(), Some(0));
        assert_eq!(end.constant_propagate(), Some(99));
    }

    #[test]
    fn block_capabilities_handles_nested_quadratic_access() {
        let context = test_context();
        let module = Module::parse(
            &context,
            include_str!("../complicated_access.mlir"),
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let body = function.first_region().unwrap().first_block().unwrap();
        let mut capabilities = vec![];

        block_capabilities(body, &mut capabilities);

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

        block_capabilities(body, &mut capabilities);

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

        block_capabilities(body, &mut capabilities);

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

        block_capabilities(body, &mut capabilities);

        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
        let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
        assert_eq!(start.constant_propagate(), Some(0));
        assert_eq!(end.constant_propagate(), Some(99));
    }
