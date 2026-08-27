use melior::{
    Context, IrRewriter,
    dialect::scf,
    ir::{
        Block, BlockLike, BlockRef, Location, Module, OperationRef, Region, RegionLike, Type,
        Value, ValueLike,
        attribute::BoolAttribute,
        block::BlockArgument,
        operation::{
            OperationLike, OperationMutLike, OperationRefMut, OperationResult, WalkOrder,
            WalkOrder::PreOrder, WalkResult,
        },
    },
};

fn as_ref<'c, 'a>(op: OperationRefMut<'c, 'a>) -> OperationRef<'c, 'a> {
    unsafe { OperationRef::from_raw(op.to_raw()) }
}

fn unswitch_loop<'c, 'a, 'd, 'q>(
    context: &'c Context,
    for_loop: OperationRef<'c, 'a>,
    if_statement: OperationRefMut<'c, 'a>,
    candidate_loops: &mut Vec<OperationRefMut<'d, 'q>>,
) {
    let mut op = if_statement;
    let condition = op.operand(0).unwrap();
    let last_loop = for_loop;

    let modified_regions: [Region; 2] = [Region::new(), Region::new()];
    op.set_attribute(
        "__marker",
        BoolAttribute::new(unsafe { op.context().to_ref() }, true).into(),
    );

    for reg in 0..2 {
        let block = Block::new(&[]);
        block.append_operation((*last_loop).clone());
        modified_regions[reg].append_block(block);

        let mut true_region = modified_regions[reg]
            .first_block()
            .unwrap()
            .first_operation_mut()
            .unwrap();

        let mut inner_if = None;
        true_region.walk_mut(PreOrder, |mut op: OperationRefMut<'_, '_>| {
            if op.has_attribute("__marker") {
                op.remove_attribute("__marker");
                inner_if = Some(op.to_raw());
                return WalkResult::Interrupt;
            }
            WalkResult::Advance
        });

        let inner_if = unsafe { OperationRef::from_raw(inner_if.unwrap()) };

        let if_rewriter = IrRewriter::from_op(inner_if);
        let if_rewriter = if_rewriter.as_rewriter_base();
        if let Some(first_block) = inner_if.region(reg).unwrap().first_block() {
            let mut current_opt = first_block.first_operation();
            while let Some(current) = current_opt {
                let ident = current.name();
                let name = ident.as_string_ref().as_str().unwrap();
                if name == "scf.yield" {
                    for (inner_if_out, yield_value) in inner_if.results().zip(current.operands()) {
                        if_rewriter.replace_all_uses_with(inner_if_out.into(), yield_value);
                    }
                    break;
                }
                current_opt = current.next_in_block();
                if_rewriter.move_op_before(current, inner_if);
            }
        }

        if_rewriter.erase_op(inner_if);
        if_rewriter.set_insertion_point_after(
            modified_regions[reg]
                .first_block()
                .unwrap()
                .first_operation()
                .unwrap(),
        );
        let for_rets: Vec<Value<'_, '_>> = true_region.results().map(|r| r.into()).collect();
        if_rewriter.insert(scf::r#yield(&for_rets, Location::unknown(&context)));
    }

    let ret_types = last_loop.results().map(|r| r.r#type());
    let ret_types: Vec<Type<'_>> = ret_types.collect();
    let rewriter = IrRewriter::from_op(last_loop);
    let rewriter = rewriter.as_rewriter_base();
    let [then_region, else_region] = modified_regions;

    let final_if = scf::r#if(
        condition,
        &ret_types,
        then_region,
        else_region,
        Location::unknown(&context),
    );
    let final_if = rewriter.insert(final_if);
    for (a, b) in last_loop.results().zip(final_if.results()) {
        rewriter.replace_all_uses_with(a.into(), b.into());
    }
    for region in final_if.regions() {
        scan_for_loops(region.first_block().unwrap(), candidate_loops);
    }
    rewriter.erase_op(last_loop);
}

fn scan_for_loops<'d, 'q, 'a, 'c>(
    starting_point: BlockRef<'a, 'c>,
    candidate_loops: &mut Vec<OperationRefMut<'d, 'q>>,
) {
    let mut current_opt = starting_point.first_operation();
    while let Some(current) = current_opt {
        current.walk(WalkOrder::PreOrder, |op| {
            let op_ident = op.name();
            let op_name = op_ident.as_string_ref().as_str().unwrap();
            if (op_name == "scf.for" || op_name == "scf.while") && !op.has_attribute("__visited") {
                candidate_loops.push(unsafe { OperationRefMut::from_raw(op.to_raw()) });
                return WalkResult::Skip;
            }
            WalkResult::Advance
        });
        current_opt = current.next_in_block();
    }
}

pub fn loop_unswitch(context: &Context, module: &mut Module<'_>) {
    let mut candidate_loops: Vec<_> = vec![];
    scan_for_loops(module.body(), &mut candidate_loops);

    while let Some(mut candidate_loop) = candidate_loops.pop() {
        let mut did_unswitch = false;
        candidate_loop
            .clone()
            .walk_mut(WalkOrder::PreOrder, |if_op: OperationRefMut<'_, '_>| {
                let op_ident = if_op.name();
                let op_name = op_ident.as_string_ref().as_str().unwrap();
                if op_name != "scf.if" {
                    return WalkResult::Advance;
                }
                let condition = if_op.operand(0).unwrap();

                let cond_op_parent = if let Ok(o) = OperationResult::try_from(condition) {
                    o.owner().parent_operation().unwrap().to_raw().ptr
                } else if let Ok(o) = BlockArgument::try_from(condition) {
                    let own = o.owner();
                    own.parent_operation().unwrap().to_raw().ptr
                } else {
                    return WalkResult::Advance;
                };
                let mut current = candidate_loop.parent_operation().unwrap();

                while current.to_raw().ptr.ne(&cond_op_parent) {
                    current = match current.parent_operation() {
                        Some(o) => o,
                        None => return WalkResult::Advance,
                    }
                }
                did_unswitch = true;
                unswitch_loop(context, as_ref(candidate_loop), if_op, &mut candidate_loops);
                WalkResult::Interrupt
            });
        if !did_unswitch {
            candidate_loop.set_attribute("__visited", BoolAttribute::new(context, true).into());
            for region in candidate_loop.regions() {
                if let Some(block) = region.first_block() {
                    scan_for_loops(block, &mut candidate_loops);
                }
            }
        }
    }

    module
        .as_operation_mut()
        .walk_mut(WalkOrder::PreOrder, |mut op| {
            if op.has_attribute("__visited") {
                op.remove_attribute("__visited").unwrap();
            }
            WalkResult::Advance
        });
}
