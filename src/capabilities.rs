use std::{
    collections::HashMap, ffi::c_void, fmt::{self, Display, Formatter}, rc::Rc,
};

use melior::ir::{
    BlockLike, BlockRef, Module, OperationRef, RegionLike, ShapedTypeLike, Value, ValueLike, attribute::IntegerAttribute, block::BlockArgument, operation::{OperationLike, OperationResult, WalkOrder, WalkResult}, r#type::{DimSize, MemRefType},
};
use wavelet_elab::logic::{cap::CapPattern, region::{Interval, Region}, semantic::Idx};
use z3::{
    SatResult, Solver,
    ast::{self, Ast, Bool},
};

use crate::{util::BlockIter, value_to_name};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CapabilityType {
    Shrd,
    Uniq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CapabilityOp {
    Add,
    Sub,
    Mult,
}

#[derive(Debug, Clone)]
pub(super) enum CapabilityExpr<'c, 'a> {
    BinOp {
        operation: CapabilityOp,
        operands: (Rc<CapabilityExpr<'c, 'a>>, Rc<CapabilityExpr<'c, 'a>>), //inclusive range
    },
    Constant(i64),
    Variable(Value<'c, 'a>),
    Blackbox(Value<'c, 'a>),
}

impl<'c, 'a> CapabilityExpr<'c, 'a> {
    pub(super) fn to_wavelet_idx<'d, 'b>(
        &self
    ) -> Idx {
        match self {
            CapabilityExpr::Constant(n) => Idx::Const(*n),
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands.0.to_wavelet_idx();
                let rhs = operands.1.to_wavelet_idx();
                match operation {
                    CapabilityOp::Add => Idx::Add(Box::new(lhs), Box::new(rhs)),
                    CapabilityOp::Sub => Idx::Sub(Box::new(lhs), Box::new(rhs)),
                    CapabilityOp::Mult => Idx::Mul(Box::new(lhs), Box::new(rhs)),
                }
            }
            CapabilityExpr::Variable(value) => {
                Idx::Var(crate::value_to_name(value))
            }
            CapabilityExpr::Blackbox(value) => Idx::Var(crate::value_to_name(value)),
        }
    }
    pub(super) fn simplified(&self) -> CapabilityExpr<'c, 'a> {
        if let Some(value) = self.constant_propagate() {
            return CapabilityExpr::Constant(value);
        }

        let CapabilityExpr::BinOp {
            operation,
            operands,
        } = self
        else {
            return self.clone();
        };

        let lhs = operands.0.simplified();
        let rhs = operands.1.simplified();

        if *operation == CapabilityOp::Add {
            if let (
                CapabilityExpr::BinOp {
                    operation: CapabilityOp::Add,
                    operands: lhs_operands,
                },
                CapabilityExpr::Constant(rhs_value),
            ) = (&lhs, &rhs)
            {
                if let CapabilityExpr::Constant(lhs_value) = lhs_operands.1.as_ref() {
                    if let Some(value) = lhs_value.checked_add(*rhs_value) {
                        return CapabilityExpr::BinOp {
                            operation: CapabilityOp::Add,
                            operands: (
                                Rc::clone(&lhs_operands.0),
                                Rc::new(CapabilityExpr::Constant(value)),
                            ),
                        };
                    }
                }
            }
        }

        match (operation, &lhs, &rhs) {
            (CapabilityOp::Add, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Sub, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Mult, _, CapabilityExpr::Constant(1)) => lhs,
            (CapabilityOp::Add, CapabilityExpr::Constant(0), _)
            | (CapabilityOp::Mult, CapabilityExpr::Constant(1), _) => rhs,
            (CapabilityOp::Mult, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Mult, CapabilityExpr::Constant(0), _) => CapabilityExpr::Constant(0),
            _ => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (Rc::new(lhs), Rc::new(rhs)),
            },
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            CapabilityExpr::BinOp {
                operation: CapabilityOp::Add | CapabilityOp::Sub,
                ..
            } => 1,
            CapabilityExpr::BinOp {
                operation: CapabilityOp::Mult,
                ..
            } => 2,
            CapabilityExpr::Constant(_)
            | CapabilityExpr::Variable(_)
            | CapabilityExpr::Blackbox(_) => 3,
        }
    }

    fn fmt_compact(&self, formatter: &mut Formatter<'_>, minimum_precedence: u8) -> fmt::Result {
        let precedence = self.precedence();
        let parenthesize = precedence < minimum_precedence;
        if parenthesize {
            write!(formatter, "(")?;
        }

        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                operands.0.fmt_compact(formatter, precedence)?;
                let symbol = match operation {
                    CapabilityOp::Add => "+",
                    CapabilityOp::Sub => "-",
                    CapabilityOp::Mult => "*",
                };
                write!(formatter, " {symbol} ")?;
                let rhs_precedence = if *operation == CapabilityOp::Sub {
                    precedence + 1
                } else {
                    precedence
                };
                operands.1.fmt_compact(formatter, rhs_precedence)?;
            }
            CapabilityExpr::Constant(value) => write!(formatter, "{value}")?,
            CapabilityExpr::Variable(_) => write!(formatter, "i")?,
            CapabilityExpr::Blackbox(value) => write!(formatter, "{}", compact_value_name(*value))?,
        }

        if parenthesize {
            write!(formatter, ")")?;
        }
        Ok(())
    }

    fn substitute_variable(
        &self,
        variable_replacement: &CapabilityExpr<'c, 'a>,
    ) -> CapabilityExpr<'c, 'a> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(operands.0.substitute_variable(variable_replacement)),
                    Rc::new(operands.1.substitute_variable(variable_replacement)),
                ),
            },
            CapabilityExpr::Variable(_) => variable_replacement.clone(),
            CapabilityExpr::Constant(_) | CapabilityExpr::Blackbox(_) => self.clone(),
        }
    }

    fn expand_blackboxes(
        &self,
        parent_for_loop: Option<OperationRef<'c, 'a>>,
    ) -> Option<CapabilityExpr<'c, 'a>> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => Some(CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(operands.0.expand_blackboxes(parent_for_loop)?),
                    Rc::new(operands.1.expand_blackboxes(parent_for_loop)?),
                ),
            }),
            CapabilityExpr::Blackbox(value) => match parent_for_loop {
                Some(for_loop) => generate_expr(*value, Some(for_loop)),
                None => Some(self.clone()),
            },
            CapabilityExpr::Constant(_) | CapabilityExpr::Variable(_) => Some(self.clone()),
        }
    }

    pub(super) fn promote(
        &self,
        variable_replacement: &CapabilityExpr<'c, 'a>,
        parent_for_loop: Option<OperationRef<'c, 'a>>,
    ) -> Option<CapabilityExpr<'c, 'a>> {
        self.substitute_variable(variable_replacement)
            .expand_blackboxes(parent_for_loop)
    }

    pub(super) fn constant_propagate(&self) -> Option<i64> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands.0.constant_propagate()?;
                let rhs = operands.1.constant_propagate()?;

                match operation {
                    CapabilityOp::Add => lhs.checked_add(rhs),
                    CapabilityOp::Sub => lhs.checked_sub(rhs),
                    CapabilityOp::Mult => lhs.checked_mul(rhs),
                }
            }
            CapabilityExpr::Constant(value) => Some(*value),
            CapabilityExpr::Variable(_) | CapabilityExpr::Blackbox(_) => None,
        }
    }

    pub(super) fn to_z3(
        &self,
        iteration_variable: &ast::Int,
        for_loop_end: &ast::Int,
        for_loop_end_value: &Value<'_, '_>,
    ) -> ast::Int {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands
                    .0
                    .to_z3(iteration_variable, for_loop_end, for_loop_end_value);
                let rhs = operands
                    .1
                    .to_z3(iteration_variable, for_loop_end, for_loop_end_value);

                match operation {
                    CapabilityOp::Add => ast::Int::add(&[&lhs, &rhs]),
                    CapabilityOp::Sub => ast::Int::sub(&[&lhs, &rhs]),
                    CapabilityOp::Mult => ast::Int::mul(&[&lhs, &rhs]),
                }
            }
            CapabilityExpr::Constant(value) => ast::Int::from_i64(*value),
            CapabilityExpr::Variable(_) => iteration_variable.clone(),
            CapabilityExpr::Blackbox(value)
                if value.to_raw().ptr == for_loop_end_value.to_raw().ptr =>
            {
                for_loop_end.clone()
            }
            CapabilityExpr::Blackbox(value) => {
                let name = format!("blackbox_{:x}", value.to_raw().ptr as usize);
                ast::Int::new_const(name)
            }
        }
    }
}

impl Display for CapabilityExpr<'_, '_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.simplified().fmt_compact(formatter, 0)
    }
}

fn compact_value_name(value: Value<'_, '_>) -> String {
    if let Ok(argument) = BlockArgument::try_from(value) {
        return format!("arg{}", argument.argument_number());
    }

    let printed = value.to_string();
    printed
        .split_once(" = ")
        .map_or(printed.as_str(), |(name, _)| name)
        .trim()
        .to_string()
}

#[derive(Debug, Clone)]
pub(super) struct Capability<'c, 'a> {
    pub(super) array: Value<'c, 'a>,
    pub(super) capability_type: CapabilityType,
    pub(super) capability_expr: Option<(CapabilityExpr<'c, 'a>, CapabilityExpr<'c, 'a>)>, // None means "poison" which takes the entire bounds of the array
}

pub(super) fn capability_constants<'c, 'a>(
    capability_map: &mut HashMap<*mut c_void, Vec<Capability<'c, 'a>>>,
) {
    fn replace_constants<'c, 'a>(expression: &CapabilityExpr<'c, 'a>) -> CapabilityExpr<'c, 'a> {
        let replaced = match expression {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(replace_constants(&operands.0)),
                    Rc::new(replace_constants(&operands.1)),
                ),
            },
            CapabilityExpr::Blackbox(value) => constant_fold_value(*value)
                .map(CapabilityExpr::Constant)
                .unwrap_or_else(|| expression.clone()),
            CapabilityExpr::Constant(_) | CapabilityExpr::Variable(_) => expression.clone(),
        };
        replaced.simplified()
    }

    for capabilities in capability_map.values_mut() {
        for capability in capabilities {
            if let Some((start, end)) = &mut capability.capability_expr {
                *start = replace_constants(start);
                *end = replace_constants(end);
            }
        }
    }
}

pub(super) fn to_wavelet_capability(
    capabilities: &[Capability<'_, '_>],
) -> Vec<CapPattern> {
    struct PatternIntervals {
        array: String,
        size: usize,
        uniq: Vec<Interval>,
        shrd: Vec<Interval>,
    }

    let mut pattern_intervals: Vec<PatternIntervals> = Vec::new();

    for capability in capabilities {
        let memref_type = MemRefType::try_from(capability.array.r#type()).unwrap();
        let size = match memref_type
            .dim_size(0)
            .unwrap()
        {
            DimSize::Static(size) => {
                usize::try_from(size).unwrap()
            }
            DimSize::Dynamic => panic!("Wavelet does not support dynamically sized arrays"),
        };
        let array = value_to_name(&capability.array);
        let interval = match &capability.capability_expr {
            Some((start, end)) => {
                let end_exclusive = CapabilityExpr::BinOp {
                    operation: CapabilityOp::Add,
                    operands: (
                        Rc::new(end.clone()),
                        Rc::new(CapabilityExpr::Constant(1)),
                    ),
                };
                Interval::bounded(
                    start.simplified().to_wavelet_idx(),
                    end_exclusive.simplified().to_wavelet_idx(),
                )
            }
            None => Interval::bounded(Idx::Const(0), Idx::from_usize(size)),
        };

        let pattern = match pattern_intervals
            .iter_mut()
            .find(|pattern| pattern.array == array)
        {
            Some(pattern) => pattern,
            None => {
                pattern_intervals.push(PatternIntervals {
                    array,
                    size,
                    uniq: Vec::new(),
                    shrd: Vec::new(),
                });
                pattern_intervals.last_mut().unwrap()
            }
        };
        let intervals = match capability.capability_type {
            CapabilityType::Shrd => &mut pattern.shrd,
            CapabilityType::Uniq => &mut pattern.uniq,
        };
        intervals.push(interval);
    }

    pattern_intervals
        .into_iter()
        .map(|pattern| CapPattern {
            array: pattern.array,
            len: wavelet_elab::ir::ArrayLen::Const(pattern.size),
            uniq: (!pattern.uniq.is_empty()).then(|| Region::from_intervals(pattern.uniq)),
            shrd: (!pattern.shrd.is_empty()).then(|| Region::from_intervals(pattern.shrd)),
        })
        .collect()
}
impl Display for Capability<'_, '_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        let kind = match self.capability_type {
            CapabilityType::Shrd => "shrd",
            CapabilityType::Uniq => "uniq",
        };
        let array = compact_value_name(self.array);
        match &self.capability_expr {
            Some((start, end)) => write!(formatter, "{array}: {kind} @ {start}..{end}"),
            None => write!(formatter, "{array}: {kind} @ *"),
        }
    }
}

pub(super) fn format_capabilities(capabilities: &[Capability<'_, '_>]) -> String {
    capabilities
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn has_iteration_variable(expr: &CapabilityExpr<'_, '_>) -> bool {
    match expr {
        CapabilityExpr::BinOp { operands, .. } => {
            has_iteration_variable(&operands.0) || has_iteration_variable(&operands.1)
        }
        CapabilityExpr::Variable(_) => true,
        CapabilityExpr::Constant(_) | CapabilityExpr::Blackbox(_) => false,
    }
}

fn find_parent_for<'c, 'a>(operation: OperationRef<'c, 'a>) -> Option<OperationRef<'c, 'a>> {
    let mut parent = operation.block()?.parent_operation()?;

    loop {
        let ident = parent.name();
        let name = ident.as_string_ref().as_str().ok()?;

        if name == "scf.for" {
            return Some(parent);
        }

        parent = parent.block()?.parent_operation()?;
    }
}

pub(super) fn find_parent_iterator<'c, 'a>(
    operation: OperationRef<'c, 'a>,
) -> Option<Value<'c, 'a>> {
    let parent_for = find_parent_for(operation)?;
    let body = parent_for.first_region()?.first_block()?;
    Some(body.argument(0).ok()?.into())
}

fn block_is_inside_operation(block: BlockRef<'_, '_>, ancestor: OperationRef<'_, '_>) -> bool {
    let mut parent = block.parent_operation();

    while let Some(operation) = parent {
        if operation.to_raw().ptr == ancestor.to_raw().ptr {
            return true;
        }
        parent = operation.block().and_then(|block| block.parent_operation());
    }

    false
}

pub(super) fn generate_expr<'c, 'a>(
    value: Value<'c, 'a>,
    target_for_loop: Option<OperationRef<'c, 'a>>,
) -> Option<CapabilityExpr<'c, 'a>>
where
    'c: 'a,
{
    generate_expr_helper(value, target_for_loop)
}

pub(super) fn constant_fold_value(value: Value<'_, '_>) -> Option<i64> {
    let operation = OperationResult::try_from(value).ok()?.owner();
    let ident = operation.name();
    let name = ident.as_string_ref().as_str().ok()?;

    if name == "arith.constant" {
        let attr = operation.attribute("value").ok()?;
        return Some(IntegerAttribute::try_from(attr).ok()?.value());
    }

    let lhs = constant_fold_value(operation.operand(0).ok()?)?;
    let rhs = constant_fold_value(operation.operand(1).ok()?)?;
    match name {
        "arith.addi" => lhs.checked_add(rhs),
        "arith.subi" => lhs.checked_sub(rhs),
        "arith.muli" => lhs.checked_mul(rhs),
        _ => None,
    }
}

fn generate_expr_helper<'c, 'a>(
    value: Value<'c, 'a>,
    target_for_loop: Option<OperationRef<'c, 'a>>,
) -> Option<CapabilityExpr<'c, 'a>>
where
    'c: 'a,
{
    if let Ok(argument) = BlockArgument::try_from(value) {
        let owner = argument.owner();

        if let Some(for_loop) = target_for_loop {
            let loop_body = for_loop.first_region()?.first_block()?;
            let iterator: Value<'c, 'a> = loop_body.argument(0).ok()?.into();

            if iterator.to_raw().ptr == value.to_raw().ptr {
                return Some(CapabilityExpr::Variable(value));
            }

            if block_is_inside_operation(owner, for_loop) {
                return None;
            }
        }

        return Some(CapabilityExpr::Blackbox(value));
    }
    let operation = OperationResult::try_from(value).ok()?;
    let operation = operation.owner();

    let is_defined_inside_target = target_for_loop.is_some_and(|for_loop| {
        operation
            .block()
            .is_some_and(|block| block_is_inside_operation(block, for_loop))
    });

    if !is_defined_inside_target {
        return Some(match constant_fold_value(value) {
            Some(value) => CapabilityExpr::Constant(value),
            None => CapabilityExpr::Blackbox(value),
        });
    }

    let ident = operation.name();
    let name = ident.as_string_ref().as_str().unwrap();
    let binop = match name {
        "arith.constant" => {
            let attr = operation.attribute("value").ok()?;
            let value = IntegerAttribute::try_from(attr).ok()?.value();
            return Some(CapabilityExpr::Constant(value));
        }
        "arith.addi" => CapabilityOp::Add,
        "arith.subi" => CapabilityOp::Sub,
        "arith.muli" => CapabilityOp::Mult,
        _ => return None,
    };
    let operands = (
        Rc::new(generate_expr_helper(
            operation.operand(0).unwrap(),
            target_for_loop,
        )?),
        Rc::new(generate_expr_helper(
            operation.operand(1).unwrap(),
            target_for_loop,
        )?),
    );
    Some(CapabilityExpr::BinOp {
        operation: binop,
        operands,
    })
}

pub(super) fn print_return_expressions(module: &Module<'_>) {
    module
        .as_operation()
        .walk(WalkOrder::PreOrder, |operation| {
            let ident = operation.name();
            let name = ident.as_string_ref().as_str().unwrap();

            if name == "func.return" {
                let target_for_loop = find_parent_for(operation);
                for value in operation.operands() {
                    if let Some(expression) = generate_expr(value, target_for_loop) {
                        println!("{expression}");
                    }
                }
            }

            WalkResult::Advance
        });
}

fn push_capability<'c, 'a>(
    capabilities: &mut Vec<Capability<'c, 'a>>,
    capability: Capability<'c, 'a>,
) -> bool {
    let array = capability.array.to_raw().ptr;
    let is_poisoned = capability.capability_expr.is_none();

    if capabilities.iter().any(|existing| {
        existing.array.to_raw().ptr == array
            && existing.capability_expr.is_none()
            && existing.capability_type == CapabilityType::Uniq
    }) {
        return false;
    }

    if is_poisoned && capability.capability_type == CapabilityType::Uniq {
        capabilities.retain(|existing| existing.array.to_raw().ptr != array);
        capabilities.push(capability);
        return true;
    }

    if capability.capability_type == CapabilityType::Shrd
        && capabilities.iter().any(|existing| {
            existing.array.to_raw().ptr == array
                && existing.capability_expr.is_none()
                && existing.capability_type == CapabilityType::Shrd
        })
    {
        return false;
    }

    if is_poisoned && capability.capability_type == CapabilityType::Shrd {
        capabilities.retain(|existing| {
            existing.array.to_raw().ptr != array || existing.capability_type == CapabilityType::Uniq
        });
    }

    capabilities.push(capability);
    true
}
pub(super) fn compute_capabilities<'c, 'a>(module: &'c Module<'c>) -> HashMap<* mut c_void, Vec<Capability<'c, 'a>>>
where 'c: 'a
{
    let mut hashmap = HashMap::new();
    for func in BlockIter::new(module.body()){
        let ident = func.name();
        let name = ident.as_string_ref().as_str().unwrap();
        if name != "func.func" {
            panic!("expected a function found some other operation")
        }
        let mut map  = HashMap::new();
        let mut caps = Vec::new();
        block_capabilities(
            func.region(0).unwrap().first_block().unwrap(), 
            &mut map, &mut caps
        );
        hashmap.extend(map);
        hashmap.insert(func.to_raw().ptr, caps);
    }
    hashmap
}
pub(super) fn block_capabilities<'c, 'a, 'b>(
    block: BlockRef<'c, 'a>,
    capability_map: &mut HashMap<* mut c_void, Vec<Capability<'c, 'a>>>,
    capabilities: &mut Vec<Capability<'c, 'a>>,
) where
    'c: 'a,
{
    println!(
        "[block_capabilities] enter block with {} propagated capabilities",
        capabilities.len()
    );
    let mut current_opt = block.first_operation();
    while let Some(current) = current_opt {
        let ident = current.name();
        let name = ident.as_string_ref().as_str().unwrap();
        println!("[block_capabilities] visiting {name}");
        if name == "memref.load" {
            let array = current.operand(0).unwrap();
            let idx = current.operand(1).unwrap();
            let capability_expr = generate_expr(idx, find_parent_for(current));
            if push_capability(
                capabilities,
                Capability {
                    array,
                    capability_type: CapabilityType::Shrd,
                    capability_expr: capability_expr.map(|x| (x.clone(), x)),
                },
            ) {
                println!(
                    "[block_capabilities] added load capability: {}",
                    capabilities.last().unwrap()
                );
            } else {
                println!("[block_capabilities] load capability already covered");
            }
        } else if name == "memref.store" {
            let array = current.operand(1).unwrap();
            let idx = current.operand(2).unwrap();
            let capability_expr = generate_expr(idx, find_parent_for(current));
            if push_capability(
                capabilities,
                Capability {
                    array,
                    capability_type: CapabilityType::Uniq,
                    capability_expr: capability_expr.map(|x| (x.clone(), x)),
                },
            ) {
                println!(
                    "[block_capabilities] added store capability: {}",
                    capabilities.last().unwrap()
                );
            } else {
                println!("[block_capabilities] store capability already covered");
            }
        } else if name == "scf.if" {
            println!("[block_capabilities] descending into scf.if");
            let mut if_capabilities = Vec::new();
            for region in current.regions() {
                if let Some(sub_block) = region.first_block() {
                    block_capabilities(sub_block, capability_map, &mut if_capabilities);
                }
            }
            capability_map.insert(current.to_raw().ptr, if_capabilities.clone());
            for capability in if_capabilities {
                push_capability(capabilities, capability);
            }
        } else if name == "scf.for" {
            println!("[block_capabilities] collecting inner scf.for capabilities");
            let inner_block = current.first_region().unwrap().first_block().unwrap();
            let mut inner_capabilities = vec![];
            block_capabilities(inner_block, capability_map, &mut inner_capabilities);
            println!(
                "[block_capabilities] scf.for produced {} inner capabilities",
                inner_capabilities.len()
            );
            let lower_bound_var = current.operand(0).unwrap();
            let upper_bound_var = current.operand(1).unwrap();
            let step_var = current.operand(2).unwrap();
            let lower_bound = generate_expr(lower_bound_var, Some(current)).map(Rc::new);
            let upper_bound = generate_expr(upper_bound_var, Some(current)).map(Rc::new);
            let parent_for_loop = find_parent_for(current);
            let is_range_poisoned = lower_bound.is_none() || upper_bound.is_none();
            let step =
                generate_expr(step_var, Some(current)).and_then(|step| step.constant_propagate());
            let iterator: Value<'c, 'a> = inner_block.argument(0).unwrap().into();
            let iteration = CapabilityExpr::Variable(iterator);
            let mut loop_capabilities = Vec::new();

            for capability in inner_capabilities {
                let Capability {
                    array,
                    capability_type,
                    capability_expr,
                } = capability;

                match capability_expr {
                    Some((start, end))
                        if has_iteration_variable(&start) || has_iteration_variable(&end) =>
                    {
                        if is_range_poisoned || step.is_none() {
                            let loop_capability = Capability {
                                array,
                                capability_type,
                                capability_expr: None,
                            };
                            push_capability(&mut loop_capabilities, loop_capability.clone());
                            let inserted = push_capability(
                                capabilities,
                                loop_capability,
                            );
                            println!(
                                "[block_capabilities] poisoned loop capability because a loop bound is unknown; inserted={inserted}"
                            );
                            continue;
                        }

                        let pattern = z3_for_loop_viability(&start, &end, &upper_bound_var);
                        println!("[block_capabilities] loop access pattern: {pattern:?}");

                        for loop_capability in loop_function_capabilities(
                            array,
                            capability_type,
                            &start,
                            &end,
                            lower_bound.as_ref().unwrap(),
                            upper_bound.as_ref().unwrap(),
                            &iteration,
                            pattern,
                            current,
                        ) {
                            push_capability(&mut loop_capabilities, loop_capability);
                        }

                        let inserted = push_capability(
                            capabilities,
                            pattern_to_capabilities(
                                array,
                                capability_type,
                                start,
                                end,
                                Rc::clone(lower_bound.as_ref().unwrap()),
                                Rc::clone(upper_bound.as_ref().unwrap()),
                                pattern,
                                parent_for_loop,
                            ),
                        );
                        if inserted {
                            println!(
                                "[block_capabilities] promoted loop capability: {}",
                                capabilities.last().unwrap()
                            );
                        } else {
                            println!(
                                "[block_capabilities] promoted loop capability already covered"
                            );
                        }
                    }
                    capability_expr => {
                        push_capability(
                            &mut loop_capabilities,
                            Capability {
                                array,
                                capability_type,
                                capability_expr: capability_expr.clone(),
                            },
                        );
                        let inserted = push_capability(
                            capabilities,
                            Capability {
                                array,
                                capability_type,
                                capability_expr,
                            },
                        );
                        if inserted {
                            println!(
                                "[block_capabilities] propagated unchanged capability: {}",
                                capabilities.last().unwrap()
                            );
                        } else {
                            println!("[block_capabilities] unchanged capability already covered");
                        }
                    }
                }
            }
            capability_map.insert(current.to_raw().ptr, loop_capabilities);
        }
        
        current_opt = current.next_in_block();
    }

    println!(
        "[block_capabilities] exit block with {} propagated capabilities: [{}]",
        capabilities.len(),
        format_capabilities(capabilities)
    );
}

fn loop_function_capabilities<'c, 'a>(
    array: Value<'c, 'a>,
    capability_type: CapabilityType,
    x: &CapabilityExpr<'c, 'a>,
    y: &CapabilityExpr<'c, 'a>,
    lower_bound: &CapabilityExpr<'c, 'a>,
    upper_bound_exclusive: &CapabilityExpr<'c, 'a>,
    iteration: &CapabilityExpr<'c, 'a>,
    pattern: Pattern,
    for_loop: OperationRef<'c, 'a>,
) -> Vec<Capability<'c, 'a>> {
    if pattern == Pattern::Poison {
        return vec![Capability {
            array,
            capability_type,
            capability_expr: None,
        }];
    }

    let upper_bound = CapabilityExpr::BinOp {
        operation: CapabilityOp::Sub,
        operands: (
            Rc::new(upper_bound_exclusive.clone()),
            Rc::new(CapabilityExpr::Constant(1)),
        ),
    };

    let promoted = match pattern {
        Pattern::Increasing => {
            let current_start = x.promote(iteration, Some(for_loop));
            let first_start = x.promote(lower_bound, Some(for_loop));
            let last_end = y.promote(&upper_bound, Some(for_loop));
            current_start.zip(first_start).zip(last_end).map(
                |((current_start, first_start), last_end)| {
                    let shared_end = CapabilityExpr::BinOp {
                        operation: CapabilityOp::Sub,
                        operands: (
                            Rc::new(current_start.clone()),
                            Rc::new(CapabilityExpr::Constant(1)),
                        ),
                    };
                    (current_start, last_end, first_start, shared_end)
                },
            )
        }
        Pattern::Decreasing => {
            let current_end = y.promote(iteration, Some(for_loop));
            let last_start = x.promote(&upper_bound, Some(for_loop));
            let first_end = y.promote(lower_bound, Some(for_loop));
            current_end.zip(last_start).zip(first_end).map(
                |((current_end, last_start), first_end)| {
                    let shared_start = CapabilityExpr::BinOp {
                        operation: CapabilityOp::Add,
                        operands: (
                            Rc::new(current_end.clone()),
                            Rc::new(CapabilityExpr::Constant(1)),
                        ),
                    };
                    (last_start, current_end, shared_start, first_end)
                },
            )
        }
        Pattern::Poison => unreachable!(),
    };

    let Some((capability_start, capability_end, shared_start, shared_end)) = promoted
    else {
        return vec![Capability {
            array,
            capability_type,
            capability_expr: None,
        }];
    };

    let mut capabilities = vec![Capability {
        array,
        capability_type,
        capability_expr: Some((capability_start, capability_end)),
    }];

    // if capability_type == CapabilityType::Uniq {
    //     capabilities.push(Capability {
    //         array,
    //         capability_type: CapabilityType::Shrd,
    //         capability_expr: Some((shared_start, shared_end)),
    //     });
    // }

    capabilities
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pattern {
    Increasing,
    Decreasing,
    Poison,
}

fn pattern_to_capabilities<'c, 'a>(
    array: Value<'c, 'a>,
    capability_type: CapabilityType,
    x: CapabilityExpr<'c, 'a>,
    y: CapabilityExpr<'c, 'a>,
    lower_bound: Rc<CapabilityExpr<'c, 'a>>,
    upper_bound_exclusive: Rc<CapabilityExpr<'c, 'a>>,
    pattern: Pattern,
    parent_for_loop: Option<OperationRef<'c, 'a>>,
) -> Capability<'c, 'a> {
    let upper_bound = Rc::new(CapabilityExpr::BinOp {
        operation: CapabilityOp::Sub,
        operands: (upper_bound_exclusive, Rc::new(CapabilityExpr::Constant(1))),
    });
    let capability_expr = match pattern {
        Pattern::Increasing => {
            let x = x.promote(lower_bound.as_ref(), parent_for_loop);
            let y = y.promote(upper_bound.as_ref(), parent_for_loop);
            x.zip(y)
        }
        Pattern::Decreasing => {
            let x = x.promote(upper_bound.as_ref(), parent_for_loop);
            let y = y.promote(lower_bound.as_ref(), parent_for_loop);
            x.zip(y)
        }
        Pattern::Poison => None,
    };
    Capability {
        array,
        capability_type,
        capability_expr,
    }
}
fn coalesce_capabilities<'c, 'a>(capabilities: Vec<Capability<'c, 'a>>){
    let mut capabilities_by_array: HashMap<*const c_void, Capability<'_, '_>> = HashMap::new();
    for capability in capabilities{
        capabilities_by_array.insert(capability.array.to_raw().ptr, capability);
    }

}
fn coalesce_capabilities_by_array<'c, 'a>(capabilities: &Vec<Capability<'c,'a>>){
}
pub(super) fn z3_for_loop_viability<'c, 'a>(
    start: &CapabilityExpr<'c, 'a>,
    end: &CapabilityExpr<'c, 'a>,
    for_loop_end_value: &Value<'c, 'a>,
) -> Pattern {
    let inner_iter_var = ast::Int::new_const("i");
    let next_iter_var = ast::Int::add(&[&inner_iter_var, &ast::Int::from_i64(1)]);
    let for_loop_end = ast::Int::new_const("end");
    let x = start.to_z3(&inner_iter_var, &for_loop_end, for_loop_end_value);
    let y = end.to_z3(&inner_iter_var, &for_loop_end, for_loop_end_value);

    let x_1 = x.substitute(&[(&inner_iter_var, &next_iter_var)]);
    let y_1 = y.substitute(&[(&inner_iter_var, &next_iter_var)]);

    let assumption = Bool::and(&[&inner_iter_var.lt(&for_loop_end)]);
    let growing_counterexample =
        Bool::and(&[&assumption, &Bool::and(&[x.le(&x_1), y.le(&y_1)]).not()]);

    let solver = Solver::new();
    solver.assert(growing_counterexample);
    if solver.check() == SatResult::Unsat {
        return Pattern::Increasing;
    }
    let shrinking_counterexample =
        Bool::and(&[&assumption, &Bool::and(&[x.ge(&x_1), y.ge(&y_1)]).not()]);
    let solver = Solver::new();
    solver.assert(shrinking_counterexample);
    if solver.check() == SatResult::Unsat {
        return Pattern::Decreasing;
    }
    Pattern::Poison
}
