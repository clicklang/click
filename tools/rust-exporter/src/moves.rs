//! Export compiler-owned moves and elaborated drops, never printed MIR.
use super::*;
use rustc_middle::mir::{self, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_span::def_id::LocalDefId;

fn name(local: mir::Local) -> String {
    format!("__rust_mir_{}", local.as_usize())
}
struct Context<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    parameters: BTreeMap<usize, String>,
}
impl<'tcx> Context<'_, 'tcx> {
    fn local(&self, local: mir::Local) -> String {
        self.parameters
            .get(&local.as_usize())
            .cloned()
            .unwrap_or_else(|| name(local))
    }
    fn place(&self, p: mir::Place<'tcx>) -> Result<Expression, String> {
        if matches!(self.body.local_decls[p.local].ty.kind(), ty::Never) {
            return Err("uninhabited MIR place cannot be accessed".into());
        }
        let mut expr = Expression::Local {
            name: self.local(p.local),
        };
        let mut t = self.body.local_decls[p.local].ty;
        for projection in p.projection {
            match projection {
                mir::ProjectionElem::Deref => {
                    let ty::Ref(_, pointee, _) = t.kind() else {
                        return Err("MIR dereference must be a safe reference".into());
                    };
                    expr = Expression::Deref {
                        reference: Box::new(expr),
                        value_type: export_type(self.tcx, *pointee)?,
                    };
                    t = *pointee;
                }
                mir::ProjectionElem::Field(index, field_ty) => {
                    let ty::Adt(def, _) = t.kind() else {
                        return Err("MIR field must belong to a plain struct".into());
                    };
                    expr = Expression::Field {
                        base: Box::new(expr),
                        record: self.tcx.item_name(def.did()).to_string(),
                        field: def.non_enum_variant().fields[index].name.to_string(),
                    };
                    t = field_ty;
                }
                _ => return Err("MIR projection outside move/drop slice".into()),
            }
        }
        Ok(expr)
    }
    fn operand(&self, op: &Operand<'tcx>) -> Result<Expression, String> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => {
                if matches!(op, Operand::Move(_))
                    && !p.projection.is_empty()
                    && matches!(self.body.local_decls[p.local].ty.kind(), ty::Adt(..))
                {
                    return Err("partial moves outside move/drop slice".into());
                }
                if matches!(
                    p.ty(&self.body.local_decls, self.tcx).ty.kind(),
                    ty::Adt(..)
                ) {
                    return Err("aggregate operand needs an explicit move event".into());
                }
                self.place(*p)
            }
            Operand::Constant(c) => {
                let bits = c
                    .const_
                    .try_eval_bits(self.tcx, ty::TypingEnv::fully_monomorphized())
                    .ok_or("unsupported MIR constant")?;
                match c.const_.ty().kind() {
                    ty::Bool => Ok(Expression::Boolean { value: bits != 0 }),
                    ty::Int(ty::IntTy::I32) => Ok(Expression::Integer {
                        value: bits as u32 as i32,
                    }),
                    ty::Uint(ty::UintTy::U8 | ty::UintTy::U16 | ty::UintTy::U32) => {
                        Ok(Expression::UnsignedInteger {
                            value: u32::try_from(bits)
                                .map_err(|_| "MIR unsigned constant outside u32")?,
                            value_type: export_type(self.tcx, c.const_.ty())?,
                        })
                    }
                    _ => Err("MIR constant outside supported integer/bool slice".into()),
                }
            }
            _ => Err("unsupported MIR operand".into()),
        }
    }
    fn statement(&self, s: &mir::Statement<'tcx>) -> Result<Option<MirStatement>, String> {
        match &s.kind {
            StatementKind::Assign(assignment) => {
                let (target, value) = assignment.as_ref();
                let target_type = target.ty(&self.body.local_decls, self.tcx).ty;
                if matches!(target_type.kind(), ty::Tuple(ts) if ts.is_empty()) {
                    return Ok(None);
                }
                if let ty::Adt(def, _) = target_type.kind() {
                    if !target.projection.is_empty() {
                        return Err("partial aggregate assignment outside move/drop slice".into());
                    }
                    let record = self.tcx.item_name(def.did()).to_string();
                    return match value {
                        Rvalue::Aggregate(kind, values) if matches!(kind.as_ref(), mir::AggregateKind::Adt(id, ..) if *id == def.did()) => {
                            Ok(Some(MirStatement::Initialize {
                                target: self.local(target.local),
                                record,
                                fields: values
                                    .iter()
                                    .map(|v| self.operand(v))
                                    .collect::<Result<_, _>>()?,
                            }))
                        }
                        Rvalue::Use(Operand::Move(source), _) if source.projection.is_empty() => {
                            Ok(Some(MirStatement::Move {
                                target: self.local(target.local),
                                source: self.local(source.local),
                                record,
                            }))
                        }
                        _ => Err(
                            "aggregate initialization must be a whole-value constructor or move"
                                .into(),
                        ),
                    };
                }
                let expression = match value {
                    Rvalue::Use(value, _) => self.operand(value)?,
                    Rvalue::Ref(_, _, p) => Expression::Borrow {
                        place: Box::new(self.place(*p)?),
                        value_type: export_type(self.tcx, target_type)?,
                    },
                    Rvalue::BinaryOp(op, values) => {
                        let operator = match op {
                            mir::BinOp::Eq => "eq",
                            mir::BinOp::Ne => "ne",
                            mir::BinOp::Lt => "lt",
                            mir::BinOp::Le => "le",
                            mir::BinOp::Gt => "gt",
                            mir::BinOp::Ge => "ge",
                            _ => {
                                return Err("MIR arithmetic outside initial move/drop slice".into());
                            }
                        };
                        Expression::Binary {
                            operator: operator.into(),
                            left_type: export_type(
                                self.tcx,
                                values.0.ty(&self.body.local_decls, self.tcx),
                            )?,
                            right_type: export_type(
                                self.tcx,
                                values.1.ty(&self.body.local_decls, self.tcx),
                            )?,
                            left: Box::new(self.operand(&values.0)?),
                            right: Box::new(self.operand(&values.1)?),
                        }
                    }
                    _ => return Err("MIR rvalue outside initial move/drop slice".into()),
                };
                Ok(Some(MirStatement::Assign {
                    target: self.place(*target)?,
                    value: expression,
                }))
            }
            StatementKind::StorageDead(local) => Ok(Some(MirStatement::EndStorage {
                local: self.local(*local),
            })),
            StatementKind::StorageLive(_) | StatementKind::Nop => Ok(None),
            _ => Err("MIR statement outside initial move/drop slice".into()),
        }
    }
    fn terminator(&self, t: &mir::Terminator<'tcx>) -> Result<MirTerminator, String> {
        match &t.kind {
            TerminatorKind::Goto { target } => Ok(MirTerminator::Goto {
                target: target.as_usize(),
            }),
            TerminatorKind::Return => Ok(MirTerminator::Return),
            TerminatorKind::Unreachable => Ok(MirTerminator::Unreachable),
            TerminatorKind::SwitchInt { discr, targets } if targets.iter().count() == 1 => {
                let (value, target) = targets.iter().next().unwrap();
                let condition = Expression::Binary {
                    operator: "eq".into(),
                    left_type: export_type(self.tcx, discr.ty(&self.body.local_decls, self.tcx))?,
                    right_type: Type::I32,
                    left: Box::new(self.operand(discr)?),
                    right: Box::new(Expression::Integer {
                        value: i32::try_from(value).map_err(|_| "unsupported MIR switch value")?,
                    }),
                };
                Ok(MirTerminator::If {
                    condition,
                    then_target: target.as_usize(),
                    else_target: targets.otherwise().as_usize(),
                })
            }
            TerminatorKind::Drop {
                place,
                target,
                drop: None,
                ..
            } if place.projection.is_empty() => {
                let ty::Adt(def, _) = self.body.local_decls[place.local].ty.kind() else {
                    return Err("only plain struct drops are supported".into());
                };
                Ok(MirTerminator::Drop {
                    local: self.local(place.local),
                    record: self.tcx.item_name(def.did()).to_string(),
                    target: target.as_usize(),
                })
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } => {
                let ty::FnDef(id, _) = func.ty(&self.body.local_decls, self.tcx).kind() else {
                    return Err("MIR calls must resolve to functions".into());
                };
                if self.tcx.is_diagnostic_item(rustc_span::sym::mem_drop, *id) {
                    let [argument] = args.as_ref() else {
                        return Err("invalid mem::drop arity".into());
                    };
                    let Operand::Move(place) = argument.node else {
                        return Err("mem::drop must consume a whole owned value".into());
                    };
                    if !place.projection.is_empty() {
                        return Err("partial moves outside move/drop slice".into());
                    }
                    let ty::Adt(def, _) = self.body.local_decls[place.local].ty.kind() else {
                        return Err("mem::drop supports plain owned structs".into());
                    };
                    return Ok(MirTerminator::Drop {
                        local: self.local(place.local),
                        record: self.tcx.item_name(def.did()).to_string(),
                        target: target.as_usize(),
                    });
                }
                if !id.is_local() || !destination.projection.is_empty() {
                    return Err("MIR call outside direct local scalar/reference calls".into());
                }
                Ok(MirTerminator::Call {
                    function: self.tcx.item_name(*id).to_string(),
                    arguments: args
                        .iter()
                        .map(|a| self.operand(&a.node))
                        .collect::<Result<_, _>>()?,
                    destination: self.local(destination.local),
                    target: target.as_usize(),
                })
            }
            _ => Err(format!(
                "MIR terminator outside initial move/drop slice at {}:{}",
                span(self.tcx, t.source_info.span).line,
                span(self.tcx, t.source_info.span).column
            )),
        }
    }
}
pub(super) fn body<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: LocalDefId,
    parameters: &[Place],
) -> Result<MirBody, String> {
    // Borrowing this query's body does not steal it or require optimization.
    // Drop flags and actual cleanup destinations come from rustc.
    let body = tcx.mir_drops_elaborated_and_const_checked(id).borrow();
    let cx = Context {
        tcx,
        body: &body,
        parameters: parameters
            .iter()
            .enumerate()
            .map(|(i, p)| (i + 1, p.name.clone()))
            .collect(),
    };
    let locals = body
        .local_decls
        .iter_enumerated()
        .filter(|(local, _)| local.as_usize() == 0 || local.as_usize() > body.arg_count)
        .map(|(local, decl)| {
            Ok(Place {
                name: name(local),
                value_type: if matches!(decl.ty.kind(), ty::Never) {
                    Type::Unit
                } else {
                    export_type(tcx, decl.ty)?
                },
                span: span(tcx, decl.source_info.span),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let blocks = body
        .basic_blocks
        .iter()
        .map(|block| {
            Ok(MirBlock {
                statements: if block.is_cleanup {
                    Vec::new()
                } else {
                    block
                        .statements
                        .iter()
                        .filter_map(|s| cx.statement(s).transpose())
                        .collect::<Result<_, _>>()?
                },
                terminator: if block.is_cleanup {
                    MirTerminator::Unreachable
                } else {
                    cx.terminator(block.terminator())?
                },
            })
        })
        .collect::<Result<_, String>>()?;
    Ok(MirBody { locals, blocks })
}
