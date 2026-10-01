#![feature(rustc_private)]
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::{self as hir, def::Res};
use rustc_middle::ty::{self, TyCtxt};
use std::collections::{BTreeMap, BTreeSet};
#[path = "../../../src/languages/rust/schema.rs"]
mod schema;
use schema::*;
mod moves;

struct Exporter {
    logical_source: String,
    result: Option<Result<RustExport, String>>,
}
// Refuse untracked module files, expansion inputs and ambient configuration
// before expansion. This first slice is exactly one ordinary source file.
struct SourceBoundary {
    invalid: bool,
}
impl<'a> rustc_ast::visit::Visitor<'a> for SourceBoundary {
    fn visit_item(&mut self, item: &'a rustc_ast::Item) {
        if !matches!(
            item.kind,
            rustc_ast::ItemKind::Fn(_)
                | rustc_ast::ItemKind::Struct(..)
                | rustc_ast::ItemKind::Impl(_)
        ) {
            self.invalid = true;
        }
        if let rustc_ast::ItemKind::Impl(implementation) = &item.kind {
            match &implementation.of_trait {
                Some(header)
                    if !matches!(header.safety, rustc_ast::Safety::Unsafe(_))
                        && header
                            .trait_ref
                            .path
                            .segments
                            .last()
                            .is_some_and(|segment| segment.ident.name.as_str() == "Drop") => {}
                _ => self.invalid = true,
            }
        }
        rustc_ast::visit::walk_item(self, item);
    }
    fn visit_attribute(&mut self, attr: &'a rustc_ast::Attribute) {
        if !attr.is_doc_comment() {
            self.invalid = true;
        }
    }
    fn visit_mac_call(&mut self, _: &'a rustc_ast::MacCall) {
        self.invalid = true;
    }
}
impl Callbacks for Exporter {
    fn after_crate_root_parsing(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        krate: &mut rustc_ast::Crate,
    ) -> Compilation {
        use rustc_ast::visit::Visitor;
        let mut boundary = SourceBoundary { invalid: false };
        boundary.visit_crate(krate);
        if boundary.invalid {
            self.result = Some(Err("Rust source boundary supports one file containing functions and structs; modules, macros, imports and attributes are unsupported".into()));
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        self.result = Some(export(tcx, &self.logical_source));
        Compilation::Stop
    }
}
fn span(tcx: TyCtxt<'_>, s: rustc_span::Span) -> Span {
    let loc = tcx.sess.source_map().lookup_char_pos(s.lo());
    Span {
        line: loc.line,
        column: loc.col.0 + 1,
    }
}
fn export_type<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<Type, String> {
    match t.kind() {
        ty::Int(ty::IntTy::I32) => Ok(Type::I32),
        ty::Uint(ty::UintTy::U8) => Ok(Type::U8),
        ty::Uint(ty::UintTy::U32) => Ok(Type::U32),
        ty::Uint(ty::UintTy::Usize) => Ok(Type::Usize),
        ty::Array(element, length) => {
            let element = export_type(tcx, *element)?;
            if !matches!(element, Type::I32 | Type::U8 | Type::U32) {
                return Err("fixed arrays require i32, u8 or u32 elements".into());
            }
            let length = tcx
                .normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    ty::Unnormalized::new_wip(*length),
                )
                .try_to_target_usize(tcx)
                .ok_or("fixed array length must be concrete")?;
            let width = if element == Type::U8 { 1 } else { 4 };
            if length > i32::MAX as u64 / width {
                return Err("fixed array storage exceeds the signed-word memory model".into());
            }
            Ok(Type::Array {
                element: Box::new(element),
                length,
            })
        }
        ty::Bool => Ok(Type::Bool),
        ty::Tuple(ts) if ts.is_empty() => Ok(Type::Unit),
        ty::Ref(_, p, m) => {
            if matches!(p.kind(), ty::Slice(element) if matches!(element.kind(), ty::Uint(ty::UintTy::U8)))
            {
                return Ok(Type::ByteSlice {
                    mutable: m.is_mut(),
                });
            }
            let pointee = export_type(tcx, *p)?;
            if !matches!(
                pointee,
                Type::I32 | Type::U8 | Type::U32 | Type::Record { .. } | Type::Array { .. }
            ) {
                return Err("reference pointee outside Rust slice".into());
            }
            Ok(Type::Reference {
                mutable: m.is_mut(),
                pointee: Box::new(pointee),
            })
        }
        ty::Adt(def, args)
            if def.is_struct()
                && args
                    .iter()
                    .all(|a| matches!(a.kind(), ty::GenericArgKind::Lifetime(_)))
                && def.did().is_local() =>
        {
            Ok(Type::Record {
                name: tcx.item_name(def.did()).to_string(),
            })
        }
        _ => Err(format!("unsupported Rust type `{t}`")),
    }
}
struct BodyExporter<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    locals: BTreeMap<u32, String>,
    names: BTreeSet<String>,
    immutable: BTreeSet<u32>,
}
fn indexed_type(t: &Type) -> bool {
    matches!(t, Type::ByteSlice { .. } | Type::Array { .. })
        || matches!(t, Type::Reference { pointee, .. } if matches!(pointee.as_ref(), Type::Array { .. }))
}
impl<'tcx> BodyExporter<'tcx> {
    fn error(&self, e: &hir::Expr<'_>, message: &str) -> String {
        let s = span(self.tcx, e.span);
        format!("Rust source {}:{}: {message}", s.line, s.column)
    }
    fn bind(&mut self, p: &hir::Pat<'tcx>, parameter: bool) -> Result<String, String> {
        if let hir::PatKind::Binding(mode, id, ident, None) = p.kind {
            if mode.0 != hir::ByRef::No {
                return Err("ref patterns outside Rust slice".into());
            }
            let source_name = ident.to_string();
            let name = if parameter
                || (!source_name.starts_with("__rust_") && !self.names.contains(&source_name))
            {
                source_name
            } else {
                format!("__rust_{}_{}", ident, id.local_id.as_u32())
            };
            self.names.insert(name.clone());
            self.locals.insert(id.local_id.as_u32(), name.clone());
            if mode.1 == hir::Mutability::Not {
                self.immutable.insert(id.local_id.as_u32());
            }
            Ok(name)
        } else {
            Err("only plain Rust binding patterns are supported".into())
        }
    }
    fn expr(&self, e: &hir::Expr<'tcx>) -> Result<Expression, String> {
        self.adjusted_expr(e, false)
    }
    fn adjusted_expr(&self, e: &hir::Expr<'tcx>, array_length: bool) -> Result<Expression, String> {
        // Built-in reference deref/reborrow adjustments keep the same address.
        // Array unsizing carries the fixed length into byte-slice metadata.
        // Refuse trait-driven deref and other pointer coercions.
        use ty::adjustment::{Adjust, AutoBorrow, DerefAdjustKind, PointerCoercion};
        let value_type =
            export_type(self.tcx, self.typeck.expr_ty(e)).map_err(|m| self.error(e, &m))?;
        let fixed_array = matches!(value_type, Type::Array { .. })
            || matches!(&value_type, Type::Reference { pointee, .. } if matches!(pointee.as_ref(), Type::Array { .. }));
        let mut slice_coercion = None;
        for adjustment in self.typeck.expr_adjustments(e) {
            if matches!(adjustment.kind, Adjust::Pointer(PointerCoercion::Unsize)) && fixed_array {
                if !array_length {
                    let Type::ByteSlice { mutable } = export_type(self.tcx, adjustment.target)?
                    else {
                        return Err(self.error(e, "array coercion requires a byte slice"));
                    };
                    slice_coercion = Some(mutable);
                }
                continue;
            }
            if !matches!(
                adjustment.kind,
                Adjust::Deref(DerefAdjustKind::Builtin) | Adjust::Borrow(AutoBorrow::Ref(..))
            ) {
                return Err(self.error(e, "implicit adjustment outside Rust slice"));
            }
        }
        let t = self.typeck.expr_ty(e);
        let expression = match e.kind {
            hir::ExprKind::DropTemps(value) => self.expr(value),
            hir::ExprKind::Array(elements) => Ok(Expression::Array {
                elements: elements
                    .iter()
                    .map(|e| self.expr(e))
                    .collect::<Result<_, _>>()?,
            }),
            hir::ExprKind::Repeat(value, _) => {
                let Type::Array { length, .. } = export_type(self.tcx, t)? else {
                    return Err(self.error(e, "array repeat requires a fixed array type"));
                };
                Ok(Expression::Repeat {
                    value: Box::new(self.expr(value)?),
                    length,
                })
            }
            hir::ExprKind::Lit(lit) => match lit.node {
                rustc_ast::LitKind::Int(v, _) => match export_type(self.tcx, t)? {
                    value_type @ (Type::U8 | Type::U32) => Ok(Expression::UnsignedInteger {
                        value: u32::try_from(v.get())
                            .map_err(|_| self.error(e, "unsigned literal outside u32"))?,
                        value_type,
                    }),
                    Type::Usize => Ok(Expression::UsizeInteger {
                        value: u64::try_from(v.get())
                            .map_err(|_| self.error(e, "usize literal outside target width"))?,
                    }),
                    Type::I32 => Ok(Expression::Integer {
                        value: i32::try_from(v.get())
                            .map_err(|_| self.error(e, "integer literal outside i32"))?,
                    }),
                    _ => Err(self.error(e, "unsupported integer literal type")),
                },
                rustc_ast::LitKind::Bool(value) => Ok(Expression::Boolean { value }),
                _ => Err(self.error(e, "unsupported Rust literal")),
            },
            hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
                Res::Local(id) => Ok(Expression::Local {
                    name: self
                        .locals
                        .get(&id.local_id.as_u32())
                        .ok_or_else(|| self.error(e, "unbound Rust local"))?
                        .clone(),
                }),
                _ => Err(self.error(e, "only resolved local values are supported")),
            },
            hir::ExprKind::MethodCall(_, receiver, args, _) => {
                if self.typeck.type_dependent_def_id(e.hir_id)
                    != self.tcx.lang_items().slice_len_fn()
                    || !args.is_empty()
                    || !indexed_type(&export_type(self.tcx, self.typeck.expr_ty(receiver))?)
                {
                    return Err(
                        self.error(e, "only builtin byte-slice or fixed-array len is supported")
                    );
                }
                Ok(Expression::SliceLength {
                    slice: Box::new(self.adjusted_expr(receiver, true)?),
                })
            }
            hir::ExprKind::Index(base, index, _) => {
                if self.typeck.type_dependent_def_id(e.hir_id).is_some()
                    || !indexed_type(&export_type(self.tcx, self.typeck.expr_ty(base))?)
                    || !matches!(
                        self.typeck.expr_ty(index).kind(),
                        ty::Uint(ty::UintTy::Usize)
                    )
                {
                    return Err(self.error(
                        e,
                        "only builtin byte-slice or fixed-array usize indexing is supported",
                    ));
                }
                Ok(Expression::Index {
                    slice: Box::new(self.expr(base)?),
                    index: Box::new(self.expr(index)?),
                })
            }
            hir::ExprKind::Binary(op, l, r) => {
                if self.typeck.type_dependent_def_id(e.hir_id).is_some() {
                    return Err(self.error(e, "overloaded operators outside Rust slice"));
                }
                let operator = match op.node {
                    hir::BinOpKind::Add => "add",
                    hir::BinOpKind::Sub => "sub",
                    hir::BinOpKind::Mul => "mul",
                    hir::BinOpKind::Div => "div",
                    hir::BinOpKind::Rem => "rem",
                    hir::BinOpKind::Shl => "shl",
                    hir::BinOpKind::Shr => "shr",
                    hir::BinOpKind::BitAnd => "bit_and",
                    hir::BinOpKind::BitOr => "bit_or",
                    hir::BinOpKind::BitXor => "bit_xor",
                    hir::BinOpKind::Eq => "eq",
                    hir::BinOpKind::Ne => "ne",
                    hir::BinOpKind::Lt => "lt",
                    hir::BinOpKind::Le => "le",
                    hir::BinOpKind::Gt => "gt",
                    hir::BinOpKind::Ge => "ge",
                    hir::BinOpKind::And => "and",
                    hir::BinOpKind::Or => "or",
                };
                if matches!(operator, "shl" | "shr")
                    && !matches!(
                        export_type(self.tcx, self.typeck.expr_ty(l))?,
                        Type::U8 | Type::U32 | Type::Usize
                    )
                {
                    return Err(self.error(e, "Rust shifts require u8, u32 or usize operands"));
                }
                Ok(Expression::Binary {
                    operator: operator.into(),
                    left_type: export_type(self.tcx, self.typeck.expr_ty(l))?,
                    right_type: export_type(self.tcx, self.typeck.expr_ty(r))?,
                    left: Box::new(self.expr(l)?),
                    right: Box::new(self.expr(r)?),
                })
            }
            hir::ExprKind::Unary(hir::UnOp::Not, v) if t.is_bool() => Ok(Expression::Not {
                value: Box::new(self.expr(v)?),
            }),
            hir::ExprKind::Unary(hir::UnOp::Not, v) if t.is_integral() => {
                Ok(Expression::BitwiseNot {
                    value: Box::new(self.expr(v)?),
                    value_type: export_type(self.tcx, t)?,
                })
            }
            hir::ExprKind::Cast(value, _) if t.is_integral() => Ok(Expression::Cast {
                value: Box::new(self.expr(value)?),
                value_type: export_type(self.tcx, t)?,
            }),
            hir::ExprKind::Unary(hir::UnOp::Neg, v)
                if matches!(t.kind(), ty::Int(ty::IntTy::I32)) =>
            {
                Ok(Expression::Binary {
                    operator: "sub".into(),
                    left_type: Type::I32,
                    right_type: Type::I32,
                    left: Box::new(Expression::Integer { value: 0 }),
                    right: Box::new(self.expr(v)?),
                })
            }
            hir::ExprKind::Unary(hir::UnOp::Deref, v)
                if matches!(self.typeck.expr_ty(v).kind(), ty::Ref(..)) =>
            {
                Ok(Expression::Deref {
                    reference: Box::new(self.expr(v)?),
                    value_type: export_type(self.tcx, t)?,
                })
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, _, v)
                if matches!(export_type(self.tcx, t)?, Type::ByteSlice { .. }) =>
            {
                if let hir::ExprKind::Unary(hir::UnOp::Deref, reference) = v.kind {
                    self.expr(reference)
                } else {
                    Err(self.error(e, "slice reborrow requires a slice reference"))
                }
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, _, v) => Ok(Expression::Borrow {
                place: Box::new(self.expr(v)?),
                value_type: export_type(self.tcx, t)?,
            }),
            hir::ExprKind::Field(base, field) => {
                let base_type = self.typeck.expr_ty(base).peel_refs();
                let ty::Adt(def, _) = base_type.kind() else {
                    return Err(self.error(e, "unsupported field base"));
                };
                Ok(Expression::Field {
                    base: Box::new(self.expr(base)?),
                    record: self.tcx.item_name(def.did()).to_string(),
                    field: field.to_string(),
                })
            }
            hir::ExprKind::Call(callee, args) => {
                let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = callee.kind else {
                    return Err(self.error(e, "only direct calls are supported"));
                };
                let Res::Def(hir::def::DefKind::Fn, id) = path.res else {
                    return Err(self.error(e, "unsupported Rust call target"));
                };
                if !id.is_local() {
                    return Err(self.error(e, "external calls outside Rust slice"));
                }
                Ok(Expression::Call {
                    function: self.tcx.item_name(id).to_string(),
                    arguments: args
                        .iter()
                        .map(|a| self.expr(a))
                        .collect::<Result<_, _>>()?,
                })
            }
            _ => Err(self.error(e, "expression outside the supported typed Rust subset")),
        }?;
        Ok(match slice_coercion {
            Some(mutable) => Expression::ArrayToSlice {
                array: Box::new(expression),
                mutable,
            },
            None => expression,
        })
    }
    fn block(&mut self, b: &hir::Block<'tcx>, tail_return: bool) -> Result<Vec<Statement>, String> {
        if !matches!(b.rules, hir::BlockCheckMode::DefaultBlock) {
            return Err("unsafe blocks outside Rust slice".into());
        }
        let mut out = Vec::new();
        for s in b.stmts {
            match s.kind {
                hir::StmtKind::Let(local) => {
                    if local.els.is_some() {
                        return Err("let-else outside Rust slice".into());
                    }
                    let init = local
                        .init
                        .ok_or("uninitialized locals outside Rust slice")?;
                    let initializer = self.expr(init)?;
                    let name = self.bind(local.pat, false)?;
                    out.push(Statement::Declare {
                        place: Place {
                            name,
                            value_type: export_type(self.tcx, self.typeck.pat_ty(local.pat))?,
                            span: span(self.tcx, local.span),
                        },
                        initializer,
                    });
                }
                hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => {
                    out.extend(self.statement(e, false)?)
                }
                _ => return Err("local items outside Rust slice".into()),
            }
        }
        if let Some(e) = b.expr {
            out.extend(self.statement(e, tail_return)?);
        } else if tail_return {
            out.push(Statement::Return { value: None });
        }
        Ok(out)
    }
    // Recognize the pinned compiler's for desugaring, never user call names.
    // Only copied byte bindings from an immutable shared slice are supported.
    fn slice_for(
        &mut self,
        e: &hir::Expr<'tcx>,
        tail_return: bool,
    ) -> Result<Vec<Statement>, String> {
        let bad = || {
            self.error(e, "Rust for loops currently require `for &byte in slice` with an immutable shared byte-slice binding")
        };
        let hir::ExprKind::Match(input, [outer], hir::MatchSource::ForLoopDesugar) = e.kind else {
            return Err(bad());
        };
        let hir::ExprKind::Call(callee, [slice]) = input.kind else {
            return Err(bad());
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = callee.kind else {
            return Err(bad());
        };
        if !matches!(path.res, Res::Def(_, id) if Some(id) == self.tcx.lang_items().into_iter_fn())
        {
            return Err(bad());
        }
        let hir::ExprKind::Path(hir::QPath::Resolved(_, source)) = slice.kind else {
            return Err(bad());
        };
        if !matches!(source.res, Res::Local(id) if self.immutable.contains(&id.local_id.as_u32()))
            || export_type(self.tcx, self.typeck.expr_ty(slice))?
                != (Type::ByteSlice { mutable: false })
        {
            return Err(bad());
        }
        let hir::PatKind::Binding(_, iterator_id, _, None) = outer.pat.kind else {
            return Err(bad());
        };
        let hir::ExprKind::Loop(block, None, hir::LoopSource::ForLoop, _) = outer.body.kind else {
            return Err(bad());
        };
        let [statement] = block.stmts else {
            return Err(bad());
        };
        let hir::StmtKind::Expr(next_match) = statement.kind else {
            return Err(bad());
        };
        let hir::ExprKind::Match(next, [none, some], hir::MatchSource::ForLoopDesugar) =
            next_match.kind
        else {
            return Err(bad());
        };
        let hir::ExprKind::Call(next_callee, [borrow]) = next.kind else {
            return Err(bad());
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, next_path)) = next_callee.kind else {
            return Err(bad());
        };
        let hir::ExprKind::AddrOf(hir::BorrowKind::Ref, hir::Mutability::Mut, iter) = borrow.kind
        else {
            return Err(bad());
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, iter_path)) = iter.kind else {
            return Err(bad());
        };
        if !matches!(next_path.res, Res::Def(_, id) if Some(id) == self.tcx.lang_items().next_fn())
            || iter_path.res != Res::Local(iterator_id)
        {
            return Err(bad());
        }
        let hir::PatKind::Struct(hir::QPath::Resolved(_, none_path), [], _) = none.pat.kind else {
            return Err(bad());
        };
        let hir::PatKind::Struct(hir::QPath::Resolved(_, some_path), [field], _) = some.pat.kind
        else {
            return Err(bad());
        };
        if !matches!(none_path.res, Res::Def(_, id) if Some(id) == self.tcx.lang_items().option_none_variant())
            || !matches!(some_path.res, Res::Def(_, id) if Some(id) == self.tcx.lang_items().option_some_variant())
            || !matches!(none.body.kind, hir::ExprKind::Break(destination, None) if destination.target_id == Ok(outer.body.hir_id))
            || outer.guard.is_some()
            || none.guard.is_some()
            || some.guard.is_some()
            || block.expr.is_some()
        {
            return Err(bad());
        }
        let hir::PatKind::Ref(binding, hir::Pinnedness::Not, hir::Mutability::Not) = field.pat.kind
        else {
            return Err(bad());
        };
        if export_type(self.tcx, self.typeck.pat_ty(binding))? != Type::U8 {
            return Err(bad());
        }
        let slice = self.expr(slice)?;
        let location = span(self.tcx, e.span);
        let index = format!("__rust_iter_index_{}_{}", location.line, location.column);
        if !self.names.insert(index.clone()) {
            return Err("duplicate Rust iterator identity".into());
        }
        let byte = self.bind(binding, false)?;
        let local = Expression::Local {
            name: index.clone(),
        };
        let mut body = vec![Statement::Declare {
            place: Place {
                name: byte,
                value_type: Type::U8,
                span: span(self.tcx, binding.span),
            },
            initializer: Expression::Index {
                slice: Box::new(slice.clone()),
                index: Box::new(local.clone()),
            },
        }];
        body.extend(self.statement(some.body, false)?);
        body.push(Statement::Assign {
            target: local.clone(),
            value: Expression::Binary {
                operator: "add".into(),
                left_type: Type::Usize,
                right_type: Type::Usize,
                left: Box::new(local.clone()),
                right: Box::new(Expression::UsizeInteger { value: 1 }),
            },
        });
        let mut statements = vec![
            Statement::Declare {
                place: Place {
                    name: index,
                    value_type: Type::Usize,
                    span: location,
                },
                initializer: Expression::UsizeInteger { value: 0 },
            },
            Statement::While {
                condition: Expression::Binary {
                    operator: "lt".into(),
                    left_type: Type::Usize,
                    right_type: Type::Usize,
                    left: Box::new(local),
                    right: Box::new(Expression::SliceLength {
                        slice: Box::new(slice),
                    }),
                },
                body,
            },
        ];
        if tail_return {
            statements.push(Statement::Return { value: None });
        }
        Ok(statements)
    }
    fn statement(
        &mut self,
        e: &hir::Expr<'tcx>,
        tail_return: bool,
    ) -> Result<Vec<Statement>, String> {
        match e.kind {
            hir::ExprKind::Block(b, None) => self.block(b, tail_return),
            hir::ExprKind::Match(_, _, hir::MatchSource::ForLoopDesugar) => {
                self.slice_for(e, tail_return)
            }
            hir::ExprKind::Loop(block, None, hir::LoopSource::While, _) => {
                let Some(guard) = block.expr else {
                    return Err(self.error(e, "unexpected rustc while shape"));
                };
                let hir::ExprKind::If(condition, body, Some(_)) = guard.kind else {
                    return Err(self.error(e, "unexpected rustc while guard"));
                };
                let mut statements = vec![Statement::While {
                    condition: self.expr(condition)?,
                    body: self.statement(body, false)?,
                }];
                if tail_return {
                    statements.push(Statement::Return { value: None });
                }
                Ok(statements)
            }
            hir::ExprKind::Loop(..) => {
                Err(self.error(e, "only unlabeled Rust while loops are supported"))
            }
            hir::ExprKind::Break(..) | hir::ExprKind::Continue(..) => {
                Err(self.error(e, "Rust break and continue are not yet supported"))
            }
            hir::ExprKind::If(c, t, f) => Ok(vec![Statement::If {
                condition: self.expr(c)?,
                then_body: self.statement(t, tail_return)?,
                else_body: match f {
                    Some(f) => self.statement(f, tail_return)?,
                    None if tail_return => {
                        return Err(self.error(e, "value-returning if needs both branches"));
                    }
                    None => Vec::new(),
                },
            }]),
            hir::ExprKind::Ret(value) => Ok(vec![Statement::Return {
                value: value.map(|v| self.expr(v)).transpose()?,
            }]),
            hir::ExprKind::Assign(target, value, _) => Ok(vec![Statement::Assign {
                target: self.expr(target)?,
                value: self.expr(value)?,
            }]),
            hir::ExprKind::AssignOp(op, target, value) => {
                if self.typeck.type_dependent_def_id(e.hir_id).is_some() {
                    return Err(self.error(e, "overloaded assignment outside Rust slice"));
                }
                let operator = match op.node {
                    hir::AssignOpKind::AddAssign => "add",
                    hir::AssignOpKind::SubAssign => "sub",
                    hir::AssignOpKind::MulAssign => "mul",
                    hir::AssignOpKind::DivAssign => "div",
                    hir::AssignOpKind::RemAssign => "rem",
                    hir::AssignOpKind::ShlAssign => "shl",
                    hir::AssignOpKind::ShrAssign => "shr",
                    hir::AssignOpKind::BitAndAssign => "bit_and",
                    hir::AssignOpKind::BitOrAssign => "bit_or",
                    hir::AssignOpKind::BitXorAssign => "bit_xor",
                };
                let left_type = export_type(self.tcx, self.typeck.expr_ty(target))?;
                if matches!(target.kind, hir::ExprKind::Index(..)) {
                    return Err(
                        self.error(e, "indexed compound assignments outside Rust slice support")
                    );
                }
                let right_type = export_type(self.tcx, self.typeck.expr_ty(value))?;
                let target = self.expr(target)?;
                Ok(vec![Statement::Assign {
                    value: Expression::Binary {
                        operator: operator.into(),
                        left_type,
                        right_type,
                        left: Box::new(target.clone()),
                        right: Box::new(self.expr(value)?),
                    },
                    target,
                }])
            }
            hir::ExprKind::DropTemps(value) => self.statement(value, tail_return),
            _ if tail_return => Ok(vec![Statement::Return {
                value: Some(self.expr(e)?),
            }]),
            _ => match self.expr(e)? {
                Expression::Call {
                    function,
                    arguments,
                } => Ok(vec![Statement::Call {
                    function,
                    arguments,
                }]),
                _ => Err(self.error(e, "discarded expressions outside Rust slice")),
            },
        }
    }
}
fn export(tcx: TyCtxt<'_>, logical: &str) -> Result<RustExport, String> {
    let mut functions = Vec::new();
    let mut records = BTreeMap::new();
    for id in tcx.hir_body_owners() {
        // Array dimensions are compiler-evaluated constants, not executable
        // functions. Their values are exported from the resolved array type.
        if tcx.def_kind(id) == hir::def::DefKind::AnonConst {
            continue;
        }
        let destructor = if tcx.def_kind(id) == hir::def::DefKind::AssocFn {
            let implementation = tcx.parent(id.to_def_id());
            if !matches!(
                tcx.def_kind(implementation),
                hir::def::DefKind::Impl { of_trait: true }
            ) || Some(
                tcx.impl_trait_ref(implementation)
                    .instantiate_identity()
                    .skip_norm_wip()
                    .def_id,
            ) != tcx.lang_items().drop_trait()
            {
                return Err("only Drop trait methods are supported".into());
            }
            let self_type = tcx
                .type_of(implementation)
                .instantiate_identity()
                .skip_norm_wip();
            Some(format!(
                "{}_drop",
                tcx.item_name(
                    self_type
                        .ty_adt_def()
                        .ok_or("Drop self must be a struct")?
                        .did()
                )
            ))
        } else {
            None
        };
        if tcx.def_kind(id) != hir::def::DefKind::Fn && destructor.is_none() {
            return Err("only free Rust functions and Drop implementations are supported".into());
        }
        let sig = tcx.fn_sig(id).instantiate_identity().skip_binder();
        if sig.safety().is_unsafe()
            || tcx
                .generics_of(id)
                .own_params
                .iter()
                .any(|p| !matches!(p.kind, ty::GenericParamDefKind::Lifetime))
        {
            return Err("unsafe or generic functions outside Rust slice".into());
        }
        let body = tcx.hir_body_owned_by(id);
        let typeck = tcx.typeck(id);
        let mut cx = BodyExporter {
            tcx,
            typeck,
            locals: BTreeMap::new(),
            names: BTreeSet::new(),
            immutable: BTreeSet::new(),
        };
        let parameters = body
            .params
            .iter()
            .zip(sig.inputs())
            .map(|(p, t)| {
                Ok(Place {
                    name: cx.bind(p.pat, true)?,
                    value_type: export_type(tcx, *t)?,
                    span: span(tcx, p.span),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let mir = tcx.mir_drops_elaborated_and_const_checked(id).borrow();
        // Standard iterator and Option temporaries belong to the checked HIR
        // desugaring, not the local-record ownership frontend. Unsupported
        // external values still fail typed HIR expression/type export.
        let owned = mir
            .local_decls
            .iter()
            .any(|d| matches!(d.ty.kind(), ty::Adt(def, _) if def.did().is_local()));
        let types = sig
            .inputs()
            .iter()
            .copied()
            .chain(mir.local_decls.iter().map(|d| d.ty));
        for t in types {
            let t = t.peel_refs();
            if let ty::Adt(def, _) = t.kind() {
                if !def.did().is_local() {
                    continue;
                }
                let name = tcx.item_name(def.did()).to_string();
                if records.contains_key(&name) {
                    continue;
                }
                let layout = tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(t))
                    .map_err(|e| format!("Rust layout: {e:?}"))?;
                let mut fields = Vec::new();
                for (i, f) in def.non_enum_variant().fields.iter_enumerated() {
                    let value_type = export_type(
                        tcx,
                        f.ty(tcx, ty::GenericArgs::identity_for_item(tcx, def.did()))
                            .skip_norm_wip(),
                    )?;
                    if !matches!(
                        value_type,
                        Type::I32 | Type::U8 | Type::U32 | Type::Reference { .. }
                    ) {
                        return Err("struct fields must be supported integers or references".into());
                    }
                    fields.push(Field {
                        name: f.name.to_string(),
                        value_type,
                        offset: u32::try_from(layout.fields.offset(i.index()).bytes())
                            .map_err(|_| "field offset too large")?,
                    });
                }
                records.insert(
                    name.clone(),
                    Record {
                        name: name.clone(),
                        size: u32::try_from(layout.size.bytes())
                            .map_err(|_| "record size too large")?,
                        alignment: u32::try_from(layout.align.abi.bytes())
                            .map_err(|_| "alignment too large")?,
                        fields,
                        destructor: def.destructor(tcx).map(|_| format!("{name}_drop")),
                    },
                );
            }
        }
        drop(mir);
        if owned
            && parameters
                .iter()
                .any(|p| matches!(p.value_type, Type::ByteSlice { .. }))
        {
            return Err("byte slices in owned-value MIR functions are unsupported".into());
        }
        let mir_body = if owned {
            Some(moves::body(tcx, id, &parameters)?)
        } else {
            None
        };
        let statements = if owned {
            Vec::new()
        } else {
            cx.statement(body.value, true)?
        };
        functions.push(Function {
            name: destructor.unwrap_or_else(|| tcx.item_name(id.to_def_id()).to_string()),
            return_type: export_type(tcx, sig.output())?,
            parameters,
            body: statements,
            mir: mir_body,
            span: span(tcx, body.value.span),
        });
    }
    if functions.is_empty() {
        return Err("Rust input has no supported functions".into());
    }
    Ok(RustExport {
        schema: SCHEMA,
        compiler_commit: COMPILER_COMMIT.into(),
        target: TARGET.into(),
        edition: "2024".into(),
        overflow_checks: true,
        panic: "abort".into(),
        mir_opt_level: 0,
        logical_source: logical.into(),
        records: records.into_values().collect(),
        functions,
    })
}
fn main() {
    let mut args = std::env::args().skip(1);
    let source = args.next().expect("source path");
    let logical_source = args.next().expect("logical source");
    let sysroot = env!("CLICK_RUST_SYSROOT").to_string();
    assert!(args.next().is_none(), "unexpected exporter arguments");
    let mut exporter = Exporter {
        logical_source,
        result: None,
    };
    let args = vec![
        "rustc".into(),
        source,
        "--crate-name=click_rust_input".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        format!("--target={TARGET}"),
        "-Coverflow-checks=on".into(),
        "-Cpanic=abort".into(),
        "-Zmir-opt-level=0".into(),
        "--sysroot".into(),
        sysroot,
    ];
    rustc_driver::run_compiler(&args, &mut exporter);
    match exporter.result.expect("compiler must finish analysis") {
        Ok(export) => println!("{}", serde_json::to_string(&export).unwrap()),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
