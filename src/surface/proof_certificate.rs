//! Proof certificates: the checked tactic steps a proof records, their structural paths and errors, and the validation that a certificate's steps and tactics are well formed.

use super::*;

/// A structured proof containing only surface-expressible simple tactics.
///
/// Unlike [`ProofTactic`], this type cannot contain smart tactics or
/// internal-only implementation operations. Smart tactics should ultimately
/// return this type directly; printing it is then a structural conversion
/// back to ordinary `.click` syntax.
///
/// The step list is shared, not copied. A certificate is cloned once per
/// certified path and once per claim on that path, and a structured step owns
/// its child certificates, so a deep copy would make cloning and comparing a
/// finished proof quadratic in the joined path structure. Sharing also gives
/// equality a pointer fast path: the identical certificate every claim of one
/// function carries is recognized in constant time instead of being walked.
#[derive(Clone, Debug, Eq)]
pub struct ProofCertificate {
    pub(super) steps: std::sync::Arc<Vec<ProofStep>>,
    // Presentation only: the checked C split proved this arm unreachable.
    pub(super) pruned_execution_arm: bool,
}

impl PartialEq for ProofCertificate {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.steps, &other.steps) || self.steps == other.steps
    }
}

/// One explicit, surface-expressible step in a [`ProofCertificate`].
///
/// Unlike [`ProofTactic`], this representation has no smart-tactic variants.
/// Structured steps own recursively explicit child certificates, so a
/// certificate's checkable shape is enforced by the Rust type rather than
/// recovered later from [`ProofTactic::class`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStep {
    Match {
        scrutinee: ContractExpression,
        ensuring: Option<Vec<ProofAssertion>>,
        arms: Vec<CertificateInductionArm>,
    },
    CloseInvariantsBy(Box<ProofCertificate>),
    Both {
        left_proof: Box<ProofCertificate>,
        right_proof: Box<ProofCertificate>,
    },
    Mark(String),
    /// A checked step and the explicit proofs of its open obligations.
    StepProved {
        step: Box<ProofStep>,
        proof: StepProofCertificate,
    },
    Step,
    StepContract(ContractApplication),
    /// Name the scalar value assigned by this checked statement.
    StepBind(String),
    StepCall(CallBinderTransport),
    /// One application of a user-defined tactic's verified contract.
    UserTactic(CallBinderTransport),
    UnfoldPredicate(String),
    UnfoldFunction(ClickFunctionApplication),
    /// `peel(f(args)) using { ... }`: the same defining equation, plus
    /// the range-fold law the listed guards select, stated over `f(args)`.
    PeelFunction {
        application: ClickFunctionApplication,
        premises: Vec<ClickProposition>,
    },
    UnfoldResource(ResourceClause),
    /// `let { witness: name, ... } = unfold(resource)` on a declared
    /// resource: the unfold, with each named `let ... where` witness of the
    /// opened body bound to a proof name.
    UnfoldWitnesses {
        resource: ResourceClause,
        names: Vec<(String, String)>,
    },
    FoldResource(ResourceClause),
    Induct {
        parameter: String,
        hypothesis: String,
    },
    StructuralInduct {
        parameter: String,
        hypothesis: String,
        arms: Vec<CertificateInductionArm>,
    },
    ApplyInduction {
        hypothesis: String,
        arguments: Vec<ContractExpression>,
        premises: Vec<ClickProposition>,
    },
    ApplyTheoremUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    ObserveResource(ResourceClause),
    /// `take`, `give`, `gather`, or `scatter` on iterated guarded ownership.
    Iterated(IteratedTactic),
    ConstructResource(ResourceClause),
    Witness(ProofWitness),
    LetSatisfy(ProofLetSatisfy),
    Choose(ProofChoice),
    Assumption,
    Extract(ClickProposition),
    Normalize,
    NormalizeUsing(Vec<ClickProposition>),
    ArithmeticUsing(Vec<ClickProposition>),
    ArithmeticCertificate(ArithmeticCertificate),
    Intro,
    IntroAs(String),
    Enumerate,
    Contradiction(ClickProposition),
    Rewrite(ClickProposition),
    TransportUsing {
        source: ClickProposition,
        target: ClickProposition,
        premises: Vec<ClickProposition>,
    },
    /// `instantiate(F, value)`, with `premises` the written `using` list.
    /// Without a list, each instantiated guard must itself be an exact fact.
    InstantiateUsing {
        quantified: ClickProposition,
        argument: ContractExpression,
        premises: Option<Vec<ClickProposition>>,
    },
    Have {
        proposition: ClickProposition,
        proof: Box<ProofCertificate>,
    },
    Open {
        resource: ResourceClause,
        proof: Box<ProofCertificate>,
        /// The closing fold's proof of its one open body fact.
        close_proof: Option<Box<ProofCertificate>>,
    },
    If {
        condition: ClickProposition,
        ensuring: Option<Vec<ProofAssertion>>,
        then_proof: Box<ProofCertificate>,
        else_proof: Box<ProofCertificate>,
    },
    Cases {
        disjunction: ClickProposition,
        left_proof: Box<ProofCertificate>,
        right_proof: Box<ProofCertificate>,
    },
    Branch {
        ensuring: Option<Vec<ProofAssertion>>,
        then_proof: Box<ProofCertificate>,
        else_proof: Box<ProofCertificate>,
    },
    CallOutcomes {
        returned_proof: Box<ProofCertificate>,
        threw_proof: Box<ProofCertificate>,
    },
    Loop(CertificateStructuralClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateStructuralClause {
    pub(super) region: CodeRegion,
    pub(super) label: Option<String>,
    pub(super) decreases: Option<TerminationMeasure>,
    pub(super) diverges: bool,
    pub(super) items: Vec<CertificateStructuralItem>,
    pub(super) resources: Vec<ResourceClause>,
    pub(super) initialize_proof: Option<Box<ProofCertificate>>,
    pub(super) preserve_proof: Option<Box<ProofCertificate>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CertificateStructuralItem {
    pub(super) claim: ClickProposition,
    pub(super) name: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificatePathSegment {
    MatchArm(usize),
    InvariantBody,
    LeftConjunct,
    RightConjunct,
    Tactic(usize),
    HaveBody,
    OpenBody,
    ThenBranch,
    ElseBranch,
    ReturnedBranch,
    ThrewBranch,
    LeftCase,
    RightCase,
    InductionArm(usize),
    LoopInitialize,
    LoopPreserve,
    LoopItem(usize),
    StepBody,
    StepRequirement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateError {
    pub(super) tactic_class: TacticClass,
    pub(super) path: Vec<CertificatePathSegment>,
}

impl ProofCertificate {
    pub fn from_proof_tactics(tactics: &[ProofTactic]) -> Result<Self, CertificateError> {
        validate_certificate_tactics(tactics, &mut Vec::new())?;
        Ok(Self {
            pruned_execution_arm: false,
            steps: std::sync::Arc::new(
                tactics
                    .iter()
                    .map(ProofStep::from_validated_tactic)
                    .collect(),
            ),
        })
    }

    /// Only checked, decided execution splits may create this presentation leaf.
    pub(crate) fn pruned_execution_arm() -> Self {
        Self {
            steps: std::sync::Arc::new(Vec::new()),
            pruned_execution_arm: true,
        }
    }

    pub(crate) fn is_pruned_execution_arm(&self) -> bool {
        self.pruned_execution_arm
    }

    pub fn steps(&self) -> &[ProofStep] {
        &self.steps
    }

    /// The steps by value, reusing the shared allocation when this is the last
    /// handle to it.
    pub(crate) fn into_steps(self) -> Vec<ProofStep> {
        std::sync::Arc::try_unwrap(self.steps).unwrap_or_else(|shared| (*shared).clone())
    }

    /// Copy-on-write access for the surface stitcher, which grows a
    /// certificate's leaves in place while it is still uniquely owned.
    pub(crate) fn steps_mut(&mut self) -> &mut Vec<ProofStep> {
        std::sync::Arc::make_mut(&mut self.steps)
    }

    /// Whether the two certificates are the same retained object rather than
    /// two equal copies of it. Every claim certified on one function proof
    /// carries the same certificate, so this is what keeps comparing and
    /// cloning them independent of the certificate's size.
    #[cfg(test)]
    pub(crate) fn shares_steps_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.steps, &other.steps)
    }

    /// Serializes checked proof provenance as a certificate.
    ///
    /// This is the same admission rule [`Self::from_proof_tactics`] applies to
    /// source tactics: a certificate leaf must be surface-expressible and
    /// simple, and a structured step must own complete explicit child proofs.
    /// The two constructors share [`certificate_step_class`] and
    /// [`CertificateError`] so provenance cannot smuggle in a leaf that source
    /// text could not spell.
    pub(crate) fn from_steps(steps: Vec<ProofStep>) -> Result<Self, ClickError> {
        validate_certificate_steps(&steps, &mut Vec::new()).map_err(|error| {
            ClickError::new(format!(
                "proof provenance produced {error} as a certificate step, which no explicit \
                 proof can spell"
            ))
        })?;
        let certificate = Self {
            pruned_execution_arm: false,
            steps: std::sync::Arc::new(steps),
        };
        if certificate.contains_arithmetic_using() {
            return Err(ClickError::new(
                "generated proof certificate retained source-only `ArithmeticUsing`; expand the smart request before serialization",
            ));
        }
        Ok(certificate)
    }

    /// Steps that were already admitted by a certificate constructor. Nested
    /// certificates are validated where they are built, so re-walking them at
    /// every enclosing construction would be quadratic in the certificate.
    pub(super) fn from_validated_steps(steps: Vec<ProofStep>) -> Self {
        Self {
            pruned_execution_arm: false,
            steps: std::sync::Arc::new(steps),
        }
    }

    pub fn to_proof_tactics(&self) -> Vec<ProofTactic> {
        self.steps.iter().map(ProofStep::to_proof_tactic).collect()
    }

    /// Returns whether this certificate contains the source-only arithmetic
    /// request.  The walk is iterative because certificates can contain
    /// deeply nested branch, loop, and `have` proofs.
    pub(super) fn contains_arithmetic_using(&self) -> bool {
        self.steps.iter().any(proof_step_contains_arithmetic_using)
    }

    /// Steps already admitted one at a time by the checks [`Self::from_steps`]
    /// applies to the whole list ([`validate_certificate_step`] and
    /// [`proof_step_contains_arithmetic_using`]).
    pub(crate) fn from_admitted_steps(steps: Vec<ProofStep>) -> Self {
        Self::from_validated_steps(steps)
    }
}

/// Whether this step, or any step nested in it, is a source-only
/// `ArithmeticUsing`. A certificate contains one exactly when one of its steps
/// does.
pub(crate) fn proof_step_contains_arithmetic_using(step: &ProofStep) -> bool {
    {
        let mut pending = vec![step];
        while let Some(step) = pending.pop() {
            match step {
                ProofStep::ArithmeticUsing(_) => return true,
                ProofStep::Match { arms, .. } | ProofStep::StructuralInduct { arms, .. } => {
                    for arm in arms {
                        pending.extend(arm.proof.steps.iter());
                    }
                }
                ProofStep::CloseInvariantsBy(proof)
                | ProofStep::Have { proof, .. }
                | ProofStep::Open {
                    proof,
                    close_proof: None,
                    ..
                } => pending.extend(proof.steps.iter()),
                ProofStep::Open {
                    proof,
                    close_proof: Some(close_proof),
                    ..
                } => {
                    pending.extend(proof.steps.iter());
                    pending.extend(close_proof.steps.iter());
                }
                ProofStep::StepProved { step, proof } => {
                    pending.push(step);
                    match proof {
                        StepProofCertificate::By(body) => pending.extend(body.steps.iter()),
                        StepProofCertificate::Requires(entries) => {
                            for entry in entries {
                                pending.extend(entry.proof.steps.iter());
                            }
                        }
                    }
                }
                ProofStep::Both {
                    left_proof,
                    right_proof,
                }
                | ProofStep::Cases {
                    left_proof,
                    right_proof,
                    ..
                }
                | ProofStep::If {
                    then_proof: left_proof,
                    else_proof: right_proof,
                    ..
                }
                | ProofStep::Branch {
                    then_proof: left_proof,
                    else_proof: right_proof,
                    ..
                }
                | ProofStep::CallOutcomes {
                    returned_proof: left_proof,
                    threw_proof: right_proof,
                } => {
                    pending.extend(left_proof.steps.iter());
                    pending.extend(right_proof.steps.iter());
                }
                ProofStep::Loop(clause) => {
                    if let Some(proof) = clause.initialize_proof.as_deref() {
                        pending.extend(proof.steps.iter());
                    }
                    if let Some(proof) = clause.preserve_proof.as_deref() {
                        pending.extend(proof.steps.iter());
                    }
                }
                _ => {}
            }
        }
        false
    }
}

impl ProofCertificate {
    pub(super) fn from_validated_proof(proof: &SourceProof) -> Self {
        let SourceProof::Script(tactics) = proof else {
            unreachable!("validated simple proof must be an explicit script")
        };
        Self {
            pruned_execution_arm: false,
            steps: std::sync::Arc::new(
                tactics
                    .iter()
                    .map(ProofStep::from_validated_tactic)
                    .collect(),
            ),
        }
    }

    pub(super) fn to_source_proof(&self) -> SourceProof {
        SourceProof::Script(self.to_proof_tactics())
    }
}

impl ProofStep {
    pub(super) fn from_validated_tactic(tactic: &ProofTactic) -> Self {
        match tactic {
            ProofTactic::CloseInvariantsBy(body) => {
                Self::CloseInvariantsBy(Box::new(ProofCertificate::from_validated_steps(
                    body.iter().map(Self::from_validated_tactic).collect(),
                )))
            }
            ProofTactic::Both(both) => Self::Both {
                left_proof: Box::new(ProofCertificate::from_validated_steps(
                    both.left_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
                right_proof: Box::new(ProofCertificate::from_validated_steps(
                    both.right_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
            },
            ProofTactic::StepProved { step, proof } => Self::StepProved {
                step: Box::new(Self::from_validated_tactic(step)),
                proof: match proof {
                    StepProof::By(body) => {
                        StepProofCertificate::By(Box::new(ProofCertificate::from_validated_steps(
                            body.iter().map(Self::from_validated_tactic).collect(),
                        )))
                    }
                    StepProof::Requires(entries) => StepProofCertificate::Requires(
                        entries
                            .iter()
                            .map(|entry| StepRequirementCertificate {
                                label: entry.label.clone(),
                                proposition: entry.have.proposition.clone(),
                                proof: ProofCertificate::from_validated_proof(
                                    &entry.have.checking_proof(),
                                ),
                            })
                            .collect(),
                    ),
                },
            },
            ProofTactic::Match(proof_match) => Self::Match {
                scrutinee: proof_match.scrutinee.clone(),
                ensuring: proof_match.ensuring.clone(),
                arms: proof_match
                    .arms
                    .iter()
                    .map(|arm| CertificateInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        proof: Box::new(ProofCertificate::from_validated_steps(
                            arm.tactics
                                .iter()
                                .map(Self::from_validated_tactic)
                                .collect(),
                        )),
                    })
                    .collect(),
            },
            ProofTactic::StructuralInduct {
                parameter,
                hypothesis,
                arms,
            } => Self::StructuralInduct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
                arms: arms
                    .iter()
                    .map(|arm| CertificateInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        proof: Box::new(ProofCertificate::from_validated_steps(
                            arm.tactics
                                .iter()
                                .map(Self::from_validated_tactic)
                                .collect(),
                        )),
                    })
                    .collect(),
            },
            ProofTactic::ApplyInduction { .. } => {
                unreachable!("bare induction application is smart")
            }
            ProofTactic::CloseInvariants => {
                unreachable!("bare invariant closure is smart")
            }
            ProofTactic::Have(proof_have) => Self::Have {
                proposition: proof_have.proposition.clone(),
                proof: Box::new(ProofCertificate::from_validated_proof(&proof_have.proof)),
            },
            ProofTactic::Open(proof_open) => Self::Open {
                resource: proof_open.resource.clone(),
                proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_open
                        .tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
                close_proof: proof_open.close_proof.as_ref().map(|body| {
                    Box::new(ProofCertificate::from_validated_steps(
                        body.iter().map(Self::from_validated_tactic).collect(),
                    ))
                }),
            },
            ProofTactic::If(proof_if) => Self::If {
                condition: proof_if.condition.clone(),
                ensuring: proof_if.ensuring.clone(),
                then_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_if
                        .then_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
                else_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_if
                        .else_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
            },
            ProofTactic::Cases(proof_cases) => {
                let (disjunction, left, right) = proof_cases.binary();
                Self::Cases {
                    disjunction,
                    left_proof: Box::new(ProofCertificate::from_validated_steps(
                        left.iter().map(Self::from_validated_tactic).collect(),
                    )),
                    right_proof: Box::new(ProofCertificate::from_validated_steps(
                        right.iter().map(Self::from_validated_tactic).collect(),
                    )),
                }
            }
            ProofTactic::Branch(proof_branch) => Self::Branch {
                ensuring: proof_branch.ensuring.clone(),
                then_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_branch
                        .then_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
                else_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_branch
                        .else_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
            },
            ProofTactic::CallOutcomes(proof_outcomes) => Self::CallOutcomes {
                returned_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_outcomes
                        .returned_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
                threw_proof: Box::new(ProofCertificate::from_validated_steps(
                    proof_outcomes
                        .threw_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                )),
            },
            ProofTactic::Loop(clause) => Self::Loop(CertificateStructuralClause {
                region: clause.region,
                label: clause.label.clone(),
                decreases: clause.decreases.clone(),
                diverges: clause.diverges,
                resources: clause.resources.clone(),
                items: clause
                    .items
                    .iter()
                    .map(|item| CertificateStructuralItem {
                        claim: item.claim.clone(),
                        name: item.name.clone(),
                    })
                    .collect(),
                initialize_proof: clause
                    .initialize_proof
                    .as_ref()
                    .map(|proof| Box::new(ProofCertificate::from_validated_proof(proof))),
                preserve_proof: clause
                    .preserve_proof
                    .as_ref()
                    .map(|proof| Box::new(ProofCertificate::from_validated_proof(proof))),
            }),
            _ => Self::from_leaf_tactic(tactic)
                .expect("certificate validation admitted a non-surface tactic"),
        }
    }

    /// The certificate step for a written tactic with no child proof and no
    /// search: the leaves every proof context shares. This is the one
    /// `ProofTactic` -> `ProofStep` mapping for leaves; a context chooses
    /// which of them it admits ([`crate::surface::proof::SourceContext`]),
    /// never how one converts. A structured or smart tactic is `None`.
    pub(crate) fn from_leaf_tactic(tactic: &ProofTactic) -> Option<Self> {
        Some(match tactic {
            ProofTactic::Mark(name) => Self::Mark(name.clone()),
            ProofTactic::Step => Self::Step,
            ProofTactic::StepBind(name) => Self::StepBind(name.clone()),
            ProofTactic::StepContract(name) => Self::StepContract(name.clone()),
            ProofTactic::StepCall(transport) => Self::StepCall(transport.clone()),
            ProofTactic::UserTactic(application) => Self::UserTactic(application.clone()),
            ProofTactic::UnfoldPredicate(name) => Self::UnfoldPredicate(name.clone()),
            ProofTactic::UnfoldFunction(application) => Self::UnfoldFunction(application.clone()),
            ProofTactic::PeelFunction {
                application,
                premises,
            } => Self::PeelFunction {
                application: application.clone(),
                premises: premises.clone(),
            },
            ProofTactic::UnfoldResource(resource) => Self::UnfoldResource(resource.clone()),
            ProofTactic::UnfoldWitnesses { resource, names } => Self::UnfoldWitnesses {
                resource: resource.clone(),
                names: names.clone(),
            },
            ProofTactic::FoldResource(resource) => Self::FoldResource(resource.clone()),
            ProofTactic::ConstructResource(resource) => Self::ConstructResource(resource.clone()),
            ProofTactic::Induct {
                parameter,
                hypothesis,
            } => Self::Induct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
            },
            ProofTactic::ApplyInductionUsing {
                hypothesis,
                arguments,
                premises,
            } => Self::ApplyInduction {
                hypothesis: hypothesis.clone(),
                arguments: arguments.clone(),
                premises: premises.clone(),
            },
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => Self::ApplyTheoremUsing {
                application: application.clone(),
                premises: premises.clone(),
            },
            ProofTactic::ObserveResource(resource) => Self::ObserveResource(resource.clone()),
            ProofTactic::Iterated(tactic) => Self::Iterated(tactic.clone()),
            ProofTactic::Witness(witness) => Self::Witness(witness.clone()),
            ProofTactic::LetSatisfy(binding) => Self::LetSatisfy(binding.clone()),
            ProofTactic::Choose(choice) => Self::Choose(choice.clone()),
            ProofTactic::Assumption => Self::Assumption,
            ProofTactic::Extract(proposition) => Self::Extract(proposition.clone()),
            ProofTactic::Normalize => Self::Normalize,
            ProofTactic::NormalizeUsing(premises) => Self::NormalizeUsing(premises.clone()),
            ProofTactic::ArithmeticUsing(premises) => Self::ArithmeticUsing(premises.clone()),
            ProofTactic::ArithmeticCertificate(certificate) => {
                Self::ArithmeticCertificate(certificate.clone())
            }
            ProofTactic::Intro => Self::Intro,
            ProofTactic::IntroAs(name) => Self::IntroAs(name.clone()),
            ProofTactic::Enumerate => Self::Enumerate,
            ProofTactic::Contradiction(proposition) => Self::Contradiction(proposition.clone()),
            ProofTactic::Rewrite(proposition) => Self::Rewrite(proposition.clone()),
            ProofTactic::TransportUsing {
                source,
                target,
                premises,
            } => Self::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises: premises.clone(),
            },
            ProofTactic::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => Self::InstantiateUsing {
                quantified: quantified.clone(),
                argument: argument.clone(),
                premises: premises.clone(),
            },
            _ => return None,
        })
    }

    pub(super) fn to_proof_tactic(&self) -> ProofTactic {
        match self {
            Self::CloseInvariantsBy(body) => {
                ProofTactic::CloseInvariantsBy(body.to_proof_tactics())
            }
            Self::Both {
                left_proof,
                right_proof,
            } => ProofTactic::Both(ProofBoth {
                left_tactics: left_proof.to_proof_tactics(),
                right_tactics: right_proof.to_proof_tactics(),
            }),
            Self::Mark(name) => ProofTactic::Mark(name.clone()),
            Self::StepProved { step, proof } => ProofTactic::StepProved {
                step: Box::new(step.to_proof_tactic()),
                proof: match proof {
                    StepProofCertificate::By(body) => StepProof::By(body.to_proof_tactics()),
                    StepProofCertificate::Requires(entries) => StepProof::Requires(
                        entries
                            .iter()
                            .map(|entry| StepRequirement {
                                label: entry.label.clone(),
                                have: ProofHave {
                                    proposition: entry.proposition.clone(),
                                    proof: entry.proof.to_source_proof(),
                                },
                            })
                            .collect(),
                    ),
                },
            },
            Self::Step => ProofTactic::Step,
            Self::StepBind(name) => ProofTactic::StepBind(name.clone()),
            Self::StepContract(name) => ProofTactic::StepContract(name.clone()),
            Self::StepCall(transport) => ProofTactic::StepCall(transport.clone()),
            Self::UserTactic(application) => ProofTactic::UserTactic(application.clone()),
            Self::UnfoldPredicate(name) => ProofTactic::UnfoldPredicate(name.clone()),
            Self::UnfoldFunction(application) => ProofTactic::UnfoldFunction(application.clone()),
            Self::PeelFunction {
                application,
                premises,
            } => ProofTactic::PeelFunction {
                application: application.clone(),
                premises: premises.clone(),
            },
            Self::UnfoldResource(resource) => ProofTactic::UnfoldResource(resource.clone()),
            Self::UnfoldWitnesses { resource, names } => ProofTactic::UnfoldWitnesses {
                resource: resource.clone(),
                names: names.clone(),
            },
            Self::FoldResource(resource) => ProofTactic::FoldResource(resource.clone()),
            Self::ConstructResource(resource) => ProofTactic::ConstructResource(resource.clone()),
            Self::Induct {
                parameter,
                hypothesis,
            } => ProofTactic::Induct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
            },
            Self::Match {
                scrutinee,
                ensuring,
                arms,
            } => ProofTactic::Match(std::sync::Arc::new(ProofMatch {
                scrutinee: scrutinee.clone(),
                ensuring: ensuring.clone(),
                arms: arms
                    .iter()
                    .map(|arm| ProofInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        tactics: arm.proof.to_proof_tactics(),
                    })
                    .collect(),
            })),
            Self::StructuralInduct {
                parameter,
                hypothesis,
                arms,
            } => ProofTactic::StructuralInduct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
                arms: arms
                    .iter()
                    .map(|arm| ProofInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        tactics: arm.proof.to_proof_tactics(),
                    })
                    .collect(),
            },
            Self::ApplyInduction {
                hypothesis,
                arguments,
                premises,
            } => ProofTactic::ApplyInductionUsing {
                hypothesis: hypothesis.clone(),
                arguments: arguments.clone(),
                premises: premises.clone(),
            },
            Self::ApplyTheoremUsing {
                application,
                premises,
            } => ProofTactic::ApplyTheoremUsing {
                application: application.clone(),
                premises: premises.clone(),
            },
            Self::ObserveResource(resource) => ProofTactic::ObserveResource(resource.clone()),
            Self::Iterated(tactic) => ProofTactic::Iterated(tactic.clone()),
            Self::Witness(witness) => ProofTactic::Witness(witness.clone()),
            Self::LetSatisfy(binding) => ProofTactic::LetSatisfy(binding.clone()),
            Self::Choose(choice) => ProofTactic::Choose(choice.clone()),
            Self::Assumption => ProofTactic::Assumption,
            Self::Extract(proposition) => ProofTactic::Extract(proposition.clone()),
            Self::Normalize => ProofTactic::Normalize,
            Self::NormalizeUsing(premises) => ProofTactic::NormalizeUsing(premises.clone()),
            Self::ArithmeticUsing(premises) => ProofTactic::ArithmeticUsing(premises.clone()),
            Self::ArithmeticCertificate(certificate) => {
                ProofTactic::ArithmeticCertificate(certificate.clone())
            }
            Self::Intro => ProofTactic::Intro,
            Self::IntroAs(name) => ProofTactic::IntroAs(name.clone()),
            Self::Enumerate => ProofTactic::Enumerate,
            Self::Contradiction(proposition) => ProofTactic::Contradiction(proposition.clone()),
            Self::Rewrite(proposition) => ProofTactic::Rewrite(proposition.clone()),
            Self::TransportUsing {
                source,
                target,
                premises,
            } => ProofTactic::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises: premises.clone(),
            },
            Self::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => ProofTactic::InstantiateUsing {
                quantified: quantified.clone(),
                argument: argument.clone(),
                premises: premises.clone(),
            },
            Self::Have { proposition, proof } => ProofTactic::Have(ProofHave {
                proposition: proposition.clone(),
                proof: proof.to_source_proof(),
            }),
            Self::Open {
                resource,
                proof,
                close_proof,
            } => ProofTactic::Open(ProofOpen {
                resource: resource.clone(),
                tactics: proof.to_proof_tactics(),
                close_proof: close_proof.as_ref().map(|body| body.to_proof_tactics()),
            }),
            Self::If {
                condition,
                ensuring,
                then_proof,
                else_proof,
            } => ProofTactic::If(ProofIf {
                condition: condition.clone(),
                ensuring: ensuring.clone(),
                then_tactics: then_proof.to_proof_tactics(),
                else_tactics: else_proof.to_proof_tactics(),
            }),
            Self::Cases {
                disjunction,
                left_proof,
                right_proof,
            } => ProofTactic::Cases(ProofCases::from_binary(
                disjunction,
                left_proof.to_proof_tactics(),
                right_proof.to_proof_tactics(),
            )),
            Self::Branch {
                ensuring,
                then_proof,
                else_proof,
            } => ProofTactic::Branch(ProofBranch {
                ensuring: ensuring.clone(),
                then_tactics: then_proof.to_proof_tactics(),
                else_tactics: else_proof.to_proof_tactics(),
            }),
            Self::CallOutcomes {
                returned_proof,
                threw_proof,
            } => ProofTactic::CallOutcomes(ProofCallOutcomes {
                returned_tactics: returned_proof.to_proof_tactics(),
                threw_tactics: threw_proof.to_proof_tactics(),
            }),
            Self::Loop(clause) => ProofTactic::Loop(StructuralClause {
                region: clause.region,
                label: clause.label.clone(),
                decreases: clause.decreases.clone(),
                diverges: clause.diverges,
                resources: clause.resources.clone(),
                items: clause
                    .items
                    .iter()
                    .map(|item| StructuralItem {
                        claim: item.claim.clone(),
                        name: item.name.clone(),
                    })
                    .collect(),
                initialize_proof: clause
                    .initialize_proof
                    .as_ref()
                    .map(|proof| proof.to_source_proof()),
                preserve_proof: clause
                    .preserve_proof
                    .as_ref()
                    .map(|proof| proof.to_source_proof()),
                scope: BTreeMap::new(),
            }),
        }
    }
}

impl std::fmt::Display for CertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message())
    }
}

impl CertificateError {
    pub fn tactic_class(&self) -> TacticClass {
        self.tactic_class
    }

    pub fn path(&self) -> &[CertificatePathSegment] {
        &self.path
    }

    /// Names the refused tactic and where it sits, in the spelling the author
    /// wrote. A certificate holds simple steps only, so the refusal a user
    /// meets is almost always a smart tactic written where an explicit script
    /// is required; saying which one and where is the whole diagnostic.
    pub fn message(&self) -> String {
        let tactic = match self.tactic_class {
            TacticClass::Smart(kind) => format!("smart tactic `{}`", smart_tactic_spelling(kind)),
            TacticClass::Control(_) => "a control tactic".to_string(),
            TacticClass::Simple(_) => "a step with no certificate form".to_string(),
            TacticClass::Sorry => "a `sorry` admission".to_string(),
        };
        let mut place = String::new();
        for segment in &self.path {
            let segment = match segment {
                CertificatePathSegment::MatchArm(index) => format!("match arm {index}"),
                CertificatePathSegment::InvariantBody => "invariant body".to_string(),
                CertificatePathSegment::LeftConjunct => "left conjunct".to_string(),
                CertificatePathSegment::RightConjunct => "right conjunct".to_string(),
                CertificatePathSegment::Tactic(index) => format!("tactic {index}"),
                CertificatePathSegment::HaveBody => "`have` body".to_string(),
                CertificatePathSegment::OpenBody => "open scope".to_string(),
                CertificatePathSegment::ThenBranch => "then branch".to_string(),
                CertificatePathSegment::ElseBranch => "else branch".to_string(),
                CertificatePathSegment::ReturnedBranch => "returned branch".to_string(),
                CertificatePathSegment::ThrewBranch => "threw branch".to_string(),
                CertificatePathSegment::LeftCase => "left case".to_string(),
                CertificatePathSegment::RightCase => "right case".to_string(),
                CertificatePathSegment::InductionArm(index) => format!("induction arm {index}"),
                CertificatePathSegment::LoopInitialize => "loop `initialize`".to_string(),
                CertificatePathSegment::LoopPreserve => "loop `preserve`".to_string(),
                CertificatePathSegment::LoopItem(index) => format!("loop item {index}"),
                CertificatePathSegment::StepBody => "step `by` body".to_string(),
                CertificatePathSegment::StepRequirement(index) => {
                    format!("step `requires` entry {index}")
                }
            };
            if !place.is_empty() {
                place.push_str(" > ");
            }
            place.push_str(&segment);
        }
        if place.is_empty() {
            tactic
        } else {
            format!("{tactic} at {place}")
        }
    }
}

/// The source spelling of a smart tactic, for diagnostics.
pub(super) fn smart_tactic_spelling(kind: SmartTacticKind) -> &'static str {
    match kind {
        SmartTacticKind::CloseInvariants => "close_invariants",
        SmartTacticKind::Auto => "auto",
        SmartTacticKind::ApplyTheorem => "apply",
        SmartTacticKind::Arithmetic => "arithmetic",
        SmartTacticKind::FactTransport => "normalize",
        SmartTacticKind::SmartExecute => "execute",
        SmartTacticKind::ExecuteUntil => "execute_until",
        SmartTacticKind::Simp => "simp",
    }
}

/// Classifies one certificate step by the tactic it prints as.
///
/// The match is exhaustive on purpose: a new [`ProofStep`] must be classified
/// deliberately, and a step classified `Smart` is refused by
/// [`ProofCertificate::from_steps`] exactly as its spelling is refused by
/// [`ProofCertificate::from_proof_tactics`]. Classification reads no payload,
/// so validating a certificate costs one pass over its own steps.
pub(super) fn certificate_step_class(step: &ProofStep) -> TacticClass {
    match step {
        ProofStep::Mark(_) => TacticClass::Simple(SimpleTactic::Mark),
        ProofStep::Step
        | ProofStep::StepBind(_)
        | ProofStep::StepContract(_)
        | ProofStep::StepCall(_) => TacticClass::Simple(SimpleTactic::StatementTransition),
        ProofStep::UserTactic(_) => TacticClass::Simple(SimpleTactic::UserTactic),
        ProofStep::UnfoldPredicate(_) => TacticClass::Simple(SimpleTactic::UnfoldPredicate),
        ProofStep::UnfoldFunction(_) | ProofStep::PeelFunction { .. } => {
            TacticClass::Simple(SimpleTactic::UnfoldFunction)
        }
        ProofStep::UnfoldResource(_) | ProofStep::UnfoldWitnesses { .. } => {
            TacticClass::Simple(SimpleTactic::UnfoldResource)
        }
        ProofStep::ObserveResource(_) => TacticClass::Simple(SimpleTactic::ObserveResource),
        ProofStep::Iterated(_) => TacticClass::Simple(SimpleTactic::IteratedOwnership),
        ProofStep::FoldResource(_) => TacticClass::Simple(SimpleTactic::FoldResource),
        ProofStep::ConstructResource(_) => TacticClass::Simple(SimpleTactic::ConstructResource),
        ProofStep::Induct { .. } => TacticClass::Simple(SimpleTactic::Induct),
        ProofStep::ApplyInduction { .. } => TacticClass::Simple(SimpleTactic::ApplyInduction),
        ProofStep::ApplyTheoremUsing { .. } => TacticClass::Simple(SimpleTactic::ApplyTheorem),
        ProofStep::Witness(_) => TacticClass::Simple(SimpleTactic::Witness),
        ProofStep::LetSatisfy(_) => TacticClass::Simple(SimpleTactic::LetSatisfy),
        ProofStep::Choose(_) => TacticClass::Simple(SimpleTactic::Choose),
        ProofStep::Assumption => TacticClass::Simple(SimpleTactic::Assumption),
        ProofStep::Extract(_) => TacticClass::Simple(SimpleTactic::Extract),
        ProofStep::Normalize | ProofStep::NormalizeUsing(_) => {
            TacticClass::Simple(SimpleTactic::Normalize)
        }
        ProofStep::ArithmeticUsing(_) => TacticClass::Smart(SmartTacticKind::Arithmetic),
        ProofStep::ArithmeticCertificate(_) => TacticClass::Simple(SimpleTactic::Arithmetic),
        ProofStep::Intro | ProofStep::IntroAs(_) => TacticClass::Simple(SimpleTactic::Intro),
        ProofStep::Enumerate => TacticClass::Simple(SimpleTactic::Enumerate),
        ProofStep::Contradiction(_) => TacticClass::Simple(SimpleTactic::Contradiction),
        ProofStep::Rewrite(_) => TacticClass::Simple(SimpleTactic::Rewrite),
        ProofStep::TransportUsing { .. } => TacticClass::Simple(SimpleTactic::FactTransport),
        ProofStep::InstantiateUsing { .. } => TacticClass::Simple(SimpleTactic::Instantiate),
        ProofStep::CloseInvariantsBy(_) => TacticClass::Control(ControlTactic::CloseInvariants),
        ProofStep::StepProved { .. } => TacticClass::Control(ControlTactic::StepProofs),
        ProofStep::Both { .. } => TacticClass::Control(ControlTactic::Both),
        ProofStep::Have { .. } => TacticClass::Control(ControlTactic::Have),
        ProofStep::Open { .. } => TacticClass::Control(ControlTactic::Open),
        ProofStep::If { .. } => TacticClass::Control(ControlTactic::If),
        ProofStep::Cases { .. } => TacticClass::Control(ControlTactic::Cases),
        ProofStep::Match { .. } => TacticClass::Control(ControlTactic::Match),
        ProofStep::StructuralInduct { .. } => TacticClass::Control(ControlTactic::StructuralInduct),
        ProofStep::Branch { .. } => TacticClass::Control(ControlTactic::Branch),
        ProofStep::CallOutcomes { .. } => TacticClass::Control(ControlTactic::CallOutcomes),
        ProofStep::Loop(_) => TacticClass::Control(ControlTactic::Loop),
    }
}

/// The step-side twin of [`validate_certificate_tactics`].
///
/// Nested certificates were admitted by their own constructor, so this walks
/// only the steps it was handed: work stays linear in the certificate delta
/// being serialized rather than quadratic in nesting depth. A structural
/// `loop` step is the one shape whose children are not certificates, so its
/// two phase proofs are checked here.
pub(super) fn validate_certificate_steps(
    steps: &[ProofStep],
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    for (index, step) in steps.iter().enumerate() {
        validate_certificate_step(step, index, path)?;
    }
    Ok(())
}

/// [`validate_certificate_steps`] for the step at `index` of its list: a list
/// is admitted exactly when each of its steps is.
pub(crate) fn validate_certificate_step(
    step: &ProofStep,
    index: usize,
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    {
        path.push(CertificatePathSegment::Tactic(index));
        // ArithmeticUsing remains accepted by the source-tactic constructor
        // as a smart request, but generated certificate steps must already
        // carry the checked structural ArithmeticCertificate provenance.
        let result = match certificate_step_class(step) {
            tactic_class @ (TacticClass::Smart(_) | TacticClass::Sorry) => Err(CertificateError {
                tactic_class,
                path: path.clone(),
            }),
            TacticClass::Control(ControlTactic::Loop) => {
                let ProofStep::Loop(clause) = step else {
                    unreachable!("step class and variant must agree")
                };
                let mut result = Ok(());
                for (segment, phase) in [
                    (
                        CertificatePathSegment::LoopInitialize,
                        &clause.initialize_proof,
                    ),
                    (CertificatePathSegment::LoopPreserve, &clause.preserve_proof),
                ] {
                    if phase.is_none() {
                        path.push(segment);
                        result = Err(CertificateError {
                            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
                            path: path.clone(),
                        });
                        path.pop();
                        break;
                    }
                }
                result
            }
            TacticClass::Simple(_) | TacticClass::Control(_) => Ok(()),
        };
        path.pop();
        result?;
    }
    Ok(())
}

pub(super) fn validate_certificate_tactics(
    tactics: &[ProofTactic],
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    for (index, tactic) in tactics.iter().enumerate() {
        path.push(CertificatePathSegment::Tactic(index));
        // Preserve the parser/source compatibility of arithmetic using in
        // preplanned pure certificates; interactive proof-object execution
        // records the structural checked certificate instead.
        let result = if matches!(tactic, ProofTactic::ArithmeticUsing(_)) {
            Ok(())
        } else {
            match tactic.class() {
                TacticClass::Control(ControlTactic::CloseInvariants) => {
                    let ProofTactic::CloseInvariantsBy(body) = tactic else {
                        unreachable!()
                    };
                    path.push(CertificatePathSegment::InvariantBody);
                    let result = validate_certificate_tactics(body, path);
                    path.pop();
                    result
                }
                TacticClass::Simple(_) => Ok(()),
                TacticClass::Control(ControlTactic::StepProofs) => {
                    let ProofTactic::StepProved { proof, .. } = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    match proof {
                        StepProof::By(body) => {
                            path.push(CertificatePathSegment::StepBody);
                            let result = validate_certificate_tactics(body, path);
                            path.pop();
                            result
                        }
                        StepProof::Requires(entries) => {
                            let mut result = Ok(());
                            for (index, entry) in entries.iter().enumerate() {
                                path.push(CertificatePathSegment::StepRequirement(index));
                                result = validate_certificate_proof(&entry.have.proof, path);
                                path.pop();
                                if result.is_err() {
                                    break;
                                }
                            }
                            result
                        }
                    }
                }
                TacticClass::Control(ControlTactic::Both) => {
                    let ProofTactic::Both(both) = tactic else {
                        unreachable!()
                    };
                    path.push(CertificatePathSegment::LeftConjunct);
                    validate_certificate_tactics(&both.left_tactics, path)?;
                    path.pop();
                    path.push(CertificatePathSegment::RightConjunct);
                    let result = validate_certificate_tactics(&both.right_tactics, path);
                    path.pop();
                    result
                }
                tactic_class @ (TacticClass::Smart(_) | TacticClass::Sorry) => {
                    Err(CertificateError {
                        tactic_class,
                        path: path.clone(),
                    })
                }
                TacticClass::Control(ControlTactic::Have) => {
                    let ProofTactic::Have(proof_have) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    path.push(CertificatePathSegment::HaveBody);
                    let result = validate_certificate_proof(&proof_have.proof, path);
                    path.pop();
                    result
                }
                TacticClass::Control(ControlTactic::Open) => {
                    let ProofTactic::Open(proof_open) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    path.push(CertificatePathSegment::OpenBody);
                    validate_certificate_tactics(&proof_open.tactics, path)?;
                    path.pop();
                    match &proof_open.close_proof {
                        Some(close_proof) => {
                            path.push(CertificatePathSegment::StepBody);
                            let result = validate_certificate_tactics(close_proof, path);
                            path.pop();
                            result
                        }
                        None => Ok(()),
                    }
                }
                TacticClass::Control(ControlTactic::If) => {
                    let ProofTactic::If(proof_if) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    path.push(CertificatePathSegment::ThenBranch);
                    let then_result = validate_certificate_tactics(&proof_if.then_tactics, path);
                    path.pop();
                    if then_result.is_err() {
                        then_result
                    } else {
                        path.push(CertificatePathSegment::ElseBranch);
                        let else_result =
                            validate_certificate_tactics(&proof_if.else_tactics, path);
                        path.pop();
                        else_result
                    }
                }
                TacticClass::Control(ControlTactic::Cases) => {
                    let ProofTactic::Cases(proof_cases) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    let (_, left, right) = proof_cases.binary();
                    path.push(CertificatePathSegment::LeftCase);
                    let left_result = validate_certificate_tactics(&left, path);
                    path.pop();
                    if left_result.is_err() {
                        left_result
                    } else {
                        path.push(CertificatePathSegment::RightCase);
                        let right_result = validate_certificate_tactics(&right, path);
                        path.pop();
                        right_result
                    }
                }
                TacticClass::Control(ControlTactic::Match) => {
                    let ProofTactic::Match(proof_match) = tactic else {
                        unreachable!()
                    };
                    let mut result = Ok(());
                    for (index, arm) in proof_match.arms.iter().enumerate() {
                        path.push(CertificatePathSegment::MatchArm(index));
                        result = validate_certificate_tactics(&arm.tactics, path);
                        path.pop();
                        if result.is_err() {
                            break;
                        }
                    }
                    result
                }
                TacticClass::Control(ControlTactic::StructuralInduct) => {
                    let ProofTactic::StructuralInduct { arms, .. } = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    let mut result = Ok(());
                    for (arm_index, arm) in arms.iter().enumerate() {
                        path.push(CertificatePathSegment::InductionArm(arm_index));
                        result = validate_certificate_tactics(&arm.tactics, path);
                        path.pop();
                        if result.is_err() {
                            break;
                        }
                    }
                    result
                }
                TacticClass::Control(ControlTactic::Branch) => {
                    let ProofTactic::Branch(proof_branch) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    path.push(CertificatePathSegment::ThenBranch);
                    let then_result =
                        validate_certificate_tactics(&proof_branch.then_tactics, path);
                    path.pop();
                    if then_result.is_err() {
                        then_result
                    } else {
                        path.push(CertificatePathSegment::ElseBranch);
                        let else_result =
                            validate_certificate_tactics(&proof_branch.else_tactics, path);
                        path.pop();
                        else_result
                    }
                }
                TacticClass::Control(ControlTactic::CallOutcomes) => {
                    let ProofTactic::CallOutcomes(outcomes) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    path.push(CertificatePathSegment::ReturnedBranch);
                    let returned = validate_certificate_tactics(&outcomes.returned_tactics, path);
                    path.pop();
                    if returned.is_err() {
                        returned
                    } else {
                        path.push(CertificatePathSegment::ThrewBranch);
                        let threw = validate_certificate_tactics(&outcomes.threw_tactics, path);
                        path.pop();
                        threw
                    }
                }
                TacticClass::Control(ControlTactic::Loop) => {
                    let ProofTactic::Loop(loop_clause) = tactic else {
                        unreachable!("tactic class and variant must agree")
                    };
                    let mut result;
                    path.push(CertificatePathSegment::LoopInitialize);
                    result = match loop_clause.initialize_proof() {
                        Some(proof) => validate_certificate_proof(proof, path),
                        None => Err(CertificateError {
                            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
                            path: path.clone(),
                        }),
                    };
                    path.pop();
                    if result.is_ok() {
                        path.push(CertificatePathSegment::LoopPreserve);
                        result = match loop_clause.preserve_proof() {
                            Some(proof) => validate_certificate_proof(proof, path),
                            None => Err(CertificateError {
                                tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
                                path: path.clone(),
                            }),
                        };
                        path.pop();
                    }
                    result
                }
            }
        };
        path.pop();
        result?;
    }
    Ok(())
}

pub(super) fn validate_certificate_proof(
    proof: &SourceProof,
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    match proof {
        SourceProof::Default => Err(CertificateError {
            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
            path: path.clone(),
        }),
        SourceProof::Tactic(smart_tactic) => Err(CertificateError {
            tactic_class: TacticClass::Smart(smart_tactic.kind()),
            path: path.clone(),
        }),
        SourceProof::Script(tactics) => validate_certificate_tactics(tactics, path),
    }
}
