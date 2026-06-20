/-
  FoundationClaims.lean — formalizing real Foundation claim gates
  ----------------------------------------------------------------------------
  The rest of this repo shows the verification pattern on SAT certificates,
  neural-network robustness, and AI-generated proofs. This module points that
  pattern back at Foundation itself.

  Foundation's operational discipline is: a review-ready or private-use result
  block must not silently become a public-release or production claim. Public
  release and production require their own explicit gates.

  This is not a parser for Foundation JSON. It is the small, kernel-checked core
  of the claim-boundary invariant those JSON result blocks are supposed to obey.
-/

/-- The lifecycle stage a Foundation result block may honestly claim. -/
inductive Stage where
  | blocked
  | reviewOnly
  | privateUseReady
  | publicReleaseReady
  | productionReady
  deriving DecidableEq, Repr

/-- The explicit gates Foundation tracks before stronger claims are allowed. -/
structure Gates where
  privateUse : Bool
  burnIn : Bool
  trustedBetaFeedback : Bool
  stakeholderReview : Bool
  signedReleaseReview : Bool
  publicRelease : Bool
  production : Bool
  deriving DecidableEq, Repr

/-- A compact result block: what stage is claimed, which gates are earned, and
    whether production/checkpoint behavior is authorized. -/
structure ResultBlock where
  stage : Stage
  gates : Gates
  productionAuthorized : Bool
  checkpointAuthorized : Bool
  deriving DecidableEq, Repr

/-- Public release has more prerequisites than private daily use. -/
def publicReleasePrereqs (g : Gates) : Prop :=
  g.privateUse = true ∧
  g.burnIn = true ∧
  g.trustedBetaFeedback = true ∧
  g.stakeholderReview = true ∧
  g.signedReleaseReview = true ∧
  g.publicRelease = true

/-- Production is stricter still: public release plus the production gate. -/
def productionPrereqs (g : Gates) : Prop :=
  publicReleasePrereqs g ∧ g.production = true

/-- A result block is internally safe when its stronger authorizations are backed
    by the corresponding explicit gates. -/
def SafeBlock (b : ResultBlock) : Prop :=
  (b.stage = Stage.publicReleaseReady → publicReleasePrereqs b.gates) ∧
  (b.stage = Stage.productionReady → productionPrereqs b.gates) ∧
  (b.productionAuthorized = true → productionPrereqs b.gates) ∧
  (b.checkpointAuthorized = true → productionPrereqs b.gates)

/-- The actual Shield posture after the private-use gate earned: private daily
    use is ready, but burn-in/human/public/production gates remain unearned. -/
def shieldPrivateUseBlock : ResultBlock := {
  stage := Stage.privateUseReady,
  gates := {
    privateUse := true,
    burnIn := false,
    trustedBetaFeedback := false,
    stakeholderReview := false,
    signedReleaseReview := false,
    publicRelease := false,
    production := false
  },
  productionAuthorized := false,
  checkpointAuthorized := false
}

/-- Foundation may honestly claim private daily use from this block. -/
theorem shield_private_use_gate_earned :
    shieldPrivateUseBlock.gates.privateUse = true := by
  rfl

/-- But the same block cannot honestly claim public release. -/
theorem shield_public_release_not_earned :
    ¬ publicReleasePrereqs shieldPrivateUseBlock.gates := by
  intro h
  exact Bool.noConfusion h.2.1

/-- Nor can it honestly claim production. -/
theorem shield_production_not_earned :
    ¬ productionPrereqs shieldPrivateUseBlock.gates := by
  intro h
  exact shield_public_release_not_earned h.1

/-- The private-use Shield block is internally safe: it earns the private-use
    fact while refusing public-release, production, and checkpoint authority. -/
theorem shield_private_use_block_safe :
    SafeBlock shieldPrivateUseBlock := by
  constructor
  · intro h; cases h
  constructor
  · intro h; cases h
  constructor
  · intro h; cases h
  · intro h; cases h

/-- A generic theorem: production authorization is impossible in any safe block
    unless the full production prerequisites are present. -/
theorem production_authorization_requires_gate (b : ResultBlock)
    (hsafe : SafeBlock b) :
    b.productionAuthorized = true → productionPrereqs b.gates := by
  exact hsafe.2.2.1

/-- Same for checkpoint authorization: a checkpoint is a production-like claim,
    so it requires the same gate bundle. -/
theorem checkpoint_authorization_requires_gate (b : ResultBlock)
    (hsafe : SafeBlock b) :
    b.checkpointAuthorized = true → productionPrereqs b.gates := by
  exact hsafe.2.2.2

/-- A concrete anti-overclaim theorem for the current Shield posture. -/
theorem shield_no_production_or_checkpoint :
    shieldPrivateUseBlock.productionAuthorized = false ∧
    shieldPrivateUseBlock.checkpointAuthorized = false := by
  exact ⟨rfl, rfl⟩

/-- Conservative gate composition: a combined evidence packet earns a gate only
    when both inputs earned it. This is the formal version of Foundation's
    "compose by intersection, not union" rule. -/
def meetGates (a b : Gates) : Gates := {
  privateUse := a.privateUse && b.privateUse,
  burnIn := a.burnIn && b.burnIn,
  trustedBetaFeedback := a.trustedBetaFeedback && b.trustedBetaFeedback,
  stakeholderReview := a.stakeholderReview && b.stakeholderReview,
  signedReleaseReview := a.signedReleaseReview && b.signedReleaseReview,
  publicRelease := a.publicRelease && b.publicRelease,
  production := a.production && b.production
}

/-- Conservative result-block composition: the aggregate is review-only unless
    independently promoted later, and production/checkpoint authority is kept
    only if both inputs already authorized it. -/
def composeBlocks (a b : ResultBlock) : ResultBlock := {
  stage := Stage.reviewOnly,
  gates := meetGates a.gates b.gates,
  productionAuthorized := a.productionAuthorized && b.productionAuthorized,
  checkpointAuthorized := a.checkpointAuthorized && b.checkpointAuthorized
}

theorem and_true_left {a b : Bool} : a && b = true → a = true := by
  cases a <;> cases b <;> intro h <;> simp at h ⊢

theorem and_true_right {a b : Bool} : a && b = true → b = true := by
  cases a <;> cases b <;> intro h <;> simp at h ⊢

theorem meet_public_release_left (a b : Gates) :
    publicReleasePrereqs (meetGates a b) → publicReleasePrereqs a := by
  intro h
  have h_private : a.privateUse && b.privateUse = true := by simpa [meetGates] using h.1
  have h_burn : a.burnIn && b.burnIn = true := by simpa [meetGates] using h.2.1
  have h_beta : a.trustedBetaFeedback && b.trustedBetaFeedback = true := by simpa [meetGates] using h.2.2.1
  have h_stake : a.stakeholderReview && b.stakeholderReview = true := by simpa [meetGates] using h.2.2.2.1
  have h_signed : a.signedReleaseReview && b.signedReleaseReview = true := by simpa [meetGates] using h.2.2.2.2.1
  have h_public : a.publicRelease && b.publicRelease = true := by simpa [meetGates] using h.2.2.2.2.2
  exact ⟨
    and_true_left h_private,
    and_true_left h_burn,
    and_true_left h_beta,
    and_true_left h_stake,
    and_true_left h_signed,
    and_true_left h_public
  ⟩

theorem meet_public_release_right (a b : Gates) :
    publicReleasePrereqs (meetGates a b) → publicReleasePrereqs b := by
  intro h
  have h_private : a.privateUse && b.privateUse = true := by simpa [meetGates] using h.1
  have h_burn : a.burnIn && b.burnIn = true := by simpa [meetGates] using h.2.1
  have h_beta : a.trustedBetaFeedback && b.trustedBetaFeedback = true := by simpa [meetGates] using h.2.2.1
  have h_stake : a.stakeholderReview && b.stakeholderReview = true := by simpa [meetGates] using h.2.2.2.1
  have h_signed : a.signedReleaseReview && b.signedReleaseReview = true := by simpa [meetGates] using h.2.2.2.2.1
  have h_public : a.publicRelease && b.publicRelease = true := by simpa [meetGates] using h.2.2.2.2.2
  exact ⟨
    and_true_right h_private,
    and_true_right h_burn,
    and_true_right h_beta,
    and_true_right h_stake,
    and_true_right h_signed,
    and_true_right h_public
  ⟩

theorem meet_production_left (a b : Gates) :
    productionPrereqs (meetGates a b) → productionPrereqs a := by
  intro h
  have h_prod : a.production && b.production = true := by simpa [meetGates] using h.2
  exact ⟨meet_public_release_left a b h.1, and_true_left h_prod⟩

theorem meet_production_right (a b : Gates) :
    productionPrereqs (meetGates a b) → productionPrereqs b := by
  intro h
  have h_prod : a.production && b.production = true := by simpa [meetGates] using h.2
  exact ⟨meet_public_release_right a b h.1, and_true_right h_prod⟩

/-- Composition cannot create public-release prerequisites from nowhere: if the
    combined block has them, each input already had them. -/
theorem composed_public_release_requires_both_inputs (a b : ResultBlock) :
    publicReleasePrereqs (composeBlocks a b).gates →
      publicReleasePrereqs a.gates ∧ publicReleasePrereqs b.gates := by
  intro h
  exact ⟨meet_public_release_left a.gates b.gates h, meet_public_release_right a.gates b.gates h⟩

/-- Composition cannot create production prerequisites from nowhere. -/
theorem composed_production_requires_both_inputs (a b : ResultBlock) :
    productionPrereqs (composeBlocks a b).gates →
      productionPrereqs a.gates ∧ productionPrereqs b.gates := by
  intro h
  exact ⟨meet_production_left a.gates b.gates h, meet_production_right a.gates b.gates h⟩

/-- If neither input authorizes production, the composed block cannot authorize
    production. This is the concrete anti-overclaim rule for dashboard and
    evidence-OS aggregation. -/
theorem compose_preserves_no_production_authority (a b : ResultBlock)
    (ha : a.productionAuthorized = false) (hb : b.productionAuthorized = false) :
    (composeBlocks a b).productionAuthorized = false := by
  simp [composeBlocks, ha, hb]

/-- Same for checkpoint authority. -/
theorem compose_preserves_no_checkpoint_authority (a b : ResultBlock)
    (ha : a.checkpointAuthorized = false) (hb : b.checkpointAuthorized = false) :
    (composeBlocks a b).checkpointAuthorized = false := by
  simp [composeBlocks, ha, hb]

/-- Combining the current Shield private-use block with itself still cannot
    promote it to production or checkpoint authority. -/
theorem shield_self_composition_no_production_or_checkpoint :
    (composeBlocks shieldPrivateUseBlock shieldPrivateUseBlock).productionAuthorized = false ∧
    (composeBlocks shieldPrivateUseBlock shieldPrivateUseBlock).checkpointAuthorized = false := by
  exact ⟨rfl, rfl⟩

/-- Foundation dashboard evidence states. `earned` is the only status that can
    support a promoted claim; `blocked` and `refused` are still evidence, but
    they must stay visible as non-promotions. -/
inductive EvidenceStatus where
  | earned
  | review
  | blocked
  | refused
  deriving DecidableEq, Repr

/-- A status is promotable only when it is explicitly earned. -/
def Promotable : EvidenceStatus → Prop
  | EvidenceStatus.earned => True
  | _ => False

/-- Conservative status composition for dashboards and evidence packets. Refusal
    dominates, then blocked, then review; earned survives only when both inputs
    are earned. This is the formal version of "failed gates remain visible." -/
def combineStatus : EvidenceStatus → EvidenceStatus → EvidenceStatus
  | EvidenceStatus.refused, _ => EvidenceStatus.refused
  | _, EvidenceStatus.refused => EvidenceStatus.refused
  | EvidenceStatus.blocked, _ => EvidenceStatus.blocked
  | _, EvidenceStatus.blocked => EvidenceStatus.blocked
  | EvidenceStatus.review, _ => EvidenceStatus.review
  | _, EvidenceStatus.review => EvidenceStatus.review
  | EvidenceStatus.earned, EvidenceStatus.earned => EvidenceStatus.earned

theorem combine_refused_left (s : EvidenceStatus) :
    combineStatus EvidenceStatus.refused s = EvidenceStatus.refused := by
  cases s <;> rfl

theorem combine_refused_right (s : EvidenceStatus) :
    combineStatus s EvidenceStatus.refused = EvidenceStatus.refused := by
  cases s <;> rfl

theorem combine_blocked_left_not_refused (s : EvidenceStatus)
    (h : s ≠ EvidenceStatus.refused) :
    combineStatus EvidenceStatus.blocked s = EvidenceStatus.blocked := by
  cases s <;> simp [combineStatus] at h ⊢

theorem combine_blocked_right_not_refused (s : EvidenceStatus)
    (h : s ≠ EvidenceStatus.refused) :
    combineStatus s EvidenceStatus.blocked = EvidenceStatus.blocked := by
  cases s <;> simp [combineStatus] at h ⊢

/-- If a combined status is promotable, both inputs were promotable. -/
theorem combined_promotable_requires_both (a b : EvidenceStatus) :
    Promotable (combineStatus a b) → Promotable a ∧ Promotable b := by
  cases a <;> cases b <;> simp [Promotable, combineStatus]

/-- A blocked input cannot disappear into an earned aggregate. -/
theorem blocked_left_not_promotable (s : EvidenceStatus) :
    ¬ Promotable (combineStatus EvidenceStatus.blocked s) := by
  cases s <;> simp [Promotable, combineStatus]

/-- A refused input cannot disappear into an earned aggregate. -/
theorem refused_left_not_promotable (s : EvidenceStatus) :
    ¬ Promotable (combineStatus EvidenceStatus.refused s) := by
  cases s <;> simp [Promotable, combineStatus]

/-- A concrete OMD-style blocked scientific packet is evidence, but it is not a
    promotable claim. -/
def omdHeldoutBlockedStatus : EvidenceStatus := EvidenceStatus.blocked

theorem omd_blocked_not_promotable :
    ¬ Promotable omdHeldoutBlockedStatus := by
  simp [omdHeldoutBlockedStatus, Promotable]

#check @shield_private_use_gate_earned
#check @shield_public_release_not_earned
#check @shield_private_use_block_safe
#check @production_authorization_requires_gate
#check @checkpoint_authorization_requires_gate
#check @shield_no_production_or_checkpoint
#check @composed_public_release_requires_both_inputs
#check @composed_production_requires_both_inputs
#check @compose_preserves_no_production_authority
#check @compose_preserves_no_checkpoint_authority
#check @shield_self_composition_no_production_or_checkpoint
#check @combined_promotable_requires_both
#check @blocked_left_not_promotable
#check @refused_left_not_promotable
#check @omd_blocked_not_promotable
#print axioms shield_private_use_block_safe
#print axioms production_authorization_requires_gate
#print axioms checkpoint_authorization_requires_gate
#print axioms composed_public_release_requires_both_inputs
#print axioms composed_production_requires_both_inputs
#print axioms compose_preserves_no_production_authority
#print axioms combined_promotable_requires_both
#print axioms blocked_left_not_promotable
#print axioms refused_left_not_promotable
