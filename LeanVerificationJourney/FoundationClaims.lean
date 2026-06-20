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

/-- A finite menu of Foundation claims that public reports and dashboards may
    either make or explicitly refuse. The point is not that this list is final;
    it is that the claim/refusal relation is checkable. -/
inductive Claim where
  | privateDailyUse
  | publicRelease
  | production
  | checkpoint
  | securityCertified
  | omdCommercial
  deriving DecidableEq, Repr

/-- A claim set is a decidable predicate over the current finite claim menu. -/
abbrev ClaimSet := Claim → Bool

def Allows (s : ClaimSet) (c : Claim) : Prop := s c = true

def Refuses (s : ClaimSet) (c : Claim) : Prop := s c = true

/-- The Foundation result-block language has two surfaces: what this artifact
    claims, and what it explicitly does not claim. A boundary is consistent
    when no claim appears on both surfaces. -/
structure ClaimBoundary where
  doesClaim : ClaimSet
  doesNotClaim : ClaimSet

def BoundaryConsistent (b : ClaimBoundary) : Prop :=
  ∀ c, ¬ (Allows b.doesClaim c ∧ Refuses b.doesNotClaim c)

/-- Shield's current public posture in claim-boundary form: private daily use
    is claimed; public release, production, checkpoint authority, security
    certification, and OMD commercial readiness are explicitly refused. -/
def shieldPrivateUseBoundary : ClaimBoundary :=
  { doesClaim := fun
      | Claim.privateDailyUse => true
      | _ => false
    doesNotClaim := fun
      | Claim.privateDailyUse => false
      | Claim.publicRelease => true
      | Claim.production => true
      | Claim.checkpoint => true
      | Claim.securityCertified => true
      | Claim.omdCommercial => true }

theorem shield_boundary_claims_private_daily_use :
    Allows shieldPrivateUseBoundary.doesClaim Claim.privateDailyUse := by
  rfl

theorem shield_boundary_refuses_production :
    Refuses shieldPrivateUseBoundary.doesNotClaim Claim.production := by
  rfl

theorem shield_boundary_refuses_checkpoint :
    Refuses shieldPrivateUseBoundary.doesNotClaim Claim.checkpoint := by
  rfl

theorem shield_boundary_refuses_security_certification :
    Refuses shieldPrivateUseBoundary.doesNotClaim Claim.securityCertified := by
  rfl

theorem shield_boundary_consistent :
    BoundaryConsistent shieldPrivateUseBoundary := by
  intro c h
  cases c <;> cases h with
  | intro hc hn => simp [Allows, Refuses, shieldPrivateUseBoundary] at hc hn

/-- Conservative claim composition: an aggregate claims only what both inputs
    claim, and it refuses anything either input refuses. -/
def intersectClaims (a b : ClaimSet) : ClaimSet := fun c => a c && b c

def unionRefusals (a b : ClaimSet) : ClaimSet := fun c => a c || b c

def composeBoundaries (a b : ClaimBoundary) : ClaimBoundary :=
  { doesClaim := intersectClaims a.doesClaim b.doesClaim
    doesNotClaim := unionRefusals a.doesNotClaim b.doesNotClaim }

theorem intersect_allows_left (a b : ClaimSet) (c : Claim) :
    Allows (intersectClaims a b) c → Allows a c := by
  intro h
  exact and_true_left (by simpa [Allows, intersectClaims] using h)

theorem intersect_allows_right (a b : ClaimSet) (c : Claim) :
    Allows (intersectClaims a b) c → Allows b c := by
  intro h
  exact and_true_right (by simpa [Allows, intersectClaims] using h)

theorem union_refuses_cases (a b : ClaimSet) (c : Claim) :
    Refuses (unionRefusals a b) c → Refuses a c ∨ Refuses b c := by
  intro h
  cases ha : a c <;> cases hb : b c <;> simp [Refuses, unionRefusals, ha, hb] at h ⊢

/-- Conservative composition preserves boundary consistency. If the aggregate
    claims something, both inputs claimed it; if the aggregate refuses it, at
    least one input refused it. Thus any inconsistency would already have
    existed in one of the inputs. -/
theorem compose_boundary_consistent (a b : ClaimBoundary)
    (ha : BoundaryConsistent a) (hb : BoundaryConsistent b) :
    BoundaryConsistent (composeBoundaries a b) := by
  intro c h
  have hClaimA : Allows a.doesClaim c :=
    intersect_allows_left a.doesClaim b.doesClaim c (by
      simpa [composeBoundaries] using h.1)
  have hClaimB : Allows b.doesClaim c :=
    intersect_allows_right a.doesClaim b.doesClaim c (by
      simpa [composeBoundaries] using h.1)
  have hRefuse := union_refuses_cases a.doesNotClaim b.doesNotClaim c (by
      simpa [composeBoundaries] using h.2)
  cases hRefuse with
  | inl hRefuseA => exact ha c ⟨hClaimA, hRefuseA⟩
  | inr hRefuseB => exact hb c ⟨hClaimB, hRefuseB⟩

/-- Even after conservative self-composition, the current Shield boundary stays
    internally consistent. -/
theorem shield_boundary_self_composition_consistent :
    BoundaryConsistent (composeBoundaries shieldPrivateUseBoundary shieldPrivateUseBoundary) := by
  exact compose_boundary_consistent shieldPrivateUseBoundary shieldPrivateUseBoundary
    shield_boundary_consistent shield_boundary_consistent

/-- A coarse source taxonomy for Foundation evidence. This does not certify the
    world; it records what kind of artifact a claim is backed by. -/
inductive SourceKind where
  | publicLeanRepo
  | localPrivateArtifact
  | generatedReport
  | externalDataset
  deriving DecidableEq, Repr

/-- The minimal provenance fields a Foundation claim needs before it can be
    treated as promotable: an artifact was recorded, the reproducing command was
    recorded, and the artifact is marked reproducible by the lane's checker. -/
structure EvidenceSource where
  kind : SourceKind
  artifactRecorded : Bool
  commandRecorded : Bool
  reproducible : Bool

def SourceValid (s : EvidenceSource) : Prop :=
  s.artifactRecorded = true ∧ s.commandRecorded = true ∧ s.reproducible = true

/-- A boundary plus the source metadata that backs it. -/
structure SourcedBoundary where
  boundary : ClaimBoundary
  source : EvidenceSource

/-- A claim is promotable only when the boundary is internally consistent, the
    claim is actually made, and the source metadata is valid. -/
def SourcedClaimPromotable (b : SourcedBoundary) (c : Claim) : Prop :=
  BoundaryConsistent b.boundary ∧ Allows b.boundary.doesClaim c ∧ SourceValid b.source

/-- The source for this public Lean module: the artifact, command, and
    reproducibility check are all explicit (`lake build`). -/
def leanFoundationClaimsSource : EvidenceSource :=
  { kind := SourceKind.publicLeanRepo
    artifactRecorded := true
    commandRecorded := true
    reproducible := true }

def shieldPrivateUseSourcedBoundary : SourcedBoundary :=
  { boundary := shieldPrivateUseBoundary
    source := leanFoundationClaimsSource }

theorem lean_foundation_claims_source_valid :
    SourceValid leanFoundationClaimsSource := by
  exact ⟨rfl, rfl, rfl⟩

theorem shield_sourced_private_daily_use_promotable :
    SourcedClaimPromotable shieldPrivateUseSourcedBoundary Claim.privateDailyUse := by
  exact ⟨shield_boundary_consistent, shield_boundary_claims_private_daily_use,
    lean_foundation_claims_source_valid⟩

/-- If the source is not valid, the claim cannot be promotable, even if the
    boundary says it is claimed. This is the "no anonymous promotion" rule. -/
theorem invalid_source_not_promotable (b : SourcedBoundary) (c : Claim)
    (h : ¬ SourceValid b.source) :
    ¬ SourcedClaimPromotable b c := by
  intro hp
  exact h hp.2.2

/-- Conservative source composition: an aggregate source is valid only when
    both source records carry each required bit. -/
def composeSources (a b : EvidenceSource) : EvidenceSource :=
  { kind := a.kind
    artifactRecorded := a.artifactRecorded && b.artifactRecorded
    commandRecorded := a.commandRecorded && b.commandRecorded
    reproducible := a.reproducible && b.reproducible }

def composeSourcedBoundaries (a b : SourcedBoundary) : SourcedBoundary :=
  { boundary := composeBoundaries a.boundary b.boundary
    source := composeSources a.source b.source }

theorem composed_source_valid_requires_left (a b : EvidenceSource) :
    SourceValid (composeSources a b) → SourceValid a := by
  intro h
  exact ⟨and_true_left (by simpa [SourceValid, composeSources] using h.1),
    and_true_left (by simpa [SourceValid, composeSources] using h.2.1),
    and_true_left (by simpa [SourceValid, composeSources] using h.2.2)⟩

theorem composed_source_valid_requires_right (a b : EvidenceSource) :
    SourceValid (composeSources a b) → SourceValid b := by
  intro h
  exact ⟨and_true_right (by simpa [SourceValid, composeSources] using h.1),
    and_true_right (by simpa [SourceValid, composeSources] using h.2.1),
    and_true_right (by simpa [SourceValid, composeSources] using h.2.2)⟩

/-- Source validity cannot be manufactured by aggregation. If a composed
    evidence packet is valid, both of its inputs were already source-valid. -/
theorem composed_source_valid_requires_both (a b : EvidenceSource) :
    SourceValid (composeSources a b) → SourceValid a ∧ SourceValid b := by
  intro h
  exact ⟨composed_source_valid_requires_left a b h,
    composed_source_valid_requires_right a b h⟩

/-- A composed sourced claim can promote only when both inputs had valid source
    metadata. This is the provenance analogue of conservative gate
    composition. -/
theorem composed_sourced_claim_requires_both_sources (a b : SourcedBoundary) (c : Claim) :
    SourcedClaimPromotable (composeSourcedBoundaries a b) c →
      SourceValid a.source ∧ SourceValid b.source := by
  intro h
  exact composed_source_valid_requires_both a.source b.source h.2.2

/-- The current sourced Shield boundary stays promotable for private daily use
    under conservative self-composition, and the proof still uses explicit
    source validity rather than anonymous dashboard state. -/
theorem shield_sourced_self_composition_private_daily_use_promotable :
    SourcedClaimPromotable
      (composeSourcedBoundaries shieldPrivateUseSourcedBoundary shieldPrivateUseSourcedBoundary)
      Claim.privateDailyUse := by
  exact ⟨shield_boundary_self_composition_consistent, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- A stricter source record for current operational claims: the ordinary
    source metadata is present, and the evidence is pinned to a version plus a
    current check. This models "not just sourced, but sourced to this run." -/
structure VersionedEvidenceSource where
  source : EvidenceSource
  versionRecorded : Bool
  currentCheckPassed : Bool

def FreshSourceValid (s : VersionedEvidenceSource) : Prop :=
  SourceValid s.source ∧ s.versionRecorded = true ∧ s.currentCheckPassed = true

structure VersionedSourcedBoundary where
  boundary : ClaimBoundary
  source : VersionedEvidenceSource

def FreshClaimPromotable (b : VersionedSourcedBoundary) (c : Claim) : Prop :=
  BoundaryConsistent b.boundary ∧ Allows b.boundary.doesClaim c ∧ FreshSourceValid b.source

def leanFoundationClaimsFreshSource : VersionedEvidenceSource :=
  { source := leanFoundationClaimsSource
    versionRecorded := true
    currentCheckPassed := true }

def shieldPrivateUseFreshBoundary : VersionedSourcedBoundary :=
  { boundary := shieldPrivateUseBoundary
    source := leanFoundationClaimsFreshSource }

theorem lean_foundation_claims_fresh_source_valid :
    FreshSourceValid leanFoundationClaimsFreshSource := by
  exact ⟨lean_foundation_claims_source_valid, rfl, rfl⟩

theorem shield_fresh_private_daily_use_promotable :
    FreshClaimPromotable shieldPrivateUseFreshBoundary Claim.privateDailyUse := by
  exact ⟨shield_boundary_consistent, shield_boundary_claims_private_daily_use,
    lean_foundation_claims_fresh_source_valid⟩

/-- A stale or unversioned source cannot support a current promotable claim. -/
theorem stale_source_not_fresh_promotable (b : VersionedSourcedBoundary) (c : Claim)
    (h : ¬ FreshSourceValid b.source) :
    ¬ FreshClaimPromotable b c := by
  intro hp
  exact h hp.2.2

def composeFreshSources (a b : VersionedEvidenceSource) : VersionedEvidenceSource :=
  { source := composeSources a.source b.source
    versionRecorded := a.versionRecorded && b.versionRecorded
    currentCheckPassed := a.currentCheckPassed && b.currentCheckPassed }

def composeFreshBoundaries (a b : VersionedSourcedBoundary) : VersionedSourcedBoundary :=
  { boundary := composeBoundaries a.boundary b.boundary
    source := composeFreshSources a.source b.source }

theorem composed_fresh_source_requires_left (a b : VersionedEvidenceSource) :
    FreshSourceValid (composeFreshSources a b) → FreshSourceValid a := by
  intro h
  exact ⟨composed_source_valid_requires_left a.source b.source h.1,
    and_true_left (by simpa [FreshSourceValid, composeFreshSources] using h.2.1),
    and_true_left (by simpa [FreshSourceValid, composeFreshSources] using h.2.2)⟩

theorem composed_fresh_source_requires_right (a b : VersionedEvidenceSource) :
    FreshSourceValid (composeFreshSources a b) → FreshSourceValid b := by
  intro h
  exact ⟨composed_source_valid_requires_right a.source b.source h.1,
    and_true_right (by simpa [FreshSourceValid, composeFreshSources] using h.2.1),
    and_true_right (by simpa [FreshSourceValid, composeFreshSources] using h.2.2)⟩

/-- Freshness also cannot be manufactured by aggregation. If a composed source
    is fresh, both inputs were already fresh. -/
theorem composed_fresh_source_requires_both (a b : VersionedEvidenceSource) :
    FreshSourceValid (composeFreshSources a b) → FreshSourceValid a ∧ FreshSourceValid b := by
  intro h
  exact ⟨composed_fresh_source_requires_left a b h,
    composed_fresh_source_requires_right a b h⟩

/-- A current composed claim can promote only when both inputs had fresh,
    version-pinned source records. -/
theorem composed_fresh_claim_requires_both_sources (a b : VersionedSourcedBoundary) (c : Claim) :
    FreshClaimPromotable (composeFreshBoundaries a b) c →
      FreshSourceValid a.source ∧ FreshSourceValid b.source := by
  intro h
  exact composed_fresh_source_requires_both a.source b.source h.2.2

/-- Self-composition of the current public Lean source remains fresh because the
    same version-pinned `lake build` evidence is present on both sides. -/
theorem shield_fresh_self_composition_private_daily_use_promotable :
    FreshClaimPromotable
      (composeFreshBoundaries shieldPrivateUseFreshBoundary shieldPrivateUseFreshBoundary)
      Claim.privateDailyUse := by
  exact ⟨shield_boundary_self_composition_consistent, rfl,
    ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩⟩

/-- A still stricter source record for operational dashboards: the evidence is
    source-valid, version-pinned, freshly checked, and not expired. Expired
    evidence may remain visible as history, but not as current authority. -/
structure ExpiringEvidenceSource where
  source : VersionedEvidenceSource
  notExpired : Bool

def CurrentSourceValid (s : ExpiringEvidenceSource) : Prop :=
  FreshSourceValid s.source ∧ s.notExpired = true

structure CurrentSourcedBoundary where
  boundary : ClaimBoundary
  source : ExpiringEvidenceSource

def CurrentClaimPromotable (b : CurrentSourcedBoundary) (c : Claim) : Prop :=
  BoundaryConsistent b.boundary ∧ Allows b.boundary.doesClaim c ∧ CurrentSourceValid b.source

def leanFoundationClaimsCurrentSource : ExpiringEvidenceSource :=
  { source := leanFoundationClaimsFreshSource
    notExpired := true }

def shieldPrivateUseCurrentBoundary : CurrentSourcedBoundary :=
  { boundary := shieldPrivateUseBoundary
    source := leanFoundationClaimsCurrentSource }

theorem lean_foundation_claims_current_source_valid :
    CurrentSourceValid leanFoundationClaimsCurrentSource := by
  exact ⟨lean_foundation_claims_fresh_source_valid, rfl⟩

theorem shield_current_private_daily_use_promotable :
    CurrentClaimPromotable shieldPrivateUseCurrentBoundary Claim.privateDailyUse := by
  exact ⟨shield_boundary_consistent, shield_boundary_claims_private_daily_use,
    lean_foundation_claims_current_source_valid⟩

/-- Expired evidence cannot support a current promotable claim. -/
theorem expired_source_not_current_promotable (b : CurrentSourcedBoundary) (c : Claim)
    (h : ¬ CurrentSourceValid b.source) :
    ¬ CurrentClaimPromotable b c := by
  intro hp
  exact h hp.2.2

def composeCurrentSources (a b : ExpiringEvidenceSource) : ExpiringEvidenceSource :=
  { source := composeFreshSources a.source b.source
    notExpired := a.notExpired && b.notExpired }

def composeCurrentBoundaries (a b : CurrentSourcedBoundary) : CurrentSourcedBoundary :=
  { boundary := composeBoundaries a.boundary b.boundary
    source := composeCurrentSources a.source b.source }

theorem composed_current_source_requires_left (a b : ExpiringEvidenceSource) :
    CurrentSourceValid (composeCurrentSources a b) → CurrentSourceValid a := by
  intro h
  exact ⟨composed_fresh_source_requires_left a.source b.source h.1,
    and_true_left (by simpa [CurrentSourceValid, composeCurrentSources] using h.2)⟩

theorem composed_current_source_requires_right (a b : ExpiringEvidenceSource) :
    CurrentSourceValid (composeCurrentSources a b) → CurrentSourceValid b := by
  intro h
  exact ⟨composed_fresh_source_requires_right a.source b.source h.1,
    and_true_right (by simpa [CurrentSourceValid, composeCurrentSources] using h.2)⟩

/-- Current authority cannot be manufactured by aggregation: both inputs must
    already be fresh and unexpired. -/
theorem composed_current_source_requires_both (a b : ExpiringEvidenceSource) :
    CurrentSourceValid (composeCurrentSources a b) → CurrentSourceValid a ∧ CurrentSourceValid b := by
  intro h
  exact ⟨composed_current_source_requires_left a b h,
    composed_current_source_requires_right a b h⟩

theorem composed_current_claim_requires_both_sources (a b : CurrentSourcedBoundary) (c : Claim) :
    CurrentClaimPromotable (composeCurrentBoundaries a b) c →
      CurrentSourceValid a.source ∧ CurrentSourceValid b.source := by
  intro h
  exact composed_current_source_requires_both a.source b.source h.2.2

/-- Refreshing a fresh source by recording a new current check makes it current
    again. This models update without deleting the old historical artifact. -/
def refreshSource (s : VersionedEvidenceSource) : ExpiringEvidenceSource :=
  { source :=
      { source := s.source
        versionRecorded := s.versionRecorded
        currentCheckPassed := true }
    notExpired := true }

theorem refresh_source_current_if_source_and_version_valid (s : VersionedEvidenceSource)
    (hSource : SourceValid s.source) (hVersion : s.versionRecorded = true) :
    CurrentSourceValid (refreshSource s) := by
  exact ⟨⟨hSource, hVersion, rfl⟩, rfl⟩

theorem shield_current_self_composition_private_daily_use_promotable :
    CurrentClaimPromotable
      (composeCurrentBoundaries shieldPrivateUseCurrentBoundary shieldPrivateUseCurrentBoundary)
      Claim.privateDailyUse := by
  exact ⟨shield_boundary_self_composition_consistent, rfl,
    ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, rfl⟩⟩

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
#check @shield_boundary_consistent
#check @compose_boundary_consistent
#check @shield_boundary_self_composition_consistent
#check @shield_sourced_private_daily_use_promotable
#check @invalid_source_not_promotable
#check @composed_source_valid_requires_both
#check @composed_sourced_claim_requires_both_sources
#check @shield_sourced_self_composition_private_daily_use_promotable
#check @shield_fresh_private_daily_use_promotable
#check @stale_source_not_fresh_promotable
#check @composed_fresh_source_requires_both
#check @composed_fresh_claim_requires_both_sources
#check @shield_fresh_self_composition_private_daily_use_promotable
#check @shield_current_private_daily_use_promotable
#check @expired_source_not_current_promotable
#check @composed_current_source_requires_both
#check @composed_current_claim_requires_both_sources
#check @refresh_source_current_if_source_and_version_valid
#check @shield_current_self_composition_private_daily_use_promotable
#print axioms shield_private_use_block_safe
#print axioms production_authorization_requires_gate
#print axioms checkpoint_authorization_requires_gate
#print axioms composed_public_release_requires_both_inputs
#print axioms composed_production_requires_both_inputs
#print axioms compose_preserves_no_production_authority
#print axioms combined_promotable_requires_both
#print axioms blocked_left_not_promotable
#print axioms refused_left_not_promotable
#print axioms shield_boundary_consistent
#print axioms compose_boundary_consistent
#print axioms shield_sourced_private_daily_use_promotable
#print axioms invalid_source_not_promotable
#print axioms composed_source_valid_requires_both
#print axioms composed_sourced_claim_requires_both_sources
#print axioms shield_fresh_private_daily_use_promotable
#print axioms stale_source_not_fresh_promotable
#print axioms composed_fresh_source_requires_both
#print axioms composed_fresh_claim_requires_both_sources
#print axioms shield_current_private_daily_use_promotable
#print axioms expired_source_not_current_promotable
#print axioms composed_current_source_requires_both
#print axioms composed_current_claim_requires_both_sources
#print axioms refresh_source_current_if_source_and_version_valid
