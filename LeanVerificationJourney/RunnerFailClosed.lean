namespace RunnerFailClosed

inductive Kind where
  | atomic
  | external
  | composed
  | multiRegion
  | quorum
  | manual
  | unknown
deriving DecidableEq, Repr

inductive Verdict where
  | certified
  | refused
  | deferred
  | unverifiable
deriving DecidableEq, Repr

inductive NonCertifiedVerdict where
  | refused
  | deferred
  | unverifiable
deriving DecidableEq, Repr

def NonCertifiedVerdict.toVerdict : NonCertifiedVerdict → Verdict
  | NonCertifiedVerdict.refused => Verdict.refused
  | NonCertifiedVerdict.deferred => Verdict.deferred
  | NonCertifiedVerdict.unverifiable => Verdict.unverifiable

structure Facts where
  kind : Kind
  path_ok : Bool
  artifact_present : Bool
  artifact_hash_ok : Bool
  manifest_ok : Bool
  manifest_hash_ok : Bool
  timeout_ok : Bool
  sandbox_ok : Bool
  rung_within_ceiling : Bool
  plugin_output_legal : Bool
  plugin_rung_le_ceiling : Bool
  plugin_rung_le_declared : Bool
  checker_positive : Bool
  all_parts_certified : Bool
  declared_eq_weakest : Bool
  quorum_count_ge_required : Bool
  quorum_distinct_count_ge_required : Bool
deriving DecidableEq, Repr

def commonOk (f : Facts) : Bool :=
  f.path_ok && f.artifact_present && f.artifact_hash_ok

def certifiedPreconditions (f : Facts) : Bool :=
  match f.kind with
  | Kind.atomic =>
      commonOk f && f.rung_within_ceiling && f.checker_positive
  | Kind.external =>
      commonOk f
        && f.manifest_ok
        && f.manifest_hash_ok
        && f.rung_within_ceiling
        && f.timeout_ok
        && f.sandbox_ok
        && f.plugin_output_legal
        && f.plugin_rung_le_ceiling
        && f.plugin_rung_le_declared
        && f.checker_positive
  | Kind.composed | Kind.multiRegion =>
      commonOk f && f.checker_positive && f.all_parts_certified && f.declared_eq_weakest
  | Kind.quorum =>
      commonOk f
        && f.checker_positive
        && f.quorum_count_ge_required
        && f.quorum_distinct_count_ge_required
  | Kind.manual | Kind.unknown =>
      false

def negativeCore (f : Facts) : NonCertifiedVerdict :=
  if !f.path_ok then
    NonCertifiedVerdict.refused
  else if !f.artifact_present then
    NonCertifiedVerdict.refused
  else if !f.artifact_hash_ok then
    NonCertifiedVerdict.refused
  else
    match f.kind with
    | Kind.manual => NonCertifiedVerdict.deferred
    | Kind.unknown => NonCertifiedVerdict.unverifiable
    | Kind.atomic =>
        if !f.rung_within_ceiling then NonCertifiedVerdict.refused else NonCertifiedVerdict.refused
    | Kind.external =>
        if !f.manifest_ok then
          NonCertifiedVerdict.refused
        else if !f.manifest_hash_ok then
          NonCertifiedVerdict.refused
        else if !f.rung_within_ceiling then
          NonCertifiedVerdict.refused
        else if !f.timeout_ok then
          NonCertifiedVerdict.unverifiable
        else if !f.sandbox_ok then
          NonCertifiedVerdict.unverifiable
        else if !f.plugin_output_legal then
          NonCertifiedVerdict.unverifiable
        else if !f.plugin_rung_le_ceiling then
          NonCertifiedVerdict.refused
        else if !f.plugin_rung_le_declared then
          NonCertifiedVerdict.refused
        else
          NonCertifiedVerdict.refused
    | Kind.composed | Kind.multiRegion =>
        if !f.all_parts_certified then
          NonCertifiedVerdict.deferred
        else if !f.declared_eq_weakest then
          NonCertifiedVerdict.refused
        else
          NonCertifiedVerdict.refused
    | Kind.quorum =>
        if !f.quorum_count_ge_required then
          NonCertifiedVerdict.refused
        else if !f.quorum_distinct_count_ge_required then
          NonCertifiedVerdict.refused
        else
          NonCertifiedVerdict.refused

def negativeVerdict (f : Facts) : Verdict :=
  (negativeCore f).toVerdict

def decide (f : Facts) : Verdict :=
  if certifiedPreconditions f then Verdict.certified else negativeVerdict f

def reasonCode (f : Facts) : String :=
  if !f.path_ok then
    "PATH_REJECTED"
  else if !f.artifact_present then
    "ARTIFACT_MISSING"
  else if !f.artifact_hash_ok then
    "ARTIFACT_HASH_MISMATCH"
  else
    match f.kind with
    | Kind.manual => "DEFERRED_PENDING_HUMAN"
    | Kind.unknown => "UNKNOWN_CHECKER"
    | Kind.atomic =>
        if !f.rung_within_ceiling then
          "RUNG_CEILING_EXCEEDED"
        else if f.checker_positive then
          "OK"
        else
          "CHECKER_ERROR"
    | Kind.external =>
        if !f.manifest_ok then
          "MANIFEST_INVALID"
        else if !f.manifest_hash_ok then
          "CHECKER_HASH_MISMATCH"
        else if !f.rung_within_ceiling then
          "RUNG_CEILING_EXCEEDED"
        else if !f.timeout_ok then
          "CHECKER_TIMEOUT"
        else if !f.sandbox_ok then
          "SANDBOX_UNAVAILABLE"
        else if !f.plugin_output_legal then
          "CHECKER_ERROR"
        else if !f.plugin_rung_le_ceiling then
          "RUNG_CEILING_EXCEEDED"
        else if !f.plugin_rung_le_declared then
          "RUNG_LAUNDERING"
        else if f.checker_positive then
          "OK"
        else
          "CHECKER_ERROR"
    | Kind.composed | Kind.multiRegion =>
        if !f.all_parts_certified then
          "WEAK_SUBBARRIER"
        else if !f.declared_eq_weakest then
          "RUNG_LAUNDERING"
        else if f.checker_positive then
          "OK"
        else
          "CHECKER_ERROR"
    | Kind.quorum =>
        if !f.quorum_count_ge_required then
          "QUORUM_NOT_MET"
        else if !f.quorum_distinct_count_ge_required then
          "QUORUM_NOT_INDEPENDENT"
        else if f.checker_positive then
          "OK"
        else
          "QUORUM_NOT_MET"

theorem negative_not_certified (f : Facts) :
    negativeVerdict f ≠ Verdict.certified := by
  cases h : negativeCore f <;> simp [negativeVerdict, h, NonCertifiedVerdict.toVerdict]

theorem only_positive_certifies (f : Facts) :
    decide f = Verdict.certified → certifiedPreconditions f = true := by
  intro h
  by_cases hpre : certifiedPreconditions f = true
  · exact hpre
  · have hneg : negativeVerdict f = Verdict.certified := by
      simpa [decide, hpre] using h
    exact False.elim ((negative_not_certified f) hneg)

theorem certified_requires_checker_positive (f : Facts) :
    certifiedPreconditions f = true → f.checker_positive = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases checker_positive <;> simp [certifiedPreconditions, commonOk]

theorem certified_requires_path_ok (f : Facts) :
    certifiedPreconditions f = true → f.path_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases path_ok <;> simp [certifiedPreconditions, commonOk]

theorem certified_requires_artifact_present (f : Facts) :
    certifiedPreconditions f = true → f.artifact_present = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases artifact_present <;> simp [certifiedPreconditions, commonOk]

theorem certified_requires_artifact_hash_ok (f : Facts) :
    certifiedPreconditions f = true → f.artifact_hash_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases artifact_hash_ok <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_manifest_ok (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.manifest_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases manifest_ok <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_manifest_hash_ok (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.manifest_hash_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases manifest_hash_ok <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_timeout_ok (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.timeout_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases timeout_ok <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_sandbox_ok (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.sandbox_ok = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases sandbox_ok <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_plugin_output_legal (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.plugin_output_legal = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases plugin_output_legal <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_plugin_rung_le_ceiling (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.plugin_rung_le_ceiling = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases plugin_rung_le_ceiling <;> simp [certifiedPreconditions, commonOk]

theorem external_cert_requires_plugin_rung_le_declared (f : Facts) :
    f.kind = Kind.external → certifiedPreconditions f = true → f.plugin_rung_le_declared = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases plugin_rung_le_declared <;> simp [certifiedPreconditions, commonOk]

theorem atomic_or_external_cert_requires_rung_within_ceiling (f : Facts) :
    (f.kind = Kind.atomic ∨ f.kind = Kind.external) →
      certifiedPreconditions f = true →
      f.rung_within_ceiling = true := by
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> cases rung_within_ceiling <;> simp [certifiedPreconditions, commonOk]

theorem runner_no_fail_open (f : Facts) :
    f.checker_positive = false → decide f ≠ Verdict.certified := by
  intro hneg hcert
  have hpos := certified_requires_checker_positive f (only_positive_certifies f hcert)
  simp [hneg] at hpos

theorem no_cert_if_path_rejected (f : Facts) :
    f.path_ok = false → decide f ≠ Verdict.certified := by
  intro hbad hcert
  have hok := certified_requires_path_ok f (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_cert_if_artifact_missing (f : Facts) :
    f.artifact_present = false → decide f ≠ Verdict.certified := by
  intro hbad hcert
  have hok := certified_requires_artifact_present f (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_cert_if_artifact_hash_bad (f : Facts) :
    f.artifact_hash_ok = false → decide f ≠ Verdict.certified := by
  intro hbad hcert
  have hok := certified_requires_artifact_hash_ok f (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_manifest_invalid (f : Facts) :
    f.kind = Kind.external → f.manifest_ok = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_manifest_ok f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_manifest_hash_bad (f : Facts) :
    f.kind = Kind.external → f.manifest_hash_ok = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_manifest_hash_ok f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_timeout_bad (f : Facts) :
    f.kind = Kind.external → f.timeout_ok = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_timeout_ok f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_sandbox_bad (f : Facts) :
    f.kind = Kind.external → f.sandbox_ok = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_sandbox_ok f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_plugin_output_illegal (f : Facts) :
    f.kind = Kind.external → f.plugin_output_legal = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_plugin_output_legal f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_plugin_rung_over_ceiling (f : Facts) :
    f.kind = Kind.external → f.plugin_rung_le_ceiling = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_plugin_rung_le_ceiling f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_external_cert_if_plugin_rung_over_declared (f : Facts) :
    f.kind = Kind.external → f.plugin_rung_le_declared = false → decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := external_cert_requires_plugin_rung_le_declared f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem no_atomic_or_external_cert_if_rung_over_ceiling (f : Facts) :
    (f.kind = Kind.atomic ∨ f.kind = Kind.external) →
      f.rung_within_ceiling = false →
      decide f ≠ Verdict.certified := by
  intro hkind hbad hcert
  have hok := atomic_or_external_cert_requires_rung_within_ceiling f hkind (only_positive_certifies f hcert)
  simp [hbad] at hok

theorem composed_cert_requires_parts (f : Facts) :
    decide f = Verdict.certified →
      f.kind = Kind.composed →
      f.all_parts_certified = true ∧ f.declared_eq_weakest = true := by
  intro hcert hkind
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> simp at hkind hcert ⊢
    have hpre := only_positive_certifies
      { kind := Kind.composed, path_ok := path_ok, artifact_present := artifact_present,
        artifact_hash_ok := artifact_hash_ok, manifest_ok := manifest_ok,
        manifest_hash_ok := manifest_hash_ok, timeout_ok := timeout_ok, sandbox_ok := sandbox_ok,
        rung_within_ceiling := rung_within_ceiling, plugin_output_legal := plugin_output_legal,
        plugin_rung_le_ceiling := plugin_rung_le_ceiling,
        plugin_rung_le_declared := plugin_rung_le_declared, checker_positive := checker_positive,
        all_parts_certified := all_parts_certified, declared_eq_weakest := declared_eq_weakest,
        quorum_count_ge_required := quorum_count_ge_required,
        quorum_distinct_count_ge_required := quorum_distinct_count_ge_required } hcert
    simp [certifiedPreconditions, commonOk] at hpre
    exact ⟨hpre.1.2, hpre.2⟩

theorem multi_region_cert_requires_parts (f : Facts) :
    decide f = Verdict.certified →
      f.kind = Kind.multiRegion →
      f.all_parts_certified = true ∧ f.declared_eq_weakest = true := by
  intro hcert hkind
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> simp at hkind hcert ⊢
    have hpre := only_positive_certifies
      { kind := Kind.multiRegion, path_ok := path_ok, artifact_present := artifact_present,
        artifact_hash_ok := artifact_hash_ok, manifest_ok := manifest_ok,
        manifest_hash_ok := manifest_hash_ok, timeout_ok := timeout_ok, sandbox_ok := sandbox_ok,
        rung_within_ceiling := rung_within_ceiling, plugin_output_legal := plugin_output_legal,
        plugin_rung_le_ceiling := plugin_rung_le_ceiling,
        plugin_rung_le_declared := plugin_rung_le_declared, checker_positive := checker_positive,
        all_parts_certified := all_parts_certified, declared_eq_weakest := declared_eq_weakest,
        quorum_count_ge_required := quorum_count_ge_required,
        quorum_distinct_count_ge_required := quorum_distinct_count_ge_required } hcert
    simp [certifiedPreconditions, commonOk] at hpre
    exact ⟨hpre.1.2, hpre.2⟩

theorem quorum_cert_requires_threshold_and_independence (f : Facts) :
    decide f = Verdict.certified →
      f.kind = Kind.quorum →
      f.quorum_count_ge_required = true ∧ f.quorum_distinct_count_ge_required = true := by
  intro hcert hkind
  cases f with
  | mk kind path_ok artifact_present artifact_hash_ok manifest_ok manifest_hash_ok timeout_ok
      sandbox_ok rung_within_ceiling plugin_output_legal plugin_rung_le_ceiling
      plugin_rung_le_declared checker_positive all_parts_certified declared_eq_weakest
      quorum_count_ge_required quorum_distinct_count_ge_required =>
    cases kind <;> simp at hkind hcert ⊢
    have hpre := only_positive_certifies
      { kind := Kind.quorum, path_ok := path_ok, artifact_present := artifact_present,
        artifact_hash_ok := artifact_hash_ok, manifest_ok := manifest_ok,
        manifest_hash_ok := manifest_hash_ok, timeout_ok := timeout_ok, sandbox_ok := sandbox_ok,
        rung_within_ceiling := rung_within_ceiling, plugin_output_legal := plugin_output_legal,
        plugin_rung_le_ceiling := plugin_rung_le_ceiling,
        plugin_rung_le_declared := plugin_rung_le_declared, checker_positive := checker_positive,
        all_parts_certified := all_parts_certified, declared_eq_weakest := declared_eq_weakest,
        quorum_count_ge_required := quorum_count_ge_required,
        quorum_distinct_count_ge_required := quorum_distinct_count_ge_required } hcert
    simp [certifiedPreconditions, commonOk] at hpre
    exact ⟨hpre.1.2, hpre.2⟩

#print axioms runner_no_fail_open
#print axioms only_positive_certifies
#print axioms no_cert_if_artifact_hash_bad
#print axioms composed_cert_requires_parts
#print axioms quorum_cert_requires_threshold_and_independence

def kindName : Kind → String
  | Kind.atomic => "atomic"
  | Kind.external => "external"
  | Kind.composed => "composed"
  | Kind.multiRegion => "multi-region"
  | Kind.quorum => "quorum"
  | Kind.manual => "manual"
  | Kind.unknown => "unknown"

def verdictName : Verdict → String
  | Verdict.certified => "CERTIFIED"
  | Verdict.refused => "REFUSED"
  | Verdict.deferred => "DEFERRED"
  | Verdict.unverifiable => "UNVERIFIABLE-HERE"

def allKinds : List Kind :=
  [Kind.atomic, Kind.external, Kind.composed, Kind.multiRegion, Kind.quorum, Kind.manual, Kind.unknown]

def fieldCount : Nat := 16
def factSpaceSize : Nat := 65536

def bit (code idx : Nat) : Bool :=
  (code >>> idx) % 2 == 1

def factsOfCode (kind : Kind) (code : Nat) : Facts :=
  {
    kind := kind,
    path_ok := bit code 0,
    artifact_present := bit code 1,
    artifact_hash_ok := bit code 2,
    manifest_ok := bit code 3,
    manifest_hash_ok := bit code 4,
    timeout_ok := bit code 5,
    sandbox_ok := bit code 6,
    rung_within_ceiling := bit code 7,
    plugin_output_legal := bit code 8,
    plugin_rung_le_ceiling := bit code 9,
    plugin_rung_le_declared := bit code 10,
    checker_positive := bit code 11,
    all_parts_certified := bit code 12,
    declared_eq_weakest := bit code 13,
    quorum_count_ge_required := bit code 14,
    quorum_distinct_count_ge_required := bit code 15
  }

def rowsForKind (kind : Kind) : List (Kind × Nat × Verdict × String) :=
  (List.range factSpaceSize).map fun code =>
    let facts := factsOfCode kind code
    (kind, code, decide facts, reasonCode facts)

def tableRows : List (Kind × Nat × Verdict × String) :=
  allKinds.foldr (fun kind acc => rowsForKind kind ++ acc) []

end RunnerFailClosed
