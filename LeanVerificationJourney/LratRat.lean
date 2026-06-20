import LeanVerificationJourney.Lrat

/-
  LratRat.lean — completing the checker: RAT support (general DRAT/LRAT).
  ----------------------------------------------------------------------------
  The RUP checker in `Lrat.lean` proves added clauses are *implied* by the
  formula (entailment-preserving). RAT clauses are NOT implied — adding one can
  change the set of models — yet they are *satisfiability-preserving*, which is
  all an UNSAT proof needs. That weaker, subtler invariant is what makes a
  checker GENERAL: every DRAT/LRAT proof (incl. those using extended resolution
  / blocked clauses, as in Schur-5, Keller-7, Pythagorean) is RUP + RAT steps.

  The heart is `rat_add_sat`: the classic flipped-assignment argument — if `a`
  satisfies the db but falsifies a RAT clause `C` on pivot `l`, flip `l` in `a`;
  the RAT condition (every resolvent on `l` is entailed) guarantees the flipped
  assignment still satisfies the db, and now satisfies `C` too. Formalized here
  with trusted base `propext, Quot.sound` — no Classical.choice, no compiler.

  Result: `checkProofGen_unsat` — a verified checker over a mixed list of RUP/RAT
  steps. `rup_add_sat` + `rat_step_sat` are the per-step satisfiability-
  preservation lemmas; `unsat_of_sat_preserved` is the top-level bridge. The
  remaining gap to an end-to-end file checker is purely the (untrusted) parser
  that turns an LRAT file's RAT lines into `PStep.rat` data.
-/

/-- A formula is satisfiable. -/
def Sat (f : Formula) : Prop := ∃ a, formulaTrue a f = true

-- helpers ---------------------------------------------------------------------

theorem clauseTrue_of_mem (a : Assign) (c : Clause) (l : Lit)
    (hl : l ∈ c) (ht : litTrue a l = true) : clauseTrue a c = true := by
  simp only [clauseTrue]; exact List.any_eq_true.mpr ⟨l, hl, ht⟩

theorem litFalse_of_clauseFalse (a : Assign) (c : Clause)
    (hc : clauseTrue a c = false) (l : Lit) (hl : l ∈ c) : litTrue a l = false := by
  cases ht : litTrue a l with
  | false => rfl
  | true => have := clauseTrue_of_mem a c l hl ht; rw [hc] at this; simp at this

/-- The only literals on `pivot`'s variable are `pivot` and `pivot.flip`. -/
theorem var_eq_cases (m pivot : Lit) (h : m.var = pivot.var) :
    m = pivot ∨ m = pivot.flip := by
  cases m with | mk mv mn => cases pivot with | mk pv pn =>
  simp only at h; subst h
  cases mn <;> cases pn <;> simp [Lit.flip]

/-- Flip `pivot`'s variable so that `pivot` becomes true. -/
def flipAssign (a : Assign) (pivot : Lit) : Assign :=
  fun v => if v = pivot.var then !pivot.neg else a v

theorem flipAssign_pivot (a : Assign) (pivot : Lit) :
    litTrue (flipAssign a pivot) pivot = true := by
  simp only [litTrue, flipAssign]; cases pivot.neg <;> simp

theorem flipAssign_other (a : Assign) (pivot l : Lit) (h : l.var ≠ pivot.var) :
    litTrue (flipAssign a pivot) l = litTrue a l := by
  simp only [litTrue, flipAssign, if_neg h]

/-- Resolvent of `C` (on `pivot`) and `D` (on `pivot.flip`): drop `pivot` from `C`
    and `pivot.flip` from `D`. -/
def resolvent (C D : Clause) (pivot : Lit) : Clause :=
  C.filter (fun l => decide (l ≠ pivot)) ++ D.filter (fun l => decide (l ≠ pivot.flip))

-- THE THEOREM -----------------------------------------------------------------

/-- RAT addition preserves satisfiability. If `pivot ∈ C` and for every db-clause `D`
    containing `pivot.flip` the resolvent is entailed by `db`, then `Sat db → Sat (db ++ [C])`. -/
theorem rat_add_sat (db : Formula) (C : Clause) (pivot : Lit)
    (hpiv : pivot ∈ C)
    (hrat : ∀ D, D ∈ db → pivot.flip ∈ D →
       ∀ a, formulaTrue a db = true → clauseTrue a (resolvent C D pivot) = true)
    (hsat : Sat db) : Sat (db ++ [C]) := by
  obtain ⟨a, ha⟩ := hsat
  cases hCa : clauseTrue a C with
  | true => exact ⟨a, by simp [formulaTrue_snoc, ha, hCa]⟩
  | false =>
    refine ⟨flipAssign a pivot, ?_⟩
    rw [formulaTrue_snoc]
    have hCflip : clauseTrue (flipAssign a pivot) C = true :=
      clauseTrue_of_mem _ C pivot hpiv (flipAssign_pivot a pivot)
    have hdbflip : formulaTrue (flipAssign a pivot) db = true := by
      rw [formulaTrue]
      refine List.all_eq_true.mpr ?_
      intro D hD
      have haD : clauseTrue a D = true := List.all_eq_true.mp ha D hD
      cases hpivD : decide (pivot ∈ D) with
      | true =>
        exact clauseTrue_of_mem _ D pivot (of_decide_eq_true hpivD) (flipAssign_pivot a pivot)
      | false =>
        have hpiv_nmem : pivot ∉ D := of_decide_eq_false hpivD
        cases hflipD : decide (pivot.flip ∈ D) with
        | true =>
          have hflip_mem : pivot.flip ∈ D := of_decide_eq_true hflipD
          have hres := hrat D hD hflip_mem a ha
          obtain ⟨m, hm_mem, hm_true⟩ := List.any_eq_true.mp hres
          rw [resolvent, List.mem_append] at hm_mem
          rcases hm_mem with hmC | hmD
          · rw [List.mem_filter] at hmC
            have hf := litFalse_of_clauseFalse a C hCa m hmC.1
            rw [hf] at hm_true; simp at hm_true
          · rw [List.mem_filter] at hmD
            have hm_ne_flip : m ≠ pivot.flip := of_decide_eq_true hmD.2
            have hm_ne_piv : m ≠ pivot := fun h => hpiv_nmem (h ▸ hmD.1)
            have hvar : m.var ≠ pivot.var := fun hv =>
              (var_eq_cases m pivot hv).elim hm_ne_piv hm_ne_flip
            refine clauseTrue_of_mem _ D m hmD.1 ?_
            rw [flipAssign_other a pivot m hvar]; exact hm_true
        | false =>
          have hflip_nmem : pivot.flip ∉ D := of_decide_eq_false hflipD
          obtain ⟨m, hm_mem, hm_true⟩ := List.any_eq_true.mp haD
          have hm_ne_piv : m ≠ pivot := fun h => hpiv_nmem (h ▸ hm_mem)
          have hm_ne_flip : m ≠ pivot.flip := fun h => hflip_nmem (h ▸ hm_mem)
          have hvar : m.var ≠ pivot.var := fun hv =>
            (var_eq_cases m pivot hv).elim hm_ne_piv hm_ne_flip
          refine clauseTrue_of_mem _ D m hm_mem ?_
          rw [flipAssign_other a pivot m hvar]; exact hm_true
    simp [hdbflip, hCflip]

-- COMPUTABLE RAT CHECK --------------------------------------------------------

/-- Verify `C` is RAT on `pivot` w.r.t. `db`: for every db-clause `D` containing
    `pivot.flip`, the resolvent must be RUP (checked with that clause's hints). -/
def checkRAT (db : Formula) (C : Clause) (pivot : Lit) (hintOf : Nat → List Nat) : Bool :=
  (List.range db.length).all (fun i =>
    match db[i]? with
    | some D => if decide (pivot.flip ∈ D) then checkRUP db (resolvent C D pivot) (hintOf i) else true
    | none => true)

theorem checkRAT_sound (db : Formula) (C : Clause) (pivot : Lit) (hintOf : Nat → List Nat)
    (h : checkRAT db C pivot hintOf = true) :
    ∀ D, D ∈ db → pivot.flip ∈ D →
      ∀ a, formulaTrue a db = true → clauseTrue a (resolvent C D pivot) = true := by
  intro D hD hflip a ha
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hD
  have hi_range : i ∈ List.range db.length := List.mem_range.mpr hilt
  have hpi : (match db[i]? with
      | some D => if decide (pivot.flip ∈ D) then checkRUP db (resolvent C D pivot) (hintOf i) else true
      | none => true) = true := List.all_eq_true.mp h i hi_range
  have hget? : db[i]? = some D := by rw [List.getElem?_eq_getElem hilt, hget]
  have hd : decide (pivot.flip ∈ D) = true := by simp [hflip]
  simp only [hget?] at hpi
  rw [if_pos hd] at hpi
  exact rup_sound db (resolvent C D pivot) (hintOf i) hpi a ha

-- SAT-PRESERVATION PER STEP ----------------------------------------------------

/-- A verified RUP addition preserves satisfiability. -/
theorem rup_add_sat (db : Formula) (C : Clause) (hints : List Nat)
    (h : checkRUP db C hints = true) (hsat : Sat db) : Sat (db ++ [C]) := by
  obtain ⟨a, ha⟩ := hsat
  exact ⟨a, by simp [formulaTrue_snoc, ha, rup_sound db C hints h a ha]⟩

/-- A verified RAT addition preserves satisfiability. -/
theorem rat_step_sat (db : Formula) (C : Clause) (pivot : Lit) (hintOf : Nat → List Nat)
    (hpiv : pivot ∈ C) (h : checkRAT db C pivot hintOf = true) (hsat : Sat db) :
    Sat (db ++ [C]) :=
  rat_add_sat db C pivot hpiv (checkRAT_sound db C pivot hintOf h) hsat

-- TOP-LEVEL BRIDGE -------------------------------------------------------------

/-- If a derivation preserves satisfiability and the final db contains the empty
    clause, the original formula is UNSAT. -/
theorem unsat_of_sat_preserved (f g : Formula)
    (hpres : Sat f → Sat g) (hempty : [] ∈ g) : Unsat f := by
  intro a
  cases hh : formulaTrue a f with
  | false => rfl
  | true =>
    obtain ⟨b, hb⟩ := hpres ⟨a, hh⟩
    have hcl : clauseTrue b [] = true := List.all_eq_true.mp hb [] hempty
    simp [clauseTrue] at hcl

-- WORKED EXAMPLE: a RAT clause that is NOT RUP -------------------------------
-- C = (x1 ∨ x4) is *blocked* on x1 w.r.t. db = {(x2 ∨ x3)} (no clause has ¬x1),
-- hence RAT — yet it is NOT implied by db (the model x1=F,x4=F,x2=T,x3=T ⊨ db, ⊭ C).
-- So a pure-RUP checker could not add it; the RAT check accepts it, and it
-- provably preserves satisfiability.

def dbDemo : Formula := [[x 2, x 3]]
def cDemo : Clause := [x 1, x 4]

theorem ratDemo_sat : Sat (dbDemo ++ [cDemo]) :=
  rat_step_sat dbDemo cDemo (x 1) (fun _ => [])
    (by decide) (by decide) ⟨(fun _ => true), by decide⟩

-- GENERAL CHECKER: a list of mixed RUP/RAT steps ----------------------------

/-- A proof step: a RUP clause (+hints) or a RAT clause (+pivot, +per-clause hints). -/
inductive PStep where
  | rup : Clause → List Nat → PStep
  | rat : Clause → Lit → List (Nat × List Nat) → PStep

def stepClause : PStep → Clause
  | .rup c _ => c
  | .rat c _ _ => c

def hintLookup (l : List (Nat × List Nat)) (i : Nat) : List Nat :=
  ((l.find? (fun p => p.1 == i)).map Prod.snd).getD []

def checkStep (db : Formula) : PStep → Bool
  | .rup c hints => checkRUP db c hints
  | .rat c pivot rhints => decide (pivot ∈ c) && checkRAT db c pivot (hintLookup rhints)

theorem checkStep_sat (db : Formula) (s : PStep) (hsat : Sat db)
    (h : checkStep db s = true) : Sat (db ++ [stepClause s]) := by
  cases s with
  | rup c hints => exact rup_add_sat db c hints h hsat
  | rat c pivot rhints =>
    simp only [checkStep] at h
    cases hp : decide (pivot ∈ c) with
    | false => rw [hp] at h; simp at h
    | true =>
      cases hrr : checkRAT db c pivot (hintLookup rhints) with
      | false => rw [hp, hrr] at h; simp at h
      | true => exact rat_step_sat db c pivot (hintLookup rhints) (of_decide_eq_true hp) hrr hsat

def runGen (db : Formula) : List PStep → Option Formula
  | [] => some db
  | s :: rest => if checkStep db s then runGen (db ++ [stepClause s]) rest else none

theorem runGen_cons (db : Formula) (s : PStep) (rest : List PStep) :
    runGen db (s :: rest) =
      (if checkStep db s then runGen (db ++ [stepClause s]) rest else none) := rfl

theorem runGen_sat (steps : List PStep) :
    ∀ db g, Sat db → runGen db steps = some g → Sat g := by
  induction steps with
  | nil => intro db g hsat hrun; rw [runGen] at hrun; injection hrun with h; subst h; exact hsat
  | cons s rest ih =>
    intro db g hsat hrun
    rw [runGen_cons] at hrun
    cases hc : checkStep db s with
    | false => rw [hc, if_neg (by simp)] at hrun; simp at hrun
    | true =>
      rw [hc, if_pos (by simp)] at hrun
      exact ih (db ++ [stepClause s]) g (checkStep_sat db s hsat hc) hrun

/-- The general checker: run mixed RUP/RAT steps, succeed iff the empty clause is derived. -/
def checkProofGen (f : Formula) (steps : List PStep) : Bool :=
  match runGen f steps with
  | some g => decide ([] ∈ g)
  | none => false

/-- SOUNDNESS of the general RUP+RAT checker. -/
theorem checkProofGen_unsat (f : Formula) (steps : List PStep)
    (h : checkProofGen f steps = true) : Unsat f := by
  cases hg : runGen f steps with
  | none => simp [checkProofGen, hg] at h
  | some g =>
    simp only [checkProofGen, hg] at h
    exact unsat_of_sat_preserved f g (fun hs => runGen_sat steps f g hs hg) (of_decide_eq_true h)

#check @rat_add_sat
#check @checkProofGen_unsat
#print axioms rat_add_sat
#print axioms checkProofGen_unsat
#print axioms ratDemo_sat
