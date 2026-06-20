/-
  A verified RUP refutation checker — core Lean 4, no Mathlib.

  Goal: prove a checker SOUND once (by induction), then certify any concrete
  UNSAT instance by pure Bool computation feeding that one theorem.
-/

/-- A literal: a variable index plus whether it is negated. Using a structure
    (not a signed Int) makes negation a clean involution with no `0` edge case. -/
structure Lit where
  var : Nat
  neg : Bool
deriving DecidableEq

/-- Negate a literal: flip its polarity. -/
def Lit.flip (l : Lit) : Lit := { l with neg := !l.neg }

abbrev Clause := List Lit
abbrev Formula := List Clause
abbrev Assign := Nat → Bool

/-- Is literal `l` true under assignment `a`? -/
def litTrue (a : Assign) (l : Lit) : Bool :=
  if l.neg then !(a l.var) else a l.var

/-- Negation really is negation of truth — unconditionally (no `0` case). -/
theorem litTrue_flip (a : Assign) (l : Lit) :
    litTrue a l.flip = !(litTrue a l) := by
  cases l with
  | mk v n => cases n <;> simp [litTrue, Lit.flip]

/-- A clause is true if some literal in it is true. -/
def clauseTrue (a : Assign) (c : Clause) : Bool := c.any (litTrue a)

/-- A formula is true if every clause is true. -/
def formulaTrue (a : Assign) (f : Formula) : Bool := f.all (clauseTrue a)

/-- `f` is unsatisfiable: no assignment makes it true. -/
def Unsat (f : Formula) : Prop := ∀ a, formulaTrue a f = false

/-- A literal is falsified by the trail when its negation is on the trail
    (i.e. the trail has committed to the opposite). Decidable membership keeps
    this computable for concrete certificates. -/
def falsifiedBy (trail : List Lit) (l : Lit) : Bool :=
  decide (l.flip ∈ trail)

/-- The literals of `d` not yet falsified by the trail. -/
def unfalsified (trail : List Lit) (d : Clause) : List Lit :=
  d.filter (fun l => !falsifiedBy trail l)

/-- The RUP loop: walk the hint clauses. Each must be unit (exactly one
    unfalsified literal) under the current trail — propagate it — until some
    hint clause is fully falsified (a conflict), which completes the refutation. -/
def rupLoop (f : Formula) (trail : List Lit) : List Nat → Bool
  | [] => false                              -- ran out of hints, no conflict
  | (i :: is) =>
    match f[i]? with
    | none => false                          -- bad hint index
    | some d =>
      match unfalsified trail d with
      | [] => true                           -- conflict: refutation complete
      | [u] => rupLoop f (u :: trail) is     -- unit: propagate u
      | _ => false                           -- not unit: malformed hint

/-- To refute clause `c`: assume it false (put the negation of each of its
    literals on the trail), then run the RUP loop. -/
def checkRUP (f : Formula) (c : Clause) (hints : List Nat) : Bool :=
  rupLoop f (c.map Lit.flip) hints

/-- One-step unfolding of `rupLoop` on a `cons` of hints. Used as a *plain*
    rewrite (its recursive call has a variable list argument, so rewriting it
    never loops). -/
theorem rupLoop_cons (f : Formula) (trail : List Lit) (i : Nat) (is : List Nat) :
    rupLoop f trail (i :: is) =
      match f[i]? with
      | none => false
      | some d =>
        match unfalsified trail d with
        | [] => true
        | [u] => rupLoop f (u :: trail) is
        | _ => false := rfl

/-- THE HEART. If the loop succeeds from a trail every literal of which is true
    under some `a ⊨ f`, we reach a contradiction. (Used with the trail that
    encodes "a falsifies c".) -/
theorem rupLoop_contra (f : Formula) (a : Assign)
    (haf : formulaTrue a f = true) :
    ∀ (hints : List Nat) (trail : List Lit),
      (∀ l, l ∈ trail → litTrue a l = true) →
      rupLoop f trail hints = true → False := by
  intro hints
  induction hints with
  | nil => intro trail _ hloop; simp [rupLoop] at hloop
  | cons i is ih =>
    intro trail htrail hloop
    -- a ⊨ f means every clause of f is true under a
    have hall : ∀ d, d ∈ f → clauseTrue a d = true := by
      intro d hd
      have := List.all_eq_true.mp haf d hd
      simpa using this
    -- keep `hloop` in original form; reduce it one step at each leaf
    cases hget : f[i]? with
    | none =>
      simp [rupLoop_cons, hget] at hloop
    | some d =>
      have hdf : d ∈ f := List.mem_of_getElem? hget
      have hdtrue : clauseTrue a d = true := hall d hdf
      -- some literal of d is true under a
      obtain ⟨lt, hlt_mem, hlt_true⟩ := List.any_eq_true.mp hdtrue
      -- that literal cannot be falsified by the trail
      have hlt_not_fals : falsifiedBy trail lt = false := by
        cases h : falsifiedBy trail lt with
        | false => rfl
        | true =>
          exfalso
          have h' : decide (lt.flip ∈ trail) = true := h
          have hmem : lt.flip ∈ trail := of_decide_eq_true h'
          have h2 : litTrue a lt.flip = true := htrail lt.flip hmem
          rw [litTrue_flip, hlt_true] at h2
          simp at h2
      -- so lt is among the unfalsified literals of d
      have hlt_unf : lt ∈ unfalsified trail d := by
        unfold unfalsified
        rw [List.mem_filter]
        exact ⟨hlt_mem, by rw [hlt_not_fals]; rfl⟩
      -- case on the unit-check result
      cases hunf : unfalsified trail d with
      | nil =>
        -- conflict claimed, but lt sits in the (now empty) unfalsified set
        rw [hunf] at hlt_unf; simp at hlt_unf
      | cons u rest =>
        cases hrest : rest with
        | nil =>
          -- exactly one unfalsified literal u; it must equal lt, so u is true
          have hunf' : unfalsified trail d = [u] := by rw [hunf, hrest]
          have hlt_eq : lt = u := by
            rw [hunf'] at hlt_unf; simpa using hlt_unf
          simp only [rupLoop_cons, hget, hunf'] at hloop
          -- now `hloop : rupLoop f (u :: trail) is = true`
          exact ih (u :: trail)
            (by
              intro l hl
              rcases List.mem_cons.mp hl with h | h
              · rw [h, ← hlt_eq]; exact hlt_true
              · exact htrail l h)
            hloop
        | cons u2 rest2 =>
          -- two or more unfalsified literals: loop returns false
          have hunf' : unfalsified trail d = u :: u2 :: rest2 := by rw [hunf, hrest]
          simp [rupLoop_cons, hget, hunf'] at hloop

/-- SOUNDNESS: if `checkRUP f c hints` succeeds, every model of `f` satisfies `c`. -/
theorem rup_sound (f : Formula) (c : Clause) (hints : List Nat)
    (h : checkRUP f c hints = true) :
    ∀ a, formulaTrue a f = true → clauseTrue a c = true := by
  intro a haf
  cases hcc : clauseTrue a c with
  | true => rfl
  | false =>
    exfalso
    -- a falsifies c, so every negated literal of c is true under a
    have htrail : ∀ l, l ∈ c.map Lit.flip → litTrue a l = true := by
      intro l hl
      obtain ⟨l0, hl0_mem, hl0_eq⟩ := List.mem_map.mp hl
      -- l0 ∈ c, and clauseTrue a c = false means litTrue a l0 = false
      have hl0_false : litTrue a l0 = false := by
        cases hl0 : litTrue a l0 with
        | false => rfl
        | true =>
          exfalso
          have : clauseTrue a c = true := by
            simp only [clauseTrue]
            exact List.any_eq_true.mpr ⟨l0, hl0_mem, hl0⟩
          rw [hcc] at this; simp at this
      rw [← hl0_eq, litTrue_flip, hl0_false]; rfl
    exact rupLoop_contra f a haf hints (c.map Lit.flip) htrail h

/-- The headline form: a successful empty-clause refutation proves UNSAT. -/
theorem rup_unsat (f : Formula) (hints : List Nat)
    (h : checkRUP f [] hints = true) : Unsat f := by
  intro a
  cases hf : formulaTrue a f with
  | false => rfl
  | true =>
    have := rup_sound f [] hints h a hf
    simp [clauseTrue] at this

/-
  ────────────────────────────────────────────────────────────────────────────
  DEMO: certify a tiny UNSAT instance THROUGH the verified checker.

  F = { (x1), (¬x1 ∨ x2), (¬x2) }   — a unit-propagation chain to a conflict.
  The certificate is the hint list [0,1,2]; `by decide` checks the Bool, and
  the once-proved `rup_unsat` turns it into a real `Unsat F`.
-/
def x (n : Nat) : Lit := ⟨n, false⟩
def nx (n : Nat) : Lit := ⟨n, true⟩

def demoF : Formula := [[x 1], [nx 1, x 2], [nx 2]]

theorem demoF_unsat : Unsat demoF :=
  rup_unsat demoF [0, 1, 2] (by decide)

#check @rup_sound
#check @rup_unsat
#check @demoF_unsat
#print axioms demoF_unsat


/-
  ════════════════════════════════════════════════════════════════════════════
  BITE 2 — a growing clause database (real LRAT shape)

  A real LRAT proof doesn't refute in one shot; it *learns* clauses one at a
  time, each justified by a RUP check against everything derived so far, until
  it learns the empty clause. We model that: a `Step` adds one clause with its
  hints; `runSteps` appends accepted clauses to the database (so hint indices
  stay stable); success = the empty clause made it into the database.

  The soundness invariant: every model of the ORIGINAL formula satisfies every
  clause in the database. Learning a RUP-entailed clause preserves it (by
  `rup_sound`). If `[]` ever enters the database, the original formula has no
  model — UNSAT.
-/

/-- One LRAT proof step: the clause to add, and the hint clause-indices that
    witness it is RUP-entailed by the current database. -/
structure Step where
  clause : Clause
  hints : List Nat

/-- Run the proof, growing the database. Each accepted clause is appended at the
    end so earlier indices never shift. -/
def runSteps (db : Formula) : List Step → Option Formula
  | [] => some db
  | (s :: ss) =>
    match checkRUP db s.clause s.hints with
    | true => runSteps (db ++ [s.clause]) ss
    | false => none

theorem runSteps_cons (db : Formula) (s : Step) (ss : List Step) :
    runSteps db (s :: ss) =
      match checkRUP db s.clause s.hints with
      | true => runSteps (db ++ [s.clause]) ss
      | false => none := rfl

/-- Appending one clause to the database conjoins its truth value. -/
theorem formulaTrue_snoc (a : Assign) (db : Formula) (c : Clause) :
    formulaTrue a (db ++ [c]) = (formulaTrue a db && clauseTrue a c) := by
  unfold formulaTrue
  rw [List.all_append]
  simp

/-- The database invariant is preserved across the whole run: if every model of
    `f` satisfies the starting database, it satisfies the final one. -/
theorem runSteps_preserves (f : Formula) :
    ∀ (steps : List Step) (db db' : Formula),
      (∀ a, formulaTrue a f = true → formulaTrue a db = true) →
      runSteps db steps = some db' →
      ∀ a, formulaTrue a f = true → formulaTrue a db' = true := by
  intro steps
  induction steps with
  | nil =>
    intro db db' hdb hrun
    rw [runSteps] at hrun
    have heq : db = db' := Option.some.inj hrun
    subst heq; exact hdb
  | cons s ss ih =>
    intro db db' hdb hrun
    cases hc : checkRUP db s.clause s.hints with
    | false => simp [runSteps_cons, hc] at hrun
    | true =>
      simp only [runSteps_cons, hc] at hrun
      refine ih (db ++ [s.clause]) db' ?_ hrun
      intro a haf
      have hdbtrue := hdb a haf
      have hcl := rup_sound db s.clause s.hints hc a hdbtrue
      simp [formulaTrue_snoc, hdbtrue, hcl]

/-- The proof checker: run the steps, succeed iff the empty clause was learned. -/
def checkProof (f : Formula) (steps : List Step) : Bool :=
  match runSteps f steps with
  | some db => decide ([] ∈ db)
  | none => false

/-- SOUNDNESS (database version): a successful proof certifies UNSAT. -/
theorem checkProof_unsat (f : Formula) (steps : List Step)
    (h : checkProof f steps = true) : Unsat f := by
  cases hrun : runSteps f steps with
  | none => simp [checkProof, hrun] at h
  | some db =>
    have hempty : [] ∈ db := by
      have hcp : checkProof f steps = decide ([] ∈ db) := by simp [checkProof, hrun]
      rw [hcp] at h; exact of_decide_eq_true h
    have hpres : ∀ a, formulaTrue a f = true → formulaTrue a db = true :=
      runSteps_preserves f steps f db (fun _ haf => haf) hrun
    intro a
    cases hf : formulaTrue a f with
    | false => rfl
    | true =>
      exfalso
      have hdbtrue := hpres a hf
      have hcl : clauseTrue a [] = true := by
        have := List.all_eq_true.mp hdbtrue [] hempty
        simpa using this
      simp [clauseTrue] at hcl

/-
  ────────────────────────────────────────────────────────────────────────────
  DEMO 2: the canonical 2-variable UNSAT — which bite 1 could NOT do.

  F = { x1∨x2, x1∨¬x2, ¬x1∨x2, ¬x1∨¬x2 }   (no unit clause to start from)

  A real 2-step LRAT-shaped proof:
    step 1: learn (x1)  [from clauses 0,1]   — index 4
    step 2: learn ()    [from clauses 4,2,3] — the empty clause ⇒ UNSAT
-/
def demoG : Formula :=
  [[x 1, x 2], [x 1, nx 2], [nx 1, x 2], [nx 1, nx 2]]

def demoGProof : List Step :=
  [ { clause := [x 1], hints := [0, 1] },
    { clause := [],     hints := [4, 2, 3] } ]

theorem demoG_unsat : Unsat demoG :=
  checkProof_unsat demoG demoGProof (by decide)

#check @checkProof_unsat
#check @demoG_unsat
#print axioms demoG_unsat


/-
  REAL certificate (NOT hand-written): Schur {1..5}, k=2.
  CNF (22 clauses) -> glucose -> DRAT -> drat-trim -L -> LRAT (s VERIFIED)
  -> parser (remap IDs, drop deletions, dedup literals) -> Step list,
  kernel-checked by the verified `checkProof`.
  UNSAT == {1..5} not 2-colorable sum-free == S(2) <= 4 (pairs with Lemma 4).
-/
def schur5F : Formula :=
  [ [x 1, x 2]
  , [nx 1, nx 2]
  , [x 3, x 4]
  , [nx 3, nx 4]
  , [x 5, x 6]
  , [nx 5, nx 6]
  , [x 7, x 8]
  , [nx 7, nx 8]
  , [x 9, x 10]
  , [nx 9, nx 10]
  , [nx 1, nx 3]
  , [nx 2, nx 4]
  , [nx 1, nx 3, nx 5]
  , [nx 2, nx 4, nx 6]
  , [nx 1, nx 5, nx 7]
  , [nx 2, nx 6, nx 8]
  , [nx 1, nx 7, nx 9]
  , [nx 2, nx 8, nx 10]
  , [nx 3, nx 7]
  , [nx 4, nx 8]
  , [nx 3, nx 5, nx 9]
  , [nx 4, nx 6, nx 10] ]

def schur5Proof : List Step :=
  [ { clause := [nx 7, nx 9], hints := [18, 2, 11, 0, 16] }
  , { clause := [nx 9], hints := [22, 6, 19, 2, 10, 0, 20, 4, 15] }
  , { clause := [nx 2], hints := [23, 8, 11, 2, 17, 6, 18] }
  , { clause := [], hints := [23, 8, 24, 0, 10, 2, 21, 19, 4, 6, 14] } ]

theorem schur5_unsat : Unsat schur5F :=
  checkProof_unsat schur5F schur5Proof (by decide)

#check @schur5_unsat
#print axioms schur5_unsat

/-
  REAL certificate (NOT hand-written), bigger: van der Waerden W(2,3) <= 9.
  {1..9}, 2 colors, no monochromatic 3-term AP: CNF (50 clauses) -> glucose
  -> DRAT -> drat-trim -L -> LRAT (s VERIFIED) -> parser -> Step list,
  kernel-checked by the verified `checkProof`.
  UNSAT == W(2,3) <= 9 (pairs with Lemma 3); 10 real proof steps, not a toy.
-/
def vdw923F : Formula :=
  [ [x 1, x 2]
  , [nx 1, nx 2]
  , [x 3, x 4]
  , [nx 3, nx 4]
  , [x 5, x 6]
  , [nx 5, nx 6]
  , [x 7, x 8]
  , [nx 7, nx 8]
  , [x 9, x 10]
  , [nx 9, nx 10]
  , [x 11, x 12]
  , [nx 11, nx 12]
  , [x 13, x 14]
  , [nx 13, nx 14]
  , [x 15, x 16]
  , [nx 15, nx 16]
  , [x 17, x 18]
  , [nx 17, nx 18]
  , [nx 1, nx 3, nx 5]
  , [nx 2, nx 4, nx 6]
  , [nx 1, nx 5, nx 9]
  , [nx 2, nx 6, nx 10]
  , [nx 1, nx 7, nx 13]
  , [nx 2, nx 8, nx 14]
  , [nx 1, nx 9, nx 17]
  , [nx 2, nx 10, nx 18]
  , [nx 3, nx 5, nx 7]
  , [nx 4, nx 6, nx 8]
  , [nx 3, nx 7, nx 11]
  , [nx 4, nx 8, nx 12]
  , [nx 3, nx 9, nx 15]
  , [nx 4, nx 10, nx 16]
  , [nx 5, nx 7, nx 9]
  , [nx 6, nx 8, nx 10]
  , [nx 5, nx 9, nx 13]
  , [nx 6, nx 10, nx 14]
  , [nx 5, nx 11, nx 17]
  , [nx 6, nx 12, nx 18]
  , [nx 7, nx 9, nx 11]
  , [nx 8, nx 10, nx 12]
  , [nx 7, nx 11, nx 15]
  , [nx 8, nx 12, nx 16]
  , [nx 9, nx 11, nx 13]
  , [nx 10, nx 12, nx 14]
  , [nx 9, nx 13, nx 17]
  , [nx 10, nx 14, nx 18]
  , [nx 11, nx 13, nx 15]
  , [nx 12, nx 14, nx 16]
  , [nx 13, nx 15, nx 17]
  , [nx 14, nx 16, nx 18] ]

def vdw923Proof : List Step :=
  [ { clause := [nx 11, nx 15, nx 17], hints := [40, 36, 46, 6, 4, 12, 23, 33, 0, 8, 24] }
  , { clause := [nx 15, nx 17], hints := [50, 10, 48, 12, 43, 8, 24, 30, 0, 2, 23, 19, 6, 4, 32] }
  , { clause := [nx 5, nx 17], hints := [51, 14, 36, 10, 47, 12, 44, 8, 39, 31, 6, 2, 26] }
  , { clause := [nx 4, nx 17], hints := [51, 52, 14, 4, 31, 8, 24, 0, 19] }
  , { clause := [nx 9, nx 17], hints := [44, 12, 24, 0, 23, 6, 51, 14, 53, 2, 28, 10, 47] }
  , { clause := [nx 17], hints := [54, 8, 52, 4, 33, 6, 35, 12, 22, 0, 21] }
  , { clause := [nx 10], hints := [55, 16, 45, 12, 25, 0, 22, 6, 39, 10, 33, 4, 46, 14, 18, 2, 31] }
  , { clause := [nx 13], hints := [55, 16, 56, 8, 34, 4, 37, 10, 42] }
  , { clause := [nx 6], hints := [55, 16, 56, 8, 57, 12, 49, 14, 30, 2, 27, 6, 37, 40, 10] }
  , { clause := [], hints := [56, 8, 57, 12, 58, 4, 20, 32, 0, 6, 23] } ]

theorem vdw923_unsat : Unsat vdw923F :=
  checkProof_unsat vdw923F vdw923Proof (by decide)

#check @vdw923_unsat
#print axioms vdw923_unsat
