import LeanVerificationJourney.Lrat

/-
  LratArray.lean — the Array-backed checker, for the TOP of the ladder.
  ----------------------------------------------------------------------------
  At small scale the List checker in `Lrat.lean` is fine, and at "embed the cert
  as a literal" scale the bottleneck was elaboration, not the checker (see
  `LratScale.lean`). But the TOP rung — reading a multi-hundred-thousand-step
  certificate from a FILE and checking it as a compiled program — is genuinely
  runtime-bound, and there the List database's O(n) append / O(i) index (=> O(n²))
  is fatal. So here the database is an `Array`: O(1) amortized push, O(1) index.

  Soundness is inherited, not re-derived: we prove the Array checker computes the
  SAME Bool as the List checker (`checkProofArr_eq`) and reuse `checkProof_unsat`.
  `checkProofArr_unsat` therefore rests on exactly `propext, Quot.sound`.
-/

def rupLoopArr (db : Array Clause) (trail : List Lit) : List Nat → Bool
  | [] => false
  | (i :: is) =>
    match db[i]? with
    | none => false
    | some d =>
      match unfalsified trail d with
      | [] => true
      | [u] => rupLoopArr db (u :: trail) is
      | _ => false

theorem rupLoopArr_cons (db : Array Clause) (trail : List Lit) (i : Nat) (is : List Nat) :
    rupLoopArr db trail (i :: is) =
      match db[i]? with
      | none => false
      | some d =>
        match unfalsified trail d with
        | [] => true
        | [u] => rupLoopArr db (u :: trail) is
        | _ => false := rfl

theorem rupLoopArr_eq (db : Array Clause) (trail : List Lit) (hints : List Nat) :
    rupLoopArr db trail hints = rupLoop db.toList trail hints := by
  induction hints generalizing trail with
  | nil => rfl
  | cons i is ih =>
    simp only [rupLoopArr_cons, rupLoop_cons, ih, Array.getElem?_toList]
    rfl

def checkRUPArr (db : Array Clause) (c : Clause) (hints : List Nat) : Bool :=
  rupLoopArr db (c.map Lit.flip) hints

theorem checkRUPArr_eq (db : Array Clause) (c : Clause) (hints : List Nat) :
    checkRUPArr db c hints = checkRUP db.toList c hints :=
  rupLoopArr_eq db (c.map Lit.flip) hints

def runStepsArr (db : Array Clause) : List Step → Option (Array Clause)
  | [] => some db
  | (s :: ss) =>
    match checkRUPArr db s.clause s.hints with
    | true => runStepsArr (db.push s.clause) ss
    | false => none

theorem runStepsArr_cons (db : Array Clause) (s : Step) (ss : List Step) :
    runStepsArr db (s :: ss) =
      match checkRUPArr db s.clause s.hints with
      | true => runStepsArr (db.push s.clause) ss
      | false => none := rfl

theorem runStepsArr_eq (db : Array Clause) (steps : List Step) :
    (runStepsArr db steps).map Array.toList = runSteps db.toList steps := by
  induction steps generalizing db with
  | nil => rfl
  | cons s ss ih =>
    rw [runStepsArr_cons, runSteps_cons, checkRUPArr_eq]
    cases checkRUP db.toList s.clause s.hints with
    | false => rfl
    | true =>
      rw [ih (db.push s.clause)]
      rw [show (db.push s.clause).toList = db.toList ++ [s.clause] from by simp]

def checkProofArr (f : List Clause) (steps : List Step) : Bool :=
  match runStepsArr f.toArray steps with
  | some db => decide ([] ∈ db.toList)
  | none => false

theorem checkProofArr_eq (f : List Clause) (steps : List Step) :
    checkProofArr f steps = checkProof f steps := by
  have h : (runStepsArr f.toArray steps).map Array.toList = runSteps f steps := by
    have e := runStepsArr_eq f.toArray steps
    rwa [List.toList_toArray] at e
  unfold checkProofArr checkProof
  cases hA : runStepsArr f.toArray steps with
  | none => simp only [hA, Option.map_none] at h; rw [← h]
  | some db => simp only [hA, Option.map_some] at h; rw [← h]

/-- SOUNDNESS for the fast checker — inherited from the List checker. -/
theorem checkProofArr_unsat (f : List Clause) (steps : List Step)
    (h : checkProofArr f steps = true) : Unsat f :=
  checkProof_unsat f steps (by rw [← checkProofArr_eq]; exact h)

#check @checkProofArr_unsat
#print axioms checkProofArr_unsat
