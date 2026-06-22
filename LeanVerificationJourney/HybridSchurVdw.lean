import LeanVerificationJourney.Lrat

/-
  HybridSchurVdw.lean
  ----------------------------------------------------------------------------
  A finite hybrid Schur / van der Waerden specification for the new Barrier
  Atlas result:

    no 3-coloring of [1..13] avoids both monochromatic Schur triples x+y=z
    and monochromatic 3-term arithmetic progressions.

  This file defines the finite claim, checks the [1..12] lower witness, builds
  the exact CNF encoder whose output is bound to the certificate, and proves the
  one-way semantic bridge from a hybrid-avoiding coloring to a satisfying CNF
  assignment. The UNSAT certificate replay lives in HybridSchurVdw13Data.lean.
-/

/-- The points `[1, ..., n]`, in increasing order. -/
def hybridPoints (n : Nat) : List Nat :=
  (List.range n).map (fun i => i + 1)

/-- Point-major, zero-based colors, one-based DIMACS variables. -/
def hybridVar (point color colors : Nat) : Nat :=
  (point - 1) * colors + color + 1

def hybridPos (v : Nat) : Lit := ⟨v, false⟩
def hybridNeg (v : Nat) : Lit := ⟨v, true⟩

/-- Schur triples are listed with `x <= y`, matching the Barrier Atlas encoder. -/
def hybridIsSchurTriple (x y z : Nat) : Bool :=
  x <= y && x + y == z

/-- Three-term arithmetic progressions `(a, a+d, a+2d)`, with `d > 0`. -/
def hybridIsAPTriple (a b c : Nat) : Bool :=
  a < b && b < c && b - a == c - b

/-- The deduplicated hybrid obstruction set, in lexicographic order. -/
def hybridTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (hybridPoints n).flatMap (fun a =>
    (hybridPoints n).flatMap (fun b =>
      (hybridPoints n).flatMap (fun c =>
        if hybridIsSchurTriple a b c || hybridIsAPTriple a b c then
          [(a, b, c)]
        else
          [])))

/-- Read a 1-based point's color from a concrete finite witness. -/
def hybridWitnessColor (w : List Nat) (point : Nat) : Nat :=
  w.getD (point - 1) 0

/-- Decode a finite coloring from a base-`colors` code. Point 1 is the low digit. -/
def hybridCodeColor (code colors point : Nat) : Nat :=
  (code / (colors ^ (point - 1))) % colors

/-- The length-`n` coloring encoded by a natural-number code. -/
def hybridColoringOfCode (n colors code : Nat) : List Nat :=
  (hybridPoints n).map (fun point => hybridCodeColor code colors point)

/-- Convert a finite coloring into a SAT assignment for the point-major encoder. -/
def hybridAssignmentOfColoring (w : List Nat) (colors : Nat) : Assign :=
  fun v =>
    if colors == 0 then
      false
    else
      hybridWitnessColor w (((v - 1) / colors) + 1) == ((v - 1) % colors)

theorem hybridAssignment_var (w : List Nat) (point color colors : Nat)
    (hpoint : 1 <= point) (hcolors : 0 < colors) (hcolor : color < colors) :
    hybridAssignmentOfColoring w colors (hybridVar point color colors) =
      (hybridWitnessColor w point == color) := by
  unfold hybridAssignmentOfColoring hybridVar
  simp [Nat.ne_of_gt hcolors]
  have hdiv : ((point - 1) * colors + color) / colors = point - 1 := by
    rw [Nat.mul_comm (point - 1) colors]
    rw [Nat.mul_add_div hcolors]
    rw [Nat.div_eq_of_lt hcolor]
    simp
  rw [hdiv]
  rw [Nat.mod_eq_of_lt hcolor]
  have hpoint' : point - 1 + 1 = point := by omega
  rw [hpoint']

/-- A concrete coloring avoids every hybrid obstruction in `[1..n]`. -/
abbrev HybridAvoids (w : List Nat) (n colors : Nat) : Prop :=
  w.length = n ∧
  (∀ color ∈ w, color < colors) ∧
  ∀ t ∈ hybridTriples n,
    ¬ (hybridWitnessColor w t.1 = hybridWitnessColor w t.2.1 ∧
       hybridWitnessColor w t.2.1 = hybridWitnessColor w t.2.2)

/-- Membership in the generated point interval gives the expected bounds. -/
theorem hybridPoints_mem_bounds {n point : Nat} (hp : point ∈ hybridPoints n) :
    1 <= point ∧ point <= n := by
  unfold hybridPoints at hp
  rcases List.mem_map.mp hp with ⟨i, hi, hpoint⟩
  have hi_lt : i < n := List.mem_range.mp hi
  omega

/-- `getD` agrees with indexed lookup inside the concrete witness length. -/
theorem hybridWitnessColor_eq_getElem (w : List Nat) (point : Nat)
    (hidx : point - 1 < w.length) :
    hybridWitnessColor w point = w[point - 1] := by
  unfold hybridWitnessColor
  unfold List.getD
  rw [List.getElem?_eq_getElem hidx]
  rfl

/-- A witness color at a generated point is itself in the allowed color range. -/
theorem hybridWitnessColor_lt_of_mem_points {w : List Nat} {n colors point : Nat}
    (hlen : w.length = n) (hcolors : ∀ color ∈ w, color < colors)
    (hp : point ∈ hybridPoints n) :
    hybridWitnessColor w point < colors := by
  have hb := hybridPoints_mem_bounds hp
  have hidx : point - 1 < w.length := by
    rw [hlen]
    omega
  have hmem : hybridWitnessColor w point ∈ w := by
    rw [hybridWitnessColor_eq_getElem w point hidx]
    exact List.getElem_mem hidx
  exact hcolors _ hmem

/-- Every generated obstruction triple uses generated points. -/
theorem hybridTriples_mem_points {n a b c : Nat} (ht : (a, b, c) ∈ hybridTriples n) :
    a ∈ hybridPoints n ∧ b ∈ hybridPoints n ∧ c ∈ hybridPoints n := by
  unfold hybridTriples at ht
  rcases List.mem_flatMap.mp ht with ⟨a0, ha0, hrest⟩
  rcases List.mem_flatMap.mp hrest with ⟨b0, hb0, hrest2⟩
  rcases List.mem_flatMap.mp hrest2 with ⟨c0, hc0, hif⟩
  by_cases hcond : hybridIsSchurTriple a0 b0 c0 || hybridIsAPTriple a0 b0 c0
  · simp [hcond] at hif
    rcases hif with ⟨haeq, hbeq, hceq⟩
    subst a
    subst b
    subst c
    exact ⟨ha0, hb0, hc0⟩
  · simp [hcond] at hif

/-- Barrier Atlas's tight lower witness: [1..12] is still colorable. -/
def hybridWitness12 : List Nat :=
  [0, 1, 0, 2, 1, 2, 2, 0, 2, 0, 1, 1]

theorem hybridWitness12_valid : HybridAvoids hybridWitness12 12 3 := by
  decide

theorem hybrid12_exists_avoiding_coloring : ∃ w, HybridAvoids w 12 3 :=
  ⟨hybridWitness12, hybridWitness12_valid⟩

/-- At least one color is assigned to a point. -/
def hybridAtLeastOneClause (point colors : Nat) : Clause :=
  (List.range colors).map (fun color => hybridPos (hybridVar point color colors))

/-- At most one color is assigned to a point. -/
def hybridAtMostOneClauses (point colors : Nat) : Formula :=
  (List.range colors).flatMap (fun c1 =>
    (List.range colors).flatMap (fun c2 =>
      if c1 < c2 then
        [[hybridNeg (hybridVar point c1 colors), hybridNeg (hybridVar point c2 colors)]]
      else
        []))

/-- The exact-one color clauses for one point. -/
def hybridPointClauses (point colors : Nat) : Formula :=
  [hybridAtLeastOneClause point colors] ++ hybridAtMostOneClauses point colors

/-- The exact-one color clauses for all points. -/
def hybridColorClauses (n colors : Nat) : Formula :=
  (hybridPoints n).flatMap (fun point => hybridPointClauses point colors)

/-- Forbid one monochromatic hybrid obstruction in one color. -/
def hybridTripleClause (t : Nat × Nat × Nat) (color colors : Nat) : Clause :=
  [hybridNeg (hybridVar t.1 color colors),
   hybridNeg (hybridVar t.2.1 color colors),
   hybridNeg (hybridVar t.2.2 color colors)]

/-- All forbidden-monochromatic-obstruction clauses. -/
def hybridObstructionClauses (n colors : Nat) : Formula :=
  (hybridTriples n).flatMap (fun t =>
    (List.range colors).map (fun color => hybridTripleClause t color colors))

/-- The Barrier Atlas hybrid Schur/vdW CNF encoder. -/
def hybridSchurVdwCNF (n colors : Nat) : Formula :=
  hybridColorClauses n colors ++ hybridObstructionClauses n colors

theorem hybridTriples13_count : (hybridTriples 13).length = 74 := by
  native_decide

theorem hybrid13_cnf_clause_count : (hybridSchurVdwCNF 13 3).length = 274 := by
  native_decide

theorem hybrid13_last_variable : hybridVar 13 2 3 = 39 := by
  native_decide

theorem hybridWitness12_satisfies_cnf :
    formulaTrue (hybridAssignmentOfColoring hybridWitness12 3)
      (hybridSchurVdwCNF 12 3) = true := by
  native_decide

/--
Every hybrid-avoiding 3-coloring of `[1..13]` satisfies the exact CNF generated
above. This is the semantic bridge from the finite combinatorial specification
to the SAT certificate interface.
-/
theorem hybrid13_avoiding_satisfies_cnf (w : List Nat)
    (hw : HybridAvoids w 13 3) :
    formulaTrue (hybridAssignmentOfColoring w 3) (hybridSchurVdwCNF 13 3) = true := by
  rcases hw with ⟨hlen, hcolors, havoid⟩
  simp [formulaTrue, clauseTrue, litTrue, hybridSchurVdwCNF, hybridColorClauses,
    hybridPointClauses, hybridAtLeastOneClause, hybridAtMostOneClauses,
    hybridObstructionClauses, hybridTripleClause, hybridPos, hybridNeg]
  constructor
  · intro point hp
    have hpBounds := hybridPoints_mem_bounds hp
    constructor
    · have hactual : hybridWitnessColor w point < 3 :=
        hybridWitnessColor_lt_of_mem_points hlen hcolors hp
      refine ⟨hybridWitnessColor w point, hactual, ?_⟩
      rw [hybridAssignment_var w point (hybridWitnessColor w point) 3 hpBounds.1
        (by decide) hactual]
      simp
    · intro c1 hc1 c2 hc2 hlt
      have h1 := hybridAssignment_var w point c1 3 hpBounds.1 (by decide) hc1
      have h2 := hybridAssignment_var w point c2 3 hpBounds.1 (by decide) hc2
      rw [h1, h2]
      by_cases hactual1 : hybridWitnessColor w point = c1
      · right
        have hne : hybridWitnessColor w point ≠ c2 := by
          intro hactual2
          omega
        simp [hne]
      · left
        simp [hactual1]
  · intro a b c ht color hcolor
    have hpoints := hybridTriples_mem_points ht
    have haBounds := hybridPoints_mem_bounds hpoints.1
    have hbBounds := hybridPoints_mem_bounds hpoints.2.1
    have hcBounds := hybridPoints_mem_bounds hpoints.2.2
    have haAssign := hybridAssignment_var w a color 3 haBounds.1 (by decide) hcolor
    have hbAssign := hybridAssignment_var w b color 3 hbBounds.1 (by decide) hcolor
    have hcAssign := hybridAssignment_var w c color 3 hcBounds.1 (by decide) hcolor
    rw [haAssign, hbAssign, hcAssign]
    by_cases ha : hybridWitnessColor w a = color
    · by_cases hb : hybridWitnessColor w b = color
      · by_cases hc : hybridWitnessColor w c = color
        · have hmono : hybridWitnessColor w a = hybridWitnessColor w b ∧
              hybridWitnessColor w b = hybridWitnessColor w c := by
            constructor <;> omega
          exact False.elim ((havoid (a, b, c) ht) hmono)
        · simp [hc]
      · simp [hb]
    · simp [ha]
