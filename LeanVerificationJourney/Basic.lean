/-
  Schur.lean — Portfolio piece #1
  ----------------------------------------------------------------------------
  Formalizing, in Lean 4, the S(2) ≥ 4 lower-bound witness from the
  `certified-combinatorics-verification` tool.

  In that tool, Python *self-verifies* an explicit 2-coloring of {1,2,3,4}:
  it has no monochromatic "Schur triple" a + b = c. Here we re-prove the same
  fact — but checked by **Lean's kernel**, a tiny, trusted proof engine. Same
  claim, a much smaller trusted base.

  Everything below uses only core Lean 4 (no Mathlib) so it builds fast.
-/

/-- A 2-coloring of the natural numbers. Each number gets a color (`Bool` = two
    colors). Numbers outside 1..4 get a default; we only ever ask about 1..4. -/
def coloring : Nat → Bool
  | 1 => false   -- color A
  | 2 => true    -- color B
  | 3 => true    -- color B
  | 4 => false   -- color A
  | _ => false

/-- Every Schur triple `a + b = c` inside [1,4], listed with `a ≤ b` so we don't
    double-count: 1+1=2, 1+2=3, 1+3=4, 2+2=4. -/
def schurTriples : List (Nat × Nat × Nat) :=
  [(1, 1, 2), (1, 2, 3), (1, 3, 4), (2, 2, 4)]

/-- A triple `(a, b, c)` is *monochromatic* under `f` when all three share a color.
    (`abbrev` instead of `def` so Lean can automatically see this is decidable.) -/
abbrev Monochromatic (f : Nat → Bool) (t : Nat × Nat × Nat) : Prop :=
  f t.1 = f t.2.1 ∧ f t.2.1 = f t.2.2

/-- THE THEOREM: no Schur triple in our list is monochromatic under `coloring`.
    `decide` asks Lean's kernel to check every case — a real machine-checked proof.
    This is the Lean version of verify.py's "lower bound self-verifies: True". -/
theorem coloring_is_sum_free :
    ∀ t ∈ schurTriples, ¬ Monochromatic coloring t := by
  decide

/-
  TRY IT YOURSELF (this is how you learn what the proof actually says):
  Change `coloring` so that `3 => false` instead of `true`. Now 1+3=4 would be
  colored (A, A, A) = monochromatic, so the theorem becomes FALSE — and `decide`
  will refuse to prove it, with an error. Watching it fail teaches you that the
  proof is checking something real, not rubber-stamping. Then change it back.
-/
#check @coloring_is_sum_free


/-
  ────────────────────────────────────────────────────────────────────────────
  Lemma #2 — S(3) ≥ 13
  ----------------------------------------------------------------------------
  Now THREE colors, all the way to 13: an explicit 3-coloring of {1,...,13} with
  no monochromatic a + b = c. (Colors are 0, 1, 2.)

  A classic sum-free partition of 1..13:
    color 0: {1, 4, 10, 13}
    color 1: {2, 3, 11, 12}
    color 2: {5, 6, 7, 8, 9}
-/
def coloring3 : Nat → Nat
  | 1 => 0
  | 4 => 0
  | 10 => 0
  | 13 => 0
  | 2 => 1
  | 3 => 1
  | 11 => 1
  | 12 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | _ => 0

/-- No monochromatic Schur triple. NOTE the upgrade in *style*: instead of listing
    the triples by hand (like Lemma #1), we check EVERY pair `a, b` in 1..13 with
    `a + b ≤ 13`, and let `c` be `a + b`. That removes any "did we list all the
    triples?" gap — the kernel checks them all. -/
theorem coloring3_is_sum_free :
    ∀ a ∈ List.range 14, ∀ b ∈ List.range 14,
      1 ≤ a → 1 ≤ b → a + b ≤ 13 →
      ¬ (coloring3 a = coloring3 b ∧ coloring3 b = coloring3 (a + b)) := by
  decide

#check @coloring3_is_sum_free


/-
  ────────────────────────────────────────────────────────────────────────────
  Lemma #3 — W(2,3) ≥ 9   (van der Waerden, a DIFFERENT structure)
  ----------------------------------------------------------------------------
  Schur was about sums (a + b = c). Van der Waerden is about *arithmetic
  progressions*: three equally-spaced numbers a, a+d, a+2d. W(2,3) = 9 means you
  can 2-color {1,...,8} with no monochromatic 3-term progression, but not {1,...,9}.

  The witness: the repeating pattern color color, other other  (RRBB RRBB):
    color 0 (R): 1, 2, 5, 6      color 1 (B): 3, 4, 7, 8

  The point of this lemma: the *mathematical object* changed (progressions, not
  sums), but the *verification pattern* is identical — define the coloring, define
  the bad structure, and check ALL cases by construction. The pattern generalizes.
-/
def vdwColoring : Nat → Bool
  | 1 => false
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => false
  | 6 => false
  | 7 => true
  | 8 => true
  | _ => false

/-- No monochromatic 3-term arithmetic progression `(a, a+d, a+2d)` in {1,…,8}.
    Same "check every case" style as Lemma #2 — now over all starts `a` and gaps `d`. -/
theorem vdwColoring_no_mono_3AP :
    ∀ a ∈ List.range 9, ∀ d ∈ List.range 9,
      1 ≤ a → 1 ≤ d → a + 2 * d ≤ 8 →
      ¬ (vdwColoring a = vdwColoring (a + d) ∧ vdwColoring (a + d) = vdwColoring (a + 2 * d)) := by
  decide

#check @vdwColoring_no_mono_3AP


/-
  ────────────────────────────────────────────────────────────────────────────
  Lemma #4 — S(2) ≤ 4   (the OTHER direction — and the deeper idea)
  ----------------------------------------------------------------------------
  Lemmas 1–3 EXHIBITED a good coloring: "there EXISTS a coloring that works."
  That's the easy kind of claim — show one example.

  This proves the opposite, harder kind: a UNIVERSAL IMPOSSIBILITY — *every*
  2-coloring of {1,...,5} FAILS (contains a monochromatic a + b = c). You can't
  prove that with one example; you must rule out ALL of them.

  Together with Lemma #1 (S(2) ≥ 4), this pins **S(2) = 4** exactly.

  HOW WE ENUMERATE: we encode a 2-coloring of {1,2,3,4,5} as a natural number
  0–31: bit i (= `Nat.testBit n i`) is the color of number i+1. The 32 possible
  values of n are exactly the 32 possible 2-colorings. `List.range 32` gives them
  all; `decide` checks every one.

  The Schur triples in {1..5} (0-indexed):
    1+1=2 → bits (0,0,1)   1+2=3 → (0,1,2)   1+3=4 → (0,2,3)
    1+4=5 → (0,3,4)        2+2=4 → (1,1,3)   2+3=5 → (1,2,4)
-/
def schurTriples5 : List (Nat × Nat × Nat) :=
  [(0, 0, 1), (0, 1, 2), (0, 2, 3), (0, 3, 4), (1, 1, 3), (1, 2, 4)]

theorem S2_upper_bound :
    ∀ n ∈ List.range 32,
      ∃ t ∈ schurTriples5,
        Nat.testBit n t.1 = Nat.testBit n t.2.1 ∧
        Nat.testBit n t.2.1 = Nat.testBit n t.2.2 := by
  decide

#check @S2_upper_bound
