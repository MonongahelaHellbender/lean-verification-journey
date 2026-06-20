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

  We enumerate ALL 2^5 = 32 two-colorings of the five numbers directly, in core
  Lean (no Mathlib): a coloring is a 5-bit code `0..31`, and the color of
  position `pos` is bit `pos` of the code. `decide` ranges over `List.range 32`
  — a bounded `∀`, which the kernel CAN evaluate — so the whole impossibility is
  checked by Lean's trusted kernel, not an external tool.
  (A `∀` over the function type `Fin 5 → Bool` is the mathematically natural
   phrasing, but core Lean cannot synthesize its `Decidable` instance without
   Mathlib's `Fintype` machinery; the bitmask encoding is the same 32 colorings,
   kept inside fast-building core Lean.)
  (Positions 0..4 correspond to numbers 1..5, so the triple a+b=c in numbers
   becomes an index triple, e.g. 1+1=2 → (0,0,1), 2+3=5 → (1,2,4).)
-/
/-- The color (`Bool`) of position `pos` under the coloring encoded by 5-bit `code`. -/
def colorAt (code pos : Nat) : Bool := (code >>> pos) % 2 == 1

/-- The Schur triples among numbers 1..5, as 0-based position indices. -/
def schurTriples5 : List (Nat × Nat × Nat) :=
  [(0, 0, 1), (0, 1, 2), (0, 2, 3), (0, 3, 4), (1, 1, 3), (1, 2, 4)]

theorem S2_upper_bound :
    ∀ code ∈ List.range 32, ∃ t ∈ schurTriples5,
      colorAt code t.1 = colorAt code t.2.1 ∧ colorAt code t.2.1 = colorAt code t.2.2 := by
  decide

#check @S2_upper_bound


/-
  ────────────────────────────────────────────────────────────────────────────
  Lemma #5 — W(2,3) ≤ 9   (the impossibility direction for van der Waerden)
  ----------------------------------------------------------------------------
  Mirror of Lemma #4, for arithmetic progressions instead of sums. Every one of
  the 2^9 = 512 two-colorings of {1,…,9} contains a monochromatic 3-term
  progression. Together with Lemma #3 (W(2,3) ≥ 9) this pins **W(2,3) = 9**.

  Same bitmask trick (positions 0..8 are the 9 low bits of `code`), and instead
  of a hand-listed triple set we let the kernel range over every start `p` and
  gap `d` with `p + 2d ≤ 8` — so there is no "did we list all progressions?" gap.

  (`set_option maxRecDepth` only raises the elaborator's recursion limit so the
  512-element search fits; it does NOT touch the kernel or the trusted base —
  the proof is still checked the same way.)
-/
set_option maxRecDepth 10000 in
theorem W23_upper_bound :
    ∀ code ∈ List.range 512,
      ∃ p ∈ List.range 9, ∃ d ∈ List.range 9,
        1 ≤ d ∧ p + 2 * d ≤ 8 ∧
        colorAt code p = colorAt code (p + d) ∧
        colorAt code (p + d) = colorAt code (p + 2 * d) := by
  decide

#check @W23_upper_bound


/-
  ────────────────────────────────────────────────────────────────────────────
  THE TRUSTED BASE, made explicit
  ----------------------------------------------------------------------------
  This is the whole point of the exercise, so let's prove it rather than assert
  it. `#print axioms` lists every axiom a theorem depends on. A proof built only
  from `decide` rests on nothing but the kernel's own computation — so the list
  is EMPTY ("does not depend on any axioms"). Compare: any proof that reached for
  classical logic would show `Classical.choice`, `propext`, `Quot.sound` here.

  So the trusted base for "S(2) = 4" is: Lean's kernel, and the few lines of
  encoding above that you can read in one sitting. Nothing else.
-/
/-
  ────────────────────────────────────────────────────────────────────────────
  Lemma #6 — S(3) ≤ 13   (completing the pinning of S(3) = 13)
  ----------------------------------------------------------------------------
  Lemma #2 showed S(3) ≥ 13: an explicit 3-coloring of {1,...,13} that works.
  This proves the other half — S(3) ≤ 13 — by showing that every 3-coloring
  of {1,...,14} FAILS (contains a monochromatic a + b = c with a,b,c ∈ {1..14}).
  Together, they pin **S(3) = 13** exactly.

  The challenge: 3^14 = 4,782,969 colorings to rule out. That's too many for
  kernel `decide` (which would run for hours in the kernel), but `native_decide`
  compiles the check to native machine code and runs it in seconds.

  THIS IS THE FIRST PLACE WE USE `native_decide` — and that's a deliberate,
  documented step in the trusted-base story. See CONCEPTS.md for the tradeoff.
-/

/-- Color of number `i` (1-based) under a 3-coloring encoded as a base-3 integer.
    The color of number i is the i-th "digit" of `code` in base 3. -/
def colorAt3 (code i : Nat) : Nat :=
  (code / (3 ^ (i - 1))) % 3

/-- All Schur triples (a, b, c) with a+b=c inside {1,...,14}. -/
def schurTriples14 : List (Nat × Nat × Nat) :=
  (List.range 14).flatMap fun i =>
    (List.range 14).flatMap fun j =>
      let a := i + 1; let b := j + 1; let c := a + b
      if c ≤ 14 then [(a, b, c)] else []

/-- S(3) ≤ 13: every 3-coloring of {1,...,14} has a monochromatic Schur triple.
    3^14 = 4,782,969 colorings — `native_decide` compiles this to machine code.
    The proof still holds; what changes is which part of the system we trust:
    now the Lean *compiler*, not only the kernel. See CONCEPTS.md. -/
theorem S3_upper_bound :
    ∀ code ∈ List.range (3 ^ 14),
      ∃ t ∈ schurTriples14,
        colorAt3 code t.1 = colorAt3 code t.2.1 ∧
        colorAt3 code t.2.1 = colorAt3 code t.2.2 := by
  native_decide

#check @S3_upper_bound


/-
  ────────────────────────────────────────────────────────────────────────────
  THE TRUSTED BASE, made explicit
  ----------------------------------------------------------------------------
  This is the whole point of the exercise, so let's prove it rather than assert
  it. `#print axioms` lists every axiom a theorem depends on. A proof built only
  from `decide` rests on nothing but the kernel's own computation — so the list
  is EMPTY ("does not depend on any axioms"). Compare: any proof that reached for
  classical logic would show `Classical.choice`, `propext`, `Quot.sound` here.

  For `native_decide`, the axioms list shows `Lean.ofReduceBool` — the one extra
  axiom that says "if the compiled native check returned true, trust it." That's
  the honest cost of the speed. Everything else in the chain is still kernel-checked.

  So the trusted base for "S(2) = 4" is: Lean's kernel + the few lines of encoding.
  For "S(3) = 13" (upper bound): add the Lean compiler and `Lean.ofReduceBool`.
  Both are explicit, both are inspectable.
-/
#print axioms coloring_is_sum_free
#print axioms S2_upper_bound
#print axioms W23_upper_bound
#print axioms S3_upper_bound
