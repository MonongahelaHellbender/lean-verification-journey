# Lean verification journey

Learning **Lean 4** by formalizing real certified-computation results — in public, one lemma at a time.

The thesis: as AI gets better at *generating* math and code, the scarce, durable skill is *verifying*
it. Lean is where that happens at the frontier (AlphaProof, Harmonic, formal-methods-for-AI). This repo
is me building that skill the honest way — by re-proving results I've already certified by other means,
now inside Lean's tiny trusted kernel.

## Progress

| # | result | file | status |
|---|---|---|---|
| 1 | S(2) ≥ 4: an explicit 2-coloring of {1,2,3,4} has no monochromatic Schur triple `a+b=c` | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `decide` |
| 2 | S(3) ≥ 13: an explicit 3-coloring of {1,…,13} has no monochromatic `a+b=c` (checks *all* pairs) | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `decide` |
| 3 | W(2,3) ≥ 9: a 2-coloring of {1,…,8} with no monochromatic 3-term arithmetic progression | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `decide` |
| 4 | S(2) ≤ 4: **every** 2-coloring of {1,…,5} has a monochromatic `a+b=c` (universal impossibility) | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `decide` |
| 5 | W(2,3) ≤ 9: **every** 2-coloring of {1,…,9} has a monochromatic 3-term progression | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `decide` |
| 6 | S(3) ≤ 13: **every** 3-coloring of {1,…,14} has a monochromatic `a+b=c` — pins **S(3) = 13** with Lemma 2 | [`LeanVerificationJourney/Basic.lean`](LeanVerificationJourney/Basic.lean) | ✅ `native_decide` |

Lemmas 1 + 4 pin **S(2) = 4** exactly. Lemmas 3 + 5 pin **W(2,3) = 9** exactly. Lemmas 2 + 6 pin **S(3) = 13** exactly.

Lemmas 1–5 are checked by Lean's kernel with no external tools and no Mathlib — `#print axioms` confirms *"does not depend on any axioms."* Lemma 6 uses `native_decide` (3^14 = 4,782,969 colorings to rule out — too many for kernel exhaustion), which adds the Lean compiler (`Lean.ofReduceBool`) to the trusted base. That's the honest, documented cost of the speed. See CONCEPTS.md for the tradeoff.

*(The single file currently holds all six combinatorics witnesses; it'll be split into modules as the
project grows.)*

Each piece corresponds to a self-verified claim from my
[certified-combinatorics-verification](https://github.com/MonongahelaHellbender/certified-combinatorics-verification)
tool — re-checked here by Lean instead of Python, shrinking the trusted base. The *large* upper bounds
(S(4) ≤ 44, W(2,5) ≤ 178) are far past what kernel `decide` can enumerate; those rest on a SAT solver
plus a machine-checkable **LRAT** certificate. Carrying that style of certificate *into* Lean is the
next part of the project — and it has now started:

## The LRAT bridge — a verified certificate checker

[`LeanVerificationJourney/Lrat.lean`](LeanVerificationJourney/Lrat.lean) is a small **proof checker**,
proved correct once, that turns an external SAT-solver refutation into a Lean theorem.

The idea that makes this scale: **prove the checker sound a single time** (by induction, in core Lean),
and then *every* instance is just a finite computation feeding that one theorem. Concretely
`checkProof_unsat : checkProof f steps = true → Unsat f`, where `Unsat f` quantifies over the
**infinite** space of all truth assignments — something `decide` can never brute-force directly, but
which a one-line certificate now discharges.

| result | what's checked | status |
|---|---|---|
| `rup_sound`, `checkProof_unsat` | the checker itself is sound (RUP + a growing learned-clause database) | ✅ proved, axioms = `propext, Quot.sound` only |
| `demoF_unsat`, `demoG_unsat` | two worked examples (a unit-propagation chain; the canonical 2-variable UNSAT, which needs a *learned* clause) | ✅ `decide` |
| `schur5_unsat` | **S(2) ≤ 4** via a *real* solver certificate (Schur {1..5}, k=2) | ✅ `decide` |
| `vdw923_unsat` | **W(2,3) ≤ 9** via a *real* certificate (10 proof steps, 50 clauses) | ✅ `decide` |
| `w24_unsat` ([`LratW24.lean`](LeanVerificationJourney/LratW24.lean)) | **W(2,4) ≤ 35** — 2³⁵ ≈ 34 billion colorings, *far beyond brute force* — via a real 429-step certificate | ✅ `native_decide` |

These are **not hand-written**: a real `glucose` run produces a DRAT proof, `drat-trim` converts it to
an LRAT certificate (`s VERIFIED`), and the data fed to `checkProof` is parsed straight from that. The
parser is *untrusted* — if it mis-translates anything, the verified checker simply returns `false` (a
refusal), never a wrong `Unsat`. All soundness lives in the proved theorem.

The small instances kernel-check (`by decide`), so their trusted base stays `propext, Quot.sound` — no
compiler, no Mathlib, no external tool trusted at proof time. **`w24_unsat` is the one that shows why
the bridge matters**: W(2,4) ≤ 35 is a *known* van der Waerden number, but its 2³⁵ colorings are utterly
past brute force — yet a 429-step certificate dispatches it. That one uses `native_decide` (429 steps is
too many to reduce in the kernel), so its `#print axioms` honestly shows the extra `ofReduceBool`
(compiler) axiom — the documented cost of climbing one rung up the trusted-base ladder, on purpose, when
brute force is off the table.

**Honest boundary.** The checker handles RUP steps (the common case; these certificates are RUP-only)
but not yet RAT steps, and it won't *scale* to the ~5-million-step S(4) ≤ 44 certificate — that's a
data-structure/performance wall (list append is O(n²)), not a soundness gap: the proof already covers
correctness at any size. Efficient array-backed checking is the next step.

## Understanding it (the point is the ideas, not the syntax)

- [`UNDERSTANDING.md`](UNDERSTANDING.md) — a concept-first primer on what formal verification *is* and
  why it's the durable skill in the AI era. Start here.
- [`CONCEPTS.md`](CONCEPTS.md) — plain-language companion explaining what each lemma *means*, lemma by
  lemma (including existence vs. universal, and coverage).

## Run it

See [SETUP.md](SETUP.md) — install Lean 4, build, and open in VS Code to see the green checkmarks.

## Why public

The visibility is the point: this is a portfolio that grows as the skill grows. Roadmap ahead —
array-backed LRAT checking to scale past tiny instances, RAT-step support, then a lemma from a 1D
fluid blow-up analysis, then small Mathlib contributions.

MIT licensed.
