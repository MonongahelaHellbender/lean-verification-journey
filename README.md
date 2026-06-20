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
tool — re-checked here by Lean instead of Python, shrinking the trusted base. (Note the natural
boundary: the *large* upper bounds — S(4) ≤ 44, W(2,5) ≤ 178 — are far past what kernel `decide` can
enumerate; those rest on the SAT + LRAT + HOL4-verified chain in that tool, and bridging an LRAT
certificate into Lean is a later step on this roadmap.)

## Understanding it (the point is the ideas, not the syntax)

- [`UNDERSTANDING.md`](UNDERSTANDING.md) — a concept-first primer on what formal verification *is* and
  why it's the durable skill in the AI era. Start here.
- [`CONCEPTS.md`](CONCEPTS.md) — plain-language companion explaining what each lemma *means*, lemma by
  lemma (including existence vs. universal, and coverage).

## Run it

See [SETUP.md](SETUP.md) — install Lean 4, build, and open in VS Code to see the green checkmarks.

## Why public

The visibility is the point: this is a portfolio that grows as the skill grows. Roadmap ahead —
bridge an LRAT certificate (S(4)/W(2,5)) into Lean, then a lemma from a 1D fluid blow-up analysis,
then small Mathlib contributions.

MIT licensed.
