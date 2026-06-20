# The point: verification is the durable skill

This repo is a combinatorics-and-Lean portfolio on the surface. Underneath it is a single thesis,
demonstrated rather than asserted:

> **As machines get exponentially better at *generating* — proofs, code, search results, plans — the
> scarce and durable value moves to *verification*: making a machine's answer trustworthy.**

Everything here is one worked example of the move that does that.

---

## The pattern (one sentence)

**Don't make the powerful thing trustworthy. Make its output *checkable* by a small thing you have
proved correct — and make the check one-directional, so it can *refuse* but never *falsely accept*.**

In this repo:
- The "powerful thing" is a SAT solver — a large, fast, untrusted C program — plus a certificate
  toolchain (`drat-trim`).
- The "small proved thing" is `checkProof_unsat` / `checkProofArr_unsat`: a checker proved sound in
  Lean, whose entire trusted base you can read in one sitting.
- The certificate is the solver's proof log (DRAT → LRAT).
- One-directional: a bug anywhere in the solver, the toolchain, or the (unverified) parser can only make
  the checker *reject* a valid certificate — it can **never** make it accept an invalid one. Soundness
  is asymmetric, and that asymmetry is the safety.

This is exactly the architecture behind the landmark machine proofs of the last decade — Schur number 5,
the Boolean Pythagorean triples, Keller's conjecture in dimension 7, the chromatic number of the plane.
None of them are trusted because the solver is trusted; they are trusted because a *small, verified
checker* re-checked the certificate.

---

## What "trust" actually costs — named, not hand-waved

The discipline this repo trains is **stating precisely what you are trusting**, and Lean makes that
auditable: `#print axioms` lists every assumption a theorem leans on. The results here climb a ladder,
and each rung trades a larger trusted base for more capability — *on purpose, and labelled*:

| rung | what it buys | trusted base (beyond Lean's kernel) |
|---|---|---|
| `decide` | small finite facts | **nothing** — `propext, Quot.sound` only |
| `native_decide` | millions of cases | + the Lean **compiler** (`ofReduceBool`) |
| `String`-decoded certificate | thousands of proof steps, fast | + Lean's classical **String API** (`Classical.choice`) |
| verified checker as a **compiled program** | *millions* of steps from a file (S(4) ≤ 44, W(2,5) ≤ 178) | + the compiler + an untrusted parser; the output is a *program run*, not a kernel-checked object |

The skill is not "make the trusted base zero." That is impossible. The skill is **knowing exactly which
rung you are on and why that trust is acceptable for the claim at hand** — and refusing to quietly slide
up a rung without saying so. Most overclaiming in the world is a silent rung-change: a *demo* (one good
run, an existence claim) presented as a *guarantee* (a universal claim, "it never fails"). Watching a
checker prove a *universal* — "no assignment out of infinitely many satisfies this" — from a finite
certificate is the antidote.

---

## Why this is the answer to "how do I trust AI?"

The claims you actually care about with AI are almost always *universal*: "the system **never** leaks the
secret," "the code is **always** memory-safe," "there is **no** input that makes it misbehave." A demo
proves none of those — a demo is an existence claim, and one good run says nothing about a universal one.

You cannot make a large model trustworthy by inspection. But you can demand that its output come with a
*checkable certificate*, and verify that certificate with something small you trust. That is the entire
premise of programs like **ARIA's Safeguarded AI** (a gatekeeper that only permits an action accompanied
by a proof it is safe). This repo is that idea in miniature, end to end and working.

The pattern is not about SAT. The same shape transfers — and learning to see it is the transferable
asset:
- **SMT / theorem-prover output** — check the proof, trust the kernel, not the prover.
- **Neural-network robustness certificates** (α,β-CROWN, Marabou) — "no adversarial example within ε,"
  validated by a tiny checker rather than trusting the verifier. *(Done — see
  [`Ibp.lean`](LeanVerificationJourney/Ibp.lean): integer interval bound propagation, proved sound, a
  worked 2-layer ReLU net certified robust over a whole input box, plus a direct proof that this
  particular toy net is globally separated over all integer inputs.)*
- **Compiler translation validation** — certify "this output matches this input" instead of trusting the
  optimizer.
- **AI-generated proofs and code-with-specs** — the model proposes; a small trusted checker disposes.
  *(Done — see [`AiProposes.lean`](LeanVerificationJourney/AiProposes.lean): a real LLM-generated proof
  kernel-checked, with the `#print axioms` audit that reveals hidden trust and exposes a cheating `sorry`.)*
- **Foundation's own claim boundaries** — the project emits review, private-use, public-release, and
  production statuses; a small theorem should make it impossible to confuse them. *(Started — see
  [`FoundationClaims.lean`](LeanVerificationJourney/FoundationClaims.lean): private daily use can be
  earned while public release, production, and checkpoint authority remain refused; the core safety
  theorems have no axioms. The same module now proves a conservative composition rule: combining bounded
  evidence blocks by intersecting gates cannot create public-release, production, or checkpoint authority
  out of weaker inputs. It also proves the negative-results rule: blocked/refused statuses remain
  non-promotable under aggregation. The newest layer is claim-boundary consistency: each artifact has a
  `doesClaim` and `doesNotClaim` surface, and Lean proves the Shield boundary is consistent and that
  conservative composition preserves consistency. The provenance layer begins the next step: a sourced
  boundary carries artifact/command/reproducibility metadata, and Lean proves that an invalid source
  record cannot support a promotable claim. The freshness layer tightens this again: stale or unversioned
  evidence cannot support a current promotable claim. The current-authority layer adds expiry and refresh:
  expired evidence remains history, but it cannot promote until a fresh check restores current status.)*

In every case the judgment is the same: *Is there a small, checkable artifact? And do I trust the
checker — at which named rung?*

---

## The honest ceiling

Three limits, in increasing order of permanence:

1. **Scope.** This works only when the question reduces to a *finite, checkable certificate* — a finite
   invariant capturing the infinite part. Most of mathematics (analysis, number theory) does not reduce
   this way.
2. **Feasibility.** Some certificates are too large to produce or even to check (Schur 5's proof is
   petabytes). These are engineering walls, not walls of principle.
3. **Gödel (1931).** No consistent system of this strength can prove every true statement — and none can
   prove its own consistency. The ladder of "verify bigger and bigger finite things" is endless and
   useful; it never reaches "verify everything." The last and most important piece of judgment is knowing
   which of these three walls you are standing at.

---

*The position this repo argues for, by demonstration: a person who can drive machines to produce
results **and** certify those results against a small, named trusted base. As generation gets cheaper,
that seat gets scarcer and more valuable.*
