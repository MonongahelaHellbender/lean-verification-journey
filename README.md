# Lean verification journey

Learning **Lean 4** by formalizing real certified-computation results — in public, one lemma at a time.

The thesis: as AI gets better at *generating* math and code, the scarce, durable skill is *verifying*
it. Lean is where that happens at the frontier (AlphaProof, Harmonic, formal-methods-for-AI). This repo
is me building that skill the honest way — by re-proving results I've already certified by other means,
now inside Lean's tiny trusted kernel.

**→ [`TRUST.md`](TRUST.md) — what this repo is *really* about:** the certificate pattern for trusting
machine-generated answers, the named trusted-base ladder, and why this is the shape of trustworthy AI.

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
| `w33_unsat` ([`LratScale.lean`](LeanVerificationJourney/LratScale.lean)) | **W(3,3) ≤ 27** — a real **6179-step** certificate, certified in ~1.5 s | ✅ `native_decide`, String-encoded |

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

**Scaling — and where the real wall turned out to be.** Pushing past a few hundred steps surfaced a
surprise. A 6179-step certificate embedded as a `List Step` *literal* takes ~335 s just to **elaborate**
(Lean chewing through the nested `cons` literal); the checker's runtime is a rounding error beside it. So
the wall was never the checker's algorithm — it was the literal. Shipping the certificate as a single
`String` (one token — elaborates instantly) and parsing it at native runtime takes W(3,3) ≤ 27 from
~335 s to ~1.5 s, with **no change to the verified checker** ([`LratScale.lean`](LeanVerificationJourney/LratScale.lean)).
The cost, precisely located: reading a `String` rests on Lean's classical String API, so `w33_unsat`
adds `Classical.choice`. (An array-backed database is the textbook "scale" move and it's sound, but it
gave ~0 speedup here — runtime was never the bottleneck. *Measure before optimizing.*)

## The top of the ladder — a verified checker as a *program*

Past a few hundred thousand steps, no certificate fits as a `String` literal either (tens of MB of
source). At that point a self-contained Lean *theorem* is the wrong shape entirely: the kernel can't do
file IO, and the literal can't be elaborated. So the top rung is a different **kind** of artifact — the
proven checker, compiled to a program ([`Main.lean`](Main.lean), `lake build lratcheck`), that reads the
certificate from a **file** and runs the Array-backed `checkProofArr`
([`LratArray.lean`](LeanVerificationJourney/LratArray.lean), O(n), soundness inherited from the List
checker via refinement — axioms `propext, Quot.sound`).

| result | steps | cert size | `lratcheck` time |
|---|---|---|---|
| **W(2,5) ≤ 178** | 607,312 | 144 MB | ~47 s |
| **S(4) ≤ 44** | 2,276,189 | 449 MB | ~3 min |

Both are *known* combinatorial numbers, and both are far beyond anything embeddable as a theorem — yet
the Lean-proven checker dispatches them. **This is also where the array database finally earns its keep:**
useless when elaboration was the bottleneck, essential once runtime is (a List database would be O(n²)).

The trust model genuinely shifts here, and it's worth being precise: the output `s VERIFIED` is *not* a
kernel-checked proof object — it's the result of *running a proven-correct program*. You trust the Lean
proof of `checkProofArr_unsat`, the Lean compiler, and the (untrusted) parser — exactly the trust model of
standalone verified checkers like `cake_lpr`. A parser bug can still only cause a *refusal*, never a false
`VERIFIED`. Try it: `lake build lratcheck && ./.lake/build/bin/lratcheck samples_w33.cert` (a bundled
6179-step W(3,3) ≤ 27 certificate).

**The checker is family-agnostic.** Schur, van der Waerden, *and* Ramsey numbers all flow through the same
`lratcheck` unchanged — it only ever sees a CNF and a certificate, never the combinatorics. As a
demonstration, **R(3,3) = 6** (the classic "any party of six has three mutual friends or three mutual
strangers") and **R(3,4) = 9** were generated, solved, and certified by the same pipeline; the latter is
bundled as `samples_r34.cert` (an 8635-step proof). The certificates produced here are RUP-only (the
`glucose` solver emits DRUP proofs).

## Completing it — RAT, the general case ([`LratRat.lean`](LeanVerificationJourney/LratRat.lean))

RUP clauses are *implied* by the formula. The other rule SAT solvers use — **RAT** (resolution asymmetric
tautology, the basis of extended resolution / blocked clauses, used in proofs like Schur-5, Keller-7, the
Pythagorean triples) — adds clauses that are **not implied**: they can change the set of models. They're
still *satisfiability-preserving*, which is all an UNSAT proof needs, but that's a weaker and subtler
invariant, so the soundness argument is different.

`LratRat.lean` proves it: `rat_add_sat` is the classic flipped-assignment argument (if an assignment
satisfies the database but falsifies a RAT clause on pivot `l`, flip `l` — the RAT condition guarantees
the result still satisfies everything). On top of it, `checkProofGen_unsat` is a verified checker over a
mixed list of **RUP + RAT** steps — i.e. a general DRAT/LRAT proof. All of it has trusted base
`propext, Quot.sound` (no `Classical.choice`, no compiler). With this, the checker's *soundness* covers
any SAT certificate; the only remaining piece for an end-to-end RAT file run is the (untrusted) parser
that turns LRAT RAT-lines into step data.

**Honest boundary.** RAT soundness is proven and the general checker is built; wiring RAT-line *parsing*
into `lratcheck` is the remaining (mechanical, untrusted) plumbing. The parser also holds the whole token
list in memory, so truly enormous certificates would want streaming I/O. Neither is a soundness gap — the
proofs cover any size; these are engineering limits.

## Beyond SAT — the pattern transfers to AI safety ([`Ibp.lean`](LeanVerificationJourney/Ibp.lean))

The whole point (see [`TRUST.md`](TRUST.md)) is that the verification *pattern* isn't about SAT — SAT is
one instance. [`Ibp.lean`](LeanVerificationJourney/Ibp.lean) carries the same move into a different
field: **neural-network robustness** ("no adversarial example in the ε-ball flips the class") — AI safety
proper.

The primitive is **interval bound propagation** — the "RUP" of NN verification: push an input *box*
through the layers with interval arithmetic; if the output margin's lower bound stays positive, the
network is robust on the whole box. Heavy verifiers (α,β-CROWN, Marabou) find tight bounds by
branch-and-bound; the cheap, checkable core is this monotone propagation. Kept honest the same way as the
SAT work — **integers** (quantized networks, a real subfield, so no float to trust) and **core Lean**, no
Mathlib. `dot_interval` / `affine_sound` / `relu_sound` prove interval arithmetic over-approximates the
true network; `net_robust` then certifies a worked 2-layer ReLU net robust over `[-1,1]²` — class 0 beats
class 1 for *every* input in the box. `net_robust_global` separately audits this particular toy network
and proves the local box certificate was conservative: for this example, class 0 beats class 1 for every
integer input. Trusted base `propext, Classical.choice, Quot.sound` for the reusable IBP checker, and
`propext, Quot.sound` for the direct global toy-net proof.

That's the real signal: *the same person, the same pattern, a second domain.* What's verified changed
completely; what you trust is still a hundred lines you can read.

## Trusting an AI directly ([`AiProposes.lean`](LeanVerificationJourney/AiProposes.lean))

The most direct case: an AI hands you a *proof*. [`AiProposes.lean`](LeanVerificationJourney/AiProposes.lean)
makes "the AI proposes, the kernel disposes" concrete — a real LLM-generated proof, kernel-checked, with
the `#print axioms` **audit** as the trust boundary. The audit does more than confirm a proof typechecks:
it reveals *how* it was obtained (a proof that reached for the compiler shows the extra `ofReduceBool`
axiom), it refuses false claims outright, and it exposes a cheating `sorry` (which shows up as `sorryAx`).
AI fluency and confidence change none of it — the axiom list, not the model's say-so, is what you trust.

## Turning the lens back on Foundation itself ([`FoundationClaims.lean`](LeanVerificationJourney/FoundationClaims.lean))

The same discipline now applies to Foundation's own claim gates. [`FoundationClaims.lean`](LeanVerificationJourney/FoundationClaims.lean)
formalizes a small, real Foundation invariant: a result block may earn **private daily use** while still
refusing public release, production authorization, and checkpoint authorization. Stronger claims require
their own explicit gates.

The concrete Shield block currently represented there matches the operational posture: private daily use
earned; burn-in, trusted beta feedback, stakeholder review, signed release, public release, and production
not earned. Lean proves:

- `shield_private_use_gate_earned`
- `shield_public_release_not_earned`
- `shield_private_use_block_safe`
- `production_authorization_requires_gate`
- `checkpoint_authorization_requires_gate`

The key safety theorems do **not depend on any axioms**. This is the first formalized Foundation-native
claim boundary: not a toy domain, but the project's own rule that review-ready evidence must not silently
turn into production or public-release authority.

The module also formalizes Foundation's conservative evidence-composition rule: when multiple bounded
result blocks are combined, gates compose by **intersection**, not union. Lean proves that composition
cannot manufacture public-release or production prerequisites, and cannot create production/checkpoint
authorization when neither input had it. This is the dashboard/evidence-OS anti-overclaim invariant in
kernel-checked form.

Finally, it formalizes the negative-results rule. Foundation statuses include `earned`, `review`,
`blocked`, and `refused`; only `earned` is promotable. Lean proves that a blocked or refused input cannot
disappear into an earned aggregate. That is the machine-checked version of "failed gates stay visible as
evidence, but never as promotions."

The newest layer is claim-boundary consistency itself. A result block has a `doesClaim` surface and a
`doesNotClaim` surface; Lean proves the current Shield private-use boundary is internally consistent, and
that conservative boundary composition preserves consistency. In plain English: a dashboard aggregate is
not allowed to say "we claim production readiness" and "we do not claim production readiness" at the same
time, and composing evidence cannot create that contradiction unless an input was already contradictory.

It also starts formalizing provenance. A sourced boundary now carries minimal source metadata — artifact
recorded, reproducing command recorded, reproducibility flag recorded — and Lean proves the no-anonymous-
promotion rule: without a valid source record, a claim is not promotable. Conservative composition cannot
manufacture valid provenance either; if a composed sourced claim promotes, both inputs had valid source
metadata. This does **not** prove the outside world is true. It proves the dashboard grammar cannot treat
an unsourced claim as earned evidence.

The stricter version adds freshness: a source can be valid yet still not current enough for an operational
claim. `VersionedEvidenceSource` adds a version-pinned record and a current-check flag; Lean proves the
same refusal rule for stale evidence. A claim backed by an old or unversioned source may remain visible
as history, but it cannot power a current promotion under this formal grammar.

The current-authority layer adds expiry and refresh. `ExpiringEvidenceSource` requires the fresh source
to be unexpired before it can authorize a current claim. Lean proves that expired evidence cannot promote,
that aggregation cannot manufacture unexpired authority, and that a valid versioned source can become
current again through an explicit refresh check. This is the rule Foundation wants in production: keep old
evidence visible, but require a new check before it authorizes today's recommendation.

The artifact-identity layer closes the most obvious provenance loophole: checking one artifact while
claiming another. `ArtifactBoundSource` records both the artifact a claim cites and the artifact the
checker actually checked. Lean proves the mismatch refusal rule: if those identities differ, the claim is
not promotable. In a private deployment those identities can be concrete paths, hashes, or result-block
IDs; in Lean the important invariant is equality of the cited and checked artifact.

The result-row layer aligns that model with report schemas. `FoundationResultRow` is the logical payload
of a decoded report row: boundary, source, status, claimed artifact, checked artifact, and
`promotionAllowed`. Lean proves that any safe row with `promotionAllowed = true` implies promotable status,
the full artifact-bound claim, artifact identity match, and current source validity. It also proves the
refusal checks a JSON validator should enforce: mismatched artifacts cannot promote, invalid/expired
current sources cannot promote, and `review` / `blocked` / `refused` rows cannot promote. This is schema
semantics, not a JSON parser; it says what the parsed fields must prove.

## Understanding it (the point is the ideas, not the syntax)

- [`UNDERSTANDING.md`](UNDERSTANDING.md) — a concept-first primer on what formal verification *is* and
  why it's the durable skill in the AI era. Start here.
- [`CONCEPTS.md`](CONCEPTS.md) — plain-language companion explaining what each lemma *means*, lemma by
  lemma (including existence vs. universal, and coverage).

## Run it

See [SETUP.md](SETUP.md) — install Lean 4, build, and open in VS Code to see the green checkmarks.

## Why public

The visibility is the point: this is a portfolio that grows as the skill grows. Roadmap ahead —
RAT-line parsing into `lratcheck`, streaming I/O for arbitrarily large certificates, then a lemma from a
1D fluid blow-up analysis, then small Mathlib contributions.

MIT licensed.
