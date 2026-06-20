# What it means — a plain-language companion

You don't need to *write* this code. You need to *understand* what it means, so you can direct AI to
produce it and judge whether it's right. This file explains the ideas behind each piece — concepts, not
syntax. Re-read it; understanding compounds with exposure.

---

## The one big shift: from "trust the answer" to "the logic was checked"

Normally a computer gives you an answer and you trust the program. A **formal proof** flips that: the
computer hands you the answer *plus a proof*, and a tiny, dumb, trusted **checker** (Lean's "kernel")
re-verifies every logical step. You no longer trust the big clever program — only the tiny checker.

That shrinking of *what you have to trust* is the whole game. It's called the **trusted base**, and
making it small is why formal proof matters — especially for AI, which is big, clever, and not
trustworthy by default.

---

## Our actual proof, idea by idea

The math: a **Schur number** S(k) asks — how far can you count from 1 while splitting the numbers into
k groups, with no group ever containing three numbers where `a + b = c`? For 2 groups, the answer is 4.
"S(2) ≥ 4" means: *there exists* a way to split {1,2,3,4} into 2 groups with no such triple. We prove it
by exhibiting one split and checking it.

| in the file | plain meaning | the idea you're learning |
|---|---|---|
| `coloring` | a rule assigning each number to one of two groups ("colors") | a **function**: input a number, output a group |
| `Bool` (true/false) | just the two group labels | data types are how you encode "what kind of thing this is" |
| `schurTriples` | the list of all `a+b=c` triples inside 1–4 | the **cases** we must check |
| `Monochromatic` | "all three numbers in this triple are the same color" = the *bad* event | a **Proposition**: a statement that's true or false |
| `Prop` | Lean's type for *statements themselves* | **the key idea: statements are objects you can hold, name, and prove** |
| `theorem ... := by decide` | "no triple is bad — and let the kernel check every case" | a **proof**; `decide` = exhaustive mechanical verification |

When `lake build` finishes with no errors, the kernel *itself* confirmed every case. That's stronger
than Python printing "True" — Python you trust; the kernel you can audit in a few hundred lines.

---

## The four mental models that transfer everywhere

1. **A statement is a thing.** In Lean, "no triple is monochromatic" is an *object* (a `Prop`) you can
   name, pass around, and prove. Most of math and verification is manipulating these objects.
2. **A proof is a checkable value.** Proving a statement = building an object whose existence the kernel
   can type-check. "Proof" stops being hand-wavy and becomes something a computer accepts or rejects.
3. **Trusted base.** You only have to trust the tiny checker. Everything else — the clever search, the
   AI that wrote the proof — can be wrong and you'd still catch it. This is *the* answer to "how do I
   trust AI output?"
4. **Decidable vs. not.** Some statements are *finite and mechanical* (`decide` can brute-check them);
   others need real ideas. Knowing which is which is a core judgment skill.

---

## Why this tiny thing is the whole thesis in miniature

This 20-line proof is the *atom* of "verifying AI." Scale the same idea up and it becomes: checking that
an AI's generated *code* meets its spec, that an AI's *proof* is actually valid, that an AI *system*
does what it claims. As AI generates more, the person who understands **what a verification means and
whether it's the right one** holds the leverage. That person is what you're training your brain to be —
through exactly this kind of repeated, concept-first exposure.

---

## Lemma #2 (S(3) ≥ 13) — what's new, conceptually

Same idea (a coloring with no monochromatic `a+b=c`), scaled to 3 colors and 13 numbers. But it teaches
**one important upgrade in how you verify** — worth internalizing because it's a judgment skill:

- **Lemma #1** listed the triples by hand (`1+1=2, 1+2=3, …`). Fine for tiny cases, but it leans on a
  human having listed *every* triple. If you forgot one, the proof would still pass — and be meaningless.
  That's a **trust gap**.
- **Lemma #2** instead says: "for *every* pair `a, b` in 1..13 with `a+b ≤ 13`, the triple `(a, b, a+b)`
  is not monochromatic." It never lists triples — it makes the computer generate and check *all* of
  them. **No gap.** The kernel, not a human, guarantees completeness.

The transferable lesson — and it's exactly the kind of thing you'll judge AI's work by: **a verification
is only as good as its coverage.** "We checked these cases" is weaker than "we checked *all* cases, by
construction." When AI hands you a proof or a test suite, the sharpest question is often not "is each
check right?" but **"is anything *uncovered*?"** Lemma #2 is the good pattern; Lemma #1 is the
acceptable-but-watch-it pattern.

(Aside you'll meet later: checking "all pairs" can get slow as numbers grow. There's a faster cousin of
`decide` called `native_decide` that compiles to fast machine code — but it *enlarges the trusted base*
by trusting the compiler too. Speed vs. trusted-base is a real tradeoff you'll weigh. We're staying with
plain `decide` here precisely because the trusted base stays tiny.)

---

## Lemma #3 (W(2,3) ≥ 9) — the pattern generalizes

This one looks different and *is* different in its math: van der Waerden's theorem is about **arithmetic
progressions** (three equally-spaced numbers `a, a+d, a+2d`), not sums. We exhibit a 2-coloring of
{1,…,8} with no progression all one color.

But here's the thing worth seeing: **the verification is the *same shape* as before.** Define a coloring
→ define the "bad structure" → check *all* cases by construction. Only the bad structure changed (a
progression instead of a sum).

The transferable idea: once you have a *pattern of verifying* ("enumerate every instance of the bad
thing and confirm none occurs"), it transfers across problems that look unrelated on the surface.
Recognizing that two different-looking problems have the *same verification skeleton* is exactly the
kind of structural judgment that makes someone fast and trustworthy — whether they're checking math, or
checking what an AI produced. You're not memorizing Schur or van der Waerden; you're learning the
*shape* of "verify a finite combinatorial claim," which is reusable forever.

---

## Lemma #4 (S(2) ≤ 4) — the deepest idea: *existence* vs. *universal*

This is the most important concept in the whole file, so sit with it.

- Lemmas 1–3 proved **existence**: "there *exists* a coloring that works." To prove it, you show **one**
  example. Easy.
- Lemma 4 proves a **universal impossibility**: "*every* coloring fails." You can't show one example —
  you must rule out **all** of them (here, all 2⁵ = 32 colorings of five numbers).

These two are different *kinds* of truth, and the gap between them is the whole story of verification:

| kind | shape | how you prove it | example |
|---|---|---|---|
| existence | "there is a good one" | exhibit **one** witness | S(2) ≥ 4: here's a coloring |
| universal | "they **all** fail" / "it **never** happens" | rule out **every** case | S(2) ≤ 4: no coloring of 5 works |

**Why this is the crux for AI.** The claims you actually care about with AI are almost always the
*universal* kind: "the system **never** leaks the secret," "the code is **always** memory-safe," "there
is **no** input that makes it misbehave." Those are infinitely harder than "here's one good run," because
one good example proves nothing about a universal claim — you need *coverage of all cases*, by exhaustion
(when finite, like here) or by a real argument (when infinite). A demo shows existence; **safety is
universal.** Knowing the difference — and refusing to accept a witness when the claim is universal — is
exactly the judgment that makes a verifier trustworthy. Most overclaiming in the world is quietly
swapping a universal claim for an existence demo.

(And note: Lemma 4 is *finite* (32 colorings), so `decide` can brute-force the universal claim. When the
universal claim is over *infinitely* many cases — like "for all inputs" — brute force is impossible and
you need an actual proof. That boundary, finite-exhaustible vs. genuinely-infinite, is the one from the
blow-up work too: there the open lemma is a universal claim over an infinite operator, which is exactly
why it's hard.)

---

## Lemma #5 (W(2,3) ≤ 9) — the same crux, a second time, on a different object

Lemma 5 is the universal-impossibility partner for van der Waerden, exactly as Lemma 4 was for Schur:
*every* one of the 2⁹ = 512 two-colorings of {1,…,9} contains a monochromatic 3-term progression. Pair
it with Lemma 3 (a good coloring of {1,…,8} exists) and you've pinned **W(2,3) = 9** exactly — both the
"you can get this far" and the "you can get no further" halves, each kernel-checked.

The reason it's worth doing twice: the *idea* — exhibit one witness for existence, exhaust every case for
a universal — is supposed to transfer across problems unchanged. Watching it land identically on sums
(Schur) and on progressions (van der Waerden) is the evidence that you've learned a *pattern*, not memorized
one example. The only practical wrinkle is size: 512 cases needed a higher `maxRecDepth` for the
elaborator, but that's a search-budget knob, not a change to what's trusted — `#print axioms` still
reports the proof *"does not depend on any axioms."*

**Where this stops.** Both impossibility lemmas here are *finite* (32 and 512 colorings). The next results
up — S(4) ≤ 44, W(2,5) ≤ 178 — have far too many colorings to enumerate in the kernel, which is precisely
why the companion `certified-combinatorics-verification` tool proves them through a SAT solver plus a
machine-checkable LRAT/HOL4 certificate. Carrying one of those certificates *into* Lean is the next rung,
and it's the same finite-exhaustible vs. genuinely-large boundary again — only now the honest answer is
"use a certificate," not "brute-force it."

---

## Lemma #6 (S(3) ≤ 13) — the first step up the trusted-base ladder

This pairs with Lemma #2 (S(3) ≥ 13) to pin **S(3) = 13** exactly. The math is the same shape as
Lemma #4 (S(2) ≤ 4): rule out every coloring. What changes is the *scale* — 3^14 = 4,782,969
colorings instead of 2^5 = 32 — and that forces a deliberate engineering choice.

**Why `native_decide` instead of `decide`?**

`decide` runs the check *inside Lean's kernel*. The kernel is tiny, interpreted, and trusted. For
32 cases (Lemma #4), that's instant. For 4.8 million cases, the kernel would grind for hours.

`native_decide` *compiles* the check to machine code and runs it. The result comes back in seconds.
But there's a cost: you now also trust the **Lean compiler**, not only the kernel. Lean captures this
precisely — `#print axioms S3_upper_bound` reports:

```
'S3_upper_bound' depends on axioms: [S3_upper_bound._native.native_decide.ax_1_1]
```

That axiom is `Lean.ofReduceBool`: "if native compiled code returned `true`, trust it." It's the
explicit, auditable price of using the compiler. Compare: `S2_upper_bound` reports *"does not depend
on any axioms"* — pure kernel. Both are real proofs; they differ in what you have to trust.

**The lesson that transfers:**

When you evaluate AI-generated proofs, code, or test suites, you constantly face a version of this
tradeoff: deeper checking costs more (time, resources, tooling); faster checking trusts more (the
compiler, the framework, the approximation). The right choice depends on how much the result matters
and what's inside the trusted thing. `native_decide` trusts the Lean compiler, which is itself
heavily tested and formally studied — a reasonable extension of trust for a combinatorics check. It
would *not* be reasonable for a safety-critical system where the compiler itself might be the attack
surface. Knowing the difference, and being able to articulate which part you're trusting, is the
judgment skill. The axiom list makes that judgment explicit.

**Where this fits in the hierarchy:**

| method | cases handled | trusted base beyond the kernel |
|---|---|---|
| `decide` | up to ~tens of thousands | nothing |
| `native_decide` | millions | Lean compiler + `Lean.ofReduceBool` |
| SAT + LRAT (external) | billions | drat-trim + LRAT format spec |
| SAT + LRAT in Lean | billions | a Lean-internal LRAT checker (next rung) |

S(4) ≤ 44 and W(2,5) ≤ 178 are in the SAT+LRAT row — the companion
`certified-combinatorics-verification` tool handles them via drat-trim + HOL4-verified cake_lpr.
Bringing that chain into Lean's hierarchy is the next rung on this roadmap.

---

## The LRAT bridge (`Lrat.lean`) — the deepest idea so far: *trust a checker, not an answer*

Up to now, every result was its own proof. `Lrat.lean` is different: it's a **proof checker** — one
program, proved correct once, that can certify *many* results without re-proving anything. This is how
the verified-math frontier actually scales, and it's worth understanding the shape.

**The problem.** A SAT solver can prove a formula has *no* solution — but the solver is a huge, fast,
untrustworthy C program. You don't want to trust it. Modern solvers therefore emit a **certificate**: a
step-by-step log (DRAT, then refined to **LRAT**) that a *tiny* checker can replay and confirm. The
trust moves from the giant solver to the tiny checker — the same move as Lean's kernel, one level up.

**What we built.** A checker in core Lean that replays an LRAT-style certificate:

- A certificate learns one new clause at a time, each justified by **RUP** (reverse unit propagation):
  "assume the new clause is false, propagate the forced consequences using the listed earlier clauses,
  and hit a contradiction." When it finally learns the *empty* clause, the formula is unsatisfiable.
- The checker maintains a growing **database** of clauses and replays each step.

**The one idea that makes it scale — prove the checker, not the answer.** We prove *once*, by induction:

> `checkProof_unsat : checkProof f steps = true → Unsat f`

After that, certifying any specific formula is just *running* `checkProof` (a finite `Bool`
computation) and quoting this theorem. Notice what `Unsat f` says: *no* assignment, out of the
**infinitely many** functions `Nat → Bool`, satisfies `f`. `decide` could never brute-force that — it's
a universal over an infinite domain (exactly the existence-vs-universal crux from Lemma 4, now over an
*infinite* space). Yet a one-line certificate discharges it, because the *checker* was proved sound for
all inputs in advance. **A proved checker converts a finite computation into an infinite guarantee.**
That is the whole reason formal verification scales.

**The honesty mechanism you should internalize.** The certificate data is produced by *untrusted* code
(a real `glucose` solver, `drat-trim`, and a Python parser). None of that is trusted. If any of it is
wrong, `checkProof` returns `false` — a *refusal* — and you simply have no theorem. It can never return
`true` for a false statement, because that direction is what the soundness proof forbids. So the design
rule is: **push everything you can into the untrusted side, and let a small proved core be the only
thing standing between you and a false claim.** When you evaluate an AI system later, this is the
pattern to reach for — not "is the smart part correct?" but "is there a small *checkable* artifact, and
do I trust the checker?"

**Real certificates, not toys.** `schur5_unsat` (S(2) ≤ 4) and `vdw923_unsat` (W(2,3) ≤ 9) are checked
from certificates a real solver actually emitted — the second is a 10-step, 50-clause proof. Both
kernel-check (`by decide`), so the trusted base is still just `propext, Quot.sound`. Debugging them
taught the real lessons: LRAT clause-IDs are non-contiguous and interleave deletions (the parser must
remap and skip them), and a clause is a *set* of literals — a solver silently dedups `[-3,-3,-7]` to
`{-3,-7}`, and a checker that forgets this will wrongly reject a valid proof. Every such bug was a false
*rejection*, never a false acceptance — which is exactly the safety the soundness proof buys you.

**The one that shows why this matters: `w24_unsat` (W(2,4) ≤ 35).** Here the bridge does something no
amount of `decide`/`native_decide` brute force could: ruling out all 2³⁵ ≈ 34 *billion* colorings of
{1,…,35}. We never enumerate them — a real 429-step certificate is replayed by the *same* verified
checker, and the universal claim falls out. This is the entire thesis in one theorem: **a proved checker
plus a small certificate beats brute force on a problem brute force can't touch.** The cost is honest and
visible — 429 steps is too many to reduce in the kernel, so it uses `native_decide`, and `#print axioms`
duly shows the extra `ofReduceBool` (compiler) axiom. That's the trusted-base ladder being climbed
*deliberately*, exactly when the cheaper rung runs out — and being able to say precisely which rung
you're on is the skill.

**Where it stops (for now).** The checker is RUP-only (no RAT steps yet). Scaling further ran into a
genuinely instructive surprise — see the next section.

---

## Scaling, and the lesson of measuring the right thing (`LratScale.lean`)

The obvious way to push to bigger certificates is "make the checker faster" — and the textbook move is to
replace the linked-list clause database (whose `++` append is O(n)) with an array (O(1)). That instinct is
reasonable, and an array-backed version *was* built and proved sound. **It gave essentially zero speedup.**

Why? Because the bottleneck was never the checker. A 6179-step certificate written as a `List Step`
*literal* takes ~335 seconds just for Lean to **elaborate** — to chew through a 6179-deep nested `cons`
expression at the syntax level, before any checking happens at all. The checker's actual runtime, once
compiled to native code, is well under a second even as a humble linked list. We optimized the part that
wasn't slow.

The fix addresses the *real* bottleneck: ship the certificate as a single **`String`** literal. A string
is one token — it elaborates instantly, no matter how long — and you parse it into clauses and steps at
native runtime, where speed is a non-issue. Same verified checker, unchanged. W(3,3) ≤ 27 (a 6179-step
proof) drops from ~335 s to ~1.5 s.

The transferable lesson is one every engineer re-learns the hard way, and it's worth internalizing here
where it's cheap: **measure before you optimize.** The "scale" problem looked like an algorithms problem
and was actually a representation problem one layer down. When you're handed a slow AI system — or any
system — the discipline is the same: find where the time actually goes before you rewrite the part you
*assumed* was slow.

**The honest cost, precisely located.** Reading a `String`'s characters rests on Lean's classical String
library, so `w33_unsat` adds `Classical.choice` to its axioms (on top of `native_decide`'s
`ofReduceBool`). That's a real, named entry in the trusted base — documented, standard, and exactly the
kind of thing being precise about is the whole point. And the parser remains *untrusted for soundness*:
`checkProof_unsat` holds for whatever it produces, so a parser bug can only make the check refuse, never
accept a false `Unsat`.

**The remaining ceiling** is now the string literal's own size. Certificates in the millions of steps
(S(4) ≤ 44 ≈ 5M, W(2,5) ≤ 178 ≈ 600k) would be tens of megabytes of source — impractical to embed. Going
there means reading the certificate from a *file* at runtime, which is how standalone verified checkers
(`cake_lpr`) actually work — a different architecture from a self-contained Lean theorem, and a natural
next rung.

---

*Companion updated as we add each lemma. The point is never the syntax — it's the understanding.*
