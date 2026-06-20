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

*Companion updated as we add each lemma. The point is never the syntax — it's the understanding.*
