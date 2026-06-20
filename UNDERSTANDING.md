# Understanding formal verification — the ideas (no code required)

A primer for building intuition, not for writing proofs. Re-read it; understanding compounds with
exposure. The goal is that you can *think* about verification clearly enough to direct AI to do it and
judge whether it actually did.

---

## 1. The only real question: how do you *know*?

Every claim — a theorem, a line of code, an AI's answer — comes with a question: *how sure are we, and
why?* There's a spectrum of answers, from weak to strong:

1. **Someone says so.** (Trust the person/tool.) Weakest.
2. **We tested it.** Tried some cases, they worked. Better — but only covers the cases you tried.
3. **We reasoned about it.** A human proof. Strong, but humans make mistakes and skip steps.
4. **A machine checked the reasoning.** A *formal proof*: every logical step verified by a small,
   trustworthy program. Strongest.

Formal verification lives at level 4. Its whole purpose is to move a claim up this ladder — to replace
"trust me" with "here is a proof a machine re-checked."

## 2. What a proof assistant actually is

A tool like **Lean** is a language where you can write down two things: a **statement** (a precise claim)
and a **proof** (a step-by-step justification) — and the tool's tiny core, the **kernel**, mechanically
checks that the proof really does establish the statement. If it doesn't, it's rejected. No persuasion,
no benefit of the doubt.

The magic isn't that it's automatic (often it isn't). The magic is that *what you must trust shrinks to
the kernel* — a few hundred lines you could audit — no matter how big or clever the rest is.

## 3. The four mental models (these are the whole game)

1. **A statement is an object.** "No coloring of {1..5} avoids a monochromatic sum" is a *thing* you can
   name and hold, not a vague assertion. Verification is manipulating these objects.
2. **A proof is a checkable value.** Proving = building something the kernel accepts. "Proof" stops being
   rhetorical and becomes binary: accepted or rejected.
3. **Trusted base.** You only have to trust the kernel. The clever search, the AI that wrote the proof,
   your own intuition — all can be wrong, and the kernel still catches it. *This is the answer to "how do
   I trust AI output?"*
4. **Decidability.** Some statements are finite and mechanical — a computer can settle them by brute
   force (Lean's `decide`). Others need a genuine idea. Knowing which is which is core judgment.

## 4. Decidable vs. not — and why it's the dividing line

If a claim ranges over *finitely many* cases, a computer can in principle check them all and settle it —
no cleverness required, just patience. That's `decide` in our little proofs (32 colorings here, 196
pairs there).

The moment a claim ranges over *infinitely many* cases — "for all whole numbers," "for every possible
input," "for the infinite-dimensional operator" — brute force is off the table. Now you need a real
mathematical argument. **That boundary — finite-and-exhaustible vs. genuinely-infinite — is where easy
verification ends and hard mathematics begins.** (It's exactly why the fluid blow-up result in this
ecosystem is stuck: its remaining claim is universal over an *infinite* operator.)

## 5. The deepest distinction: *existence* vs. *universal*

- **Existence** — "there is a good one." Proven by **one example**. Easy. (A demo. A passing test. "Look,
  it worked.")
- **Universal** — "they *all* work" or "it *never* fails." Proven by **ruling out every case**. Hard.

The claims that matter are almost always universal: *safety* ("never leaks"), *correctness* ("always
right"), *robustness* ("no input breaks it"). And here's the trap that fuels most overclaiming in the
world: **people show you an existence demo and let you believe a universal claim.** "Here's it working"
(existence) is quietly swapped for "it works" (universal). Catching that swap is the single most valuable
verification instinct you can have.

## 6. The one question that catches almost everything: *coverage*

When anyone — a person, a paper, an AI — hands you "I verified it," the sharpest question is usually not
"is each check correct?" It's: **"is anything *uncovered*?"** Did you check *all* the cases, or just
some? Is the claim universal but the evidence only existence? Was a whole category of input ignored?

Most verification failures aren't wrong checks — they're *missing* checks. Coverage is where you look.

## 7. Why this is *your* seat in the AI era

As AI gets better at *generating* — code, proofs, answers, papers — generation gets cheap and abundant.
What stays scarce is *knowing whether the generated thing is actually correct*. That's verification, and
it's a different muscle than generation:

- AI writes a proof → someone has to know if it's valid (and whether it proves the *right* statement).
- AI writes code → someone has to know if it meets the spec, *for all inputs*, not just the demo.
- AI claims "the system is safe" → someone has to know if that's a universal guarantee or an existence
  demo wearing a universal's clothes.

The person who can **direct AI to produce the work AND judge whether it's truly verified** sits in the
highest-leverage seat there is — and it gets *more* valuable as AI improves, because there's more
generated output that needs judging. These tiny Schur and van der Waerden proofs are the training reps.
The muscle they build — *statements as objects, trusted base, decidable vs. not, existence vs. universal,
coverage* — is the muscle that scales all the way up.

---

## Plain-language glossary (terms you'll hear)

- **Formal proof** — a proof a machine re-checks step by step.
- **Proof assistant / interactive theorem prover** (Lean, Coq, Isabelle) — the tool you write them in.
- **Kernel** — the small trusted core that does the final checking. The whole "trusted base."
- **`decide`** — "brute-force check all finite cases." Works only when the claim is finite & decidable.
- **`native_decide`** — a faster brute force that trusts the compiler too (bigger trusted base; a
  speed-vs-trust tradeoff).
- **Mathlib** — the big community library of formalized mathematics for Lean.
- **Decidable** — settleable by a finite mechanical procedure.
- **Existence vs. universal** — "there is one" vs. "they all" / "it never." The crux of §5.
- **Coverage** — whether *all* relevant cases are actually accounted for. The question of §6.
- **Trusted base** — the set of things you must trust for a proof to mean something. Smaller = better.

*The point is never the syntax. It's learning to think like this — and you already are.*
