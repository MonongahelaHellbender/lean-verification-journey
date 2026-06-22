import LeanVerificationJourney.Lrat
import LeanVerificationJourney.LratW24Data

/-
  LratW24.lean — the LRAT bridge doing what brute force CANNOT.
  ----------------------------------------------------------------------------
  W(2,4) = 35 is a known van der Waerden number. The upper bound W(2,4) ≤ 35
  says: EVERY 2-coloring of {1,…,35} contains a monochromatic 4-term arithmetic
  progression. There are 2^35 ≈ 34 *billion* colorings — utterly past what
  `decide` or `native_decide` could brute-force enumerate.

  But the verified checker in `Lrat.lean` doesn't enumerate colorings; it replays
  a SAT certificate. A real `glucose` run + `drat-trim` produced a 429-step LRAT
  proof (drat-trim: `s VERIFIED`); the CNF `w24F` and proof `w24Proof` are parsed
  straight from it and live in `LratW24Data.lean` (kept separate so this file is
  the *logic*, not ~880 lines of literal). The once-proved `checkProof_unsat`
  turns them into a theorem — the whole point of the bridge.

  `native_decide` (not kernel `decide`) — 429 steps is too many to reduce in the
  kernel — so `#print axioms` shows the `ofReduceBool` (compiler) axiom, the
  honest, documented cost. The small instances in `Lrat.lean` stay pure-kernel;
  this is where the trusted-base ladder is climbed on purpose.
-/

-- Elaborator guard for the `native_decide` below (the proof literal itself is
-- elaborated in `LratW24Data.lean`, which sets the same option). Not trusted base.
set_option maxRecDepth 100000

/-- **W(2,4) ≤ 35**, certified from a real 429-step SAT certificate. -/
theorem w24_unsat : Unsat w24F :=
  checkProof_unsat w24F w24Proof (by native_decide)

#check @w24_unsat
#print axioms w24_unsat
