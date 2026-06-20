import LeanVerificationJourney.LratScale
import LeanVerificationJourney.LratArray

/-
  `lratcheck` — the top of the ladder.

  A self-contained Lean *theorem* cannot certify a multi-hundred-thousand-step
  UNSAT proof: the kernel can't do file IO, and a certificate that large can't be
  elaborated as a literal. So the top rung is a different *kind* of artifact — a
  verified checker **compiled to a program** that reads the certificate from a
  FILE and runs the Array-backed `checkProofArr` (O(n), so runtime stays sane at
  scale). If it prints VERIFIED, then `checkProofArr cert = true`, and the
  Lean-proved `checkProofArr_unsat` turns that into `Unsat`. The trust shifts from
  "the kernel checked a proof object" to "I ran a proven-correct program" — which
  is exactly how standalone verified checkers (cake_lpr) work.

  Usage:  lratcheck <flat-cert-file>
  The file is the same space-separated integer format `parseCert` consumes.
-/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let s ← IO.FS.readFile path
    let (f, steps) := parseCert s
    IO.println s!"parsed: {f.length} original clauses, {steps.length} proof steps"
    if checkProofArr f steps then
      IO.println "s VERIFIED — UNSAT certified by the Lean-proven checkProofArr"
      IO.println "  (checkProofArr_unsat : checkProofArr f steps = true → Unsat f)"
    else
      IO.println "REJECTED — the certificate did not check"
  | _ => IO.println "usage: lratcheck <flat-cert-file>"
