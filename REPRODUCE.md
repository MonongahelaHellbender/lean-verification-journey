# Reproducing the certified results

Every claim in this repo is meant to be re-run, not taken on faith. This file says
exactly *what* reproduces *where*, so nothing rests on "trust me, I checked."

## Tier A — fully reproducible from this repo (and checked in CI)

These need only Lean 4 (`leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`) and
the files already in the repo. **CI runs all of this on every push.**

### Every kernel-checked theorem

```bash
lake build
```

This re-checks, in Lean's kernel, all the `decide` / `native_decide` results —
including the **W(2,4) ≤ 35** in-kernel certificate (`LratW24`) and the
**W(3,3) ≤ 27** String-decoded certificate (`LratScale`). A green build *is* the
proof; `#print axioms <thm>` shows each one's trusted base.

### The compiled checker, end-to-end, on the bundled certificates

The top rung (`lratcheck`) is a *compiled program*, not a kernel-checked object, so
building it is not enough — it has to actually run and emit `VERIFIED`:

```bash
lake build lratcheck
./.lake/build/bin/lratcheck samples_w33.cert   # W(3,3) ≤ 27,  6179 steps
./.lake/build/bin/lratcheck samples_r34.cert   # R(3,4) ≤ 9,   8635 steps
```

Each prints `s VERIFIED — UNSAT certified by the Lean-proven checkProofArr`. The CI
job (`.github/workflows/lean_action_ci.yml`) runs exactly these two commands and
fails if either does not say `VERIFIED`.

## Tier B — the two large results (local-only, by size)

**S(4) ≤ 44** (2,276,189 steps, 449 MB cert) and **W(2,5) ≤ 178** (607,312 steps,
144 MB cert) are produced by the *same* `lratcheck` program — but their certificates
are far too large to commit (hundreds of MB) or to run on a free CI runner. They are
**not in this repo**, and the README marks them as such. To reproduce them you
regenerate the certificate locally and feed it to the bundled, already-proven
checker. Nothing about the *checker* changes — only the input file does.

The certificate format `lratcheck` consumes is a flat, space-separated DIMACS-style
integer stream: the first integer is the original clause count, then 0-delimited
clauses, then the proof steps (see `parseCert` in `LratScale.lean`). Producing one
for S(4)/W(2,5) is a four-step pipeline:

1. **Generate the CNF.** The Schur / van der Waerden encodings live in
   [`certified-combinatorics-verification`](https://github.com/MonongahelaHellbender/certified-combinatorics-verification)
   (`verify.py`, `schur_clauses` / `vdw_clauses`). Emit DIMACS for S(4) on {1..45}
   or W(2,5) on {1..178}.
2. **Solve, emitting a proof.** Run a DRAT-producing SAT solver (e.g. `glucose`
   with proof logging, as `verify.py` does via `pysat`'s `with_proof=True`). The
   result is a DRUP/DRAT proof log.
3. **Convert to LRAT.** Run `drat-trim` on the CNF + DRAT proof to get a checked
   LRAT certificate (`s VERIFIED` from drat-trim itself).
4. **Flatten** the CNF+certificate into the space-separated integer format above and
   feed it to `./.lake/build/bin/lratcheck <file>`.

> **Honest status.** The flattening in step 4 is a small local script, not shipped
> here; steps 1–3 use standard external tools. The two large cert files were
> generated and checked this way locally — the run is reproducible, but it is *not*
> in CI, and you must regenerate the cert yourself. The soundness guarantee is
> identical to the bundled certs: a bug anywhere upstream can only make `lratcheck`
> *refuse*, never falsely accept (`checkProofArr_unsat`).

## What "reproduces" means here

A reader does **not** need to re-run anything to trust the *small* results — the
kernel already checked them and CI re-checks them. For the two large results, the
trust model is the one stated in `TRUST.md`: you trust the Lean proof of
`checkProofArr_unsat`, the Lean compiler, and an untrusted parser — exactly the
trust model of standalone verified checkers like `cake_lpr`.
