# Setup — checking these proofs yourself

This repo **is** a ready-to-build Lean 4 project, so there is nothing to scaffold:
install Lean, clone, and `lake build`. ~10 minutes, most of it the one-time
install. First-run hiccups are normal — see the bottom.

## 1. Install Lean 4 (via `elan`, the version manager)
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
# then restart your terminal (or: source ~/.profile / source ~/.zshrc) so `lake` is on PATH
lake --version    # confirm it printed a version
```
`elan` reads this repo's `lean-toolchain` and fetches the exact Lean version the
proofs were checked with, so you never have to match versions by hand.

## 2. Clone and build (the kernel checks every proof)
```bash
git clone https://github.com/MonongahelaHellbender/lean-verification-journey.git
cd lean-verification-journey
lake build
```
`Build completed successfully` = every theorem is machine-checked by Lean's
kernel. The build prints each theorem's type and, at the end, the
`#print axioms` lines — every one reports *"does not depend on any axioms,"* so
the trusted base is the kernel plus the few lines of encoding in
`LeanVerificationJourney/Basic.lean`. No Mathlib, no external tools.

This is exactly what the GitHub Actions badge runs on every push
(`.github/workflows/lean_action_ci.yml`), so a green badge means the public build
checks too.

## 3. See it live in VS Code (optional, but worth it)
- Install VS Code, then in Extensions search **"Lean 4"** (publisher: `leanprover`) and install it.
```bash
code .
```
Open `LeanVerificationJourney/Basic.lean`. After a few seconds Lean checks the
file (orange "loading" bar → gone). Put your cursor on `coloring_is_sum_free` and
the **Lean Infoview** (right panel) shows the proved statement; each `#check`
line shows a theorem's type.

## 4. Make it fail on purpose (this is how you learn it's real)
In `coloring`, change `3 => true` to `3 => false`. Now `1+3=4` is colored
`(A, A, A)` — a monochromatic Schur triple — so `coloring_is_sum_free` becomes
**false**, and `lake build` will refuse it with an error. Watching the proof
*reject* a wrong coloring is the proof that it was checking something real. Change
it back and the build goes green again.

## If something errors
Copy the exact error and read it slowly — Lean's errors are precise once you know
the shape of them, and learning to read them is half of learning Lean. The most
common first-run issue is simply `lake` not yet being on your `PATH` (re-open the
terminal after step 1).
