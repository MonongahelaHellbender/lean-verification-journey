/-
  Ibp.lean — the pattern in a SECOND domain: AI / neural-network robustness.
  ----------------------------------------------------------------------------
  The rest of this repo certifies SAT proofs. The verification *pattern* —
  a small, proven checker with a tiny named trusted base — is not about SAT,
  and this module shows it transfer cleanly to neural-network robustness, which
  is AI safety proper: "no adversarial example in the ε-ball flips the class."

  The primitive is **interval bound propagation** (IBP) — the "RUP" of NN
  verification. Push an input *box* through the layers with interval arithmetic;
  if the output margin's lower bound stays positive, the network is robust on the
  whole box. Heavy verifiers (α,β-CROWN, Marabou) compute tight bounds by
  branch-and-bound; the cheap, checkable core is this monotone propagation.

  Kept honest the same way as the SAT work: **integers** (quantized networks — a
  real subfield), so no float to trust; **core Lean**, no Mathlib. The soundness
  theorems (`dot_interval`, `affine_sound`, `relu_sound`) say interval arithmetic
  over-approximates the true network, so a box that separates the classes proves
  robustness for EVERY concrete input in it (`net_robust`).

  Trusted base: `propext, Classical.choice, Quot.sound` — the `Classical.choice`
  enters via the integer-order lemmas; still no Mathlib, no floats, no compiler.
-/

abbrev Vec := List Int
abbrev Box := List (Int × Int)   -- per-coordinate (lo, hi)

/-- `x` lies in the box. -/
def inBox : Vec → Box → Prop
  | [], [] => True
  | x :: xs, (lo, hi) :: bs => lo ≤ x ∧ x ≤ hi ∧ inBox xs bs
  | _, _ => False

/-- Dot product (lockstep; truncates on length mismatch). -/
def dot : Vec → Vec → Int
  | w0 :: ws, x0 :: xs => w0 * x0 + dot ws xs
  | _, _ => 0

/-- Lower bound of `dot w x` over the box (interval arithmetic). -/
def rowLo : Vec → Box → Int
  | w0 :: ws, (lo, hi) :: bs => (if w0 ≥ 0 then w0 * lo else w0 * hi) + rowLo ws bs
  | _, _ => 0

/-- Upper bound of `dot w x` over the box. -/
def rowHi : Vec → Box → Int
  | w0 :: ws, (lo, hi) :: bs => (if w0 ≥ 0 then w0 * hi else w0 * lo) + rowHi ws bs
  | _, _ => 0

theorem term_lo (w0 x0 lo hi : Int) (h1 : lo ≤ x0) (h2 : x0 ≤ hi) :
    (if w0 ≥ 0 then w0 * lo else w0 * hi) ≤ w0 * x0 := by
  split
  · rename_i hw; exact Int.mul_le_mul_of_nonneg_left h1 hw
  · rename_i hw
    have hw' : w0 ≤ 0 := Int.le_of_lt (Int.not_le.mp hw)
    exact Int.mul_le_mul_of_nonpos_left hw' h2

theorem term_hi (w0 x0 lo hi : Int) (h1 : lo ≤ x0) (h2 : x0 ≤ hi) :
    w0 * x0 ≤ (if w0 ≥ 0 then w0 * hi else w0 * lo) := by
  split
  · rename_i hw; exact Int.mul_le_mul_of_nonneg_left h2 hw
  · rename_i hw
    have hw' : w0 ≤ 0 := Int.le_of_lt (Int.not_le.mp hw)
    exact Int.mul_le_mul_of_nonpos_left hw' h1

/-- THE CORE: interval arithmetic over-approximates the dot product. -/
theorem dot_interval (w : Vec) : ∀ (x : Vec) (bx : Box),
    inBox x bx → w.length = x.length →
    rowLo w bx ≤ dot w x ∧ dot w x ≤ rowHi w bx := by
  induction w with
  | nil =>
    intro x bx hx hlen
    cases x with
    | nil =>
      cases bx with
      | nil => simp [rowLo, dot, rowHi]
      | cons => simp [inBox] at hx
    | cons => simp at hlen
  | cons w0 ws ih =>
    intro x bx hx hlen
    cases x with
    | nil => simp at hlen
    | cons x0 xs =>
      cases bx with
      | nil => simp [inBox] at hx
      | cons p bs =>
        obtain ⟨lo, hi⟩ := p
        obtain ⟨hlo, hhi, hrest⟩ := hx
        have hlen' : ws.length = xs.length := by simpa using hlen
        obtain ⟨ihlo, ihhi⟩ := ih xs bs hrest hlen'
        exact ⟨Int.add_le_add (term_lo w0 x0 lo hi hlo hhi) ihlo,
               Int.add_le_add (term_hi w0 x0 lo hi hlo hhi) ihhi⟩

#check @dot_interval
#print axioms dot_interval

theorem inBox_length : ∀ (x : Vec) (bx : Box), inBox x bx → x.length = bx.length := by
  intro x
  induction x with
  | nil => intro bx h; cases bx with | nil => rfl | cons => simp [inBox] at h
  | cons x0 xs ih => intro bx h; cases bx with
    | nil => simp [inBox] at h
    | cons p bs => obtain ⟨_, _, hr⟩ := h; simp [ih bs hr]

-- ReLU layer ------------------------------------------------------------------
def reluVec (x : Vec) : Vec := x.map (fun xi => max 0 xi)
def reluBox (bx : Box) : Box := bx.map (fun p => (max 0 p.1, max 0 p.2))

theorem relu_sound : ∀ (x : Vec) (bx : Box), inBox x bx → inBox (reluVec x) (reluBox bx) := by
  intro x
  induction x with
  | nil => intro bx h; cases bx with | nil => trivial | cons => simp [inBox] at h
  | cons x0 xs ih => intro bx h; cases bx with
    | nil => simp [inBox] at h
    | cons p bs =>
      obtain ⟨lo, hi⟩ := p
      obtain ⟨hlo, hhi, hr⟩ := h
      exact ⟨by simp [reluBox] at *; omega, by simp [reluVec, reluBox] at *; omega, ih bs hr⟩

#check @relu_sound
#print axioms relu_sound

-- Affine layer ----------------------------------------------------------------
def affineVec : List Vec → Vec → Vec → Vec
  | row :: W, bi :: b, x => (dot row x + bi) :: affineVec W b x
  | _, _, _ => []
def affineBox : List Vec → Vec → Box → Box
  | row :: W, bi :: b, ib => (rowLo row ib + bi, rowHi row ib + bi) :: affineBox W b ib
  | _, _, _ => []

theorem affine_sound : ∀ (W : List Vec) (b x : Vec) (ib : Box),
    inBox x ib → (∀ row ∈ W, row.length = x.length) →
    inBox (affineVec W b x) (affineBox W b ib) := by
  intro W
  induction W with
  | nil => intro b x ib _ _; simp [affineVec, affineBox, inBox]
  | cons row W ih =>
    intro b x ib hx hlen
    cases b with
    | nil => simp [affineVec, affineBox, inBox]
    | cons bi b =>
      have hrow : row.length = x.length := hlen row (by simp)
      obtain ⟨dlo, dhi⟩ := dot_interval row x ib hx hrow
      exact ⟨Int.add_le_add_right dlo bi, Int.add_le_add_right dhi bi,
             ih b x ib hx (fun r hr => hlen r (by simp [hr]))⟩

#check @affine_sound
#print axioms affine_sound

-- Robustness from a separated output box --------------------------------------
/-- If the output box's class-0 lower bound beats class-1's upper bound, then for
    the concrete output, class 0 strictly wins (no input in the box flips it). -/
theorem sep_first_beats_second (y : Vec) (a0 b0 a1 b1 : Int)
    (h : inBox y [(a0, b0), (a1, b1)]) (hsep : b1 < a0) :
    y.getD 1 0 < y.getD 0 0 := by
  cases y with
  | nil => simp [inBox] at h
  | cons y0 ys => cases ys with
    | nil => simp [inBox] at h
    | cons y1 yt => cases yt with
      | nil => obtain ⟨h0, _, _, h3, _⟩ := h; simp; omega
      | cons => simp [inBox] at h

-- WORKED EXAMPLE: a 2-input → 2-ReLU → 2-output integer net, proved robust ----
-- over the box [-1,1]^2: class 0 strictly beats class 1 for EVERY input.
def ib : Box := [(-1, 1), (-1, 1)]
def net (x : Vec) : Vec :=
  affineVec [[1, 1], [-1, -1]] [5, 0] (reluVec (affineVec [[1, 1], [1, -1]] [0, 0] x))
def netbox : Box :=
  affineBox [[1, 1], [-1, -1]] [5, 0] (reluBox (affineBox [[1, 1], [1, -1]] [0, 0] ib))

theorem net_in_box (x : Vec) (hx : inBox x ib) : inBox (net x) netbox := by
  have hxl : x.length = 2 := by have h := inBox_length x ib hx; simpa [ib] using h
  have len1 : ∀ row ∈ ([[1, 1], [1, -1]] : List Vec), row.length = x.length := by
    intro row hr; simp [List.mem_cons] at hr; rcases hr with rfl | rfl <;> simp [hxl]
  have s1 := affine_sound [[1, 1], [1, -1]] [0, 0] x ib hx len1
  have s2 := relu_sound _ _ s1
  have hlen2 : (reluVec (affineVec [[1, 1], [1, -1]] [0, 0] x)).length = 2 := rfl
  have len2 : ∀ row ∈ ([[1, 1], [-1, -1]] : List Vec),
      row.length = (reluVec (affineVec [[1, 1], [1, -1]] [0, 0] x)).length := by
    intro row hr; rw [hlen2]; simp [List.mem_cons] at hr; rcases hr with rfl | rfl <;> rfl
  exact affine_sound [[1, 1], [-1, -1]] [5, 0] _ _ s2 len2

/-- **ROBUSTNESS**: for every input in `[-1,1]²`, the network's class 0 strictly
    beats class 1 — a verified guarantee against any (integer) perturbation in the box. -/
theorem net_robust (x : Vec) (hx : inBox x ib) : (net x).getD 1 0 < (net x).getD 0 0 := by
  have hb : inBox (net x) netbox := net_in_box x hx
  have hnb : netbox = [(5, 9), (-4, 0)] := by decide
  rw [hnb] at hb
  exact sep_first_beats_second (net x) 5 9 (-4) 0 hb (by decide)

/-- For this particular toy network, the classifier is even stronger than the
    local IBP certificate: class 0 beats class 1 for every integer input.

    This is not the general verification method — `dot_interval`, `affine_sound`,
    `relu_sound`, and `net_robust` are the reusable checker pattern. This theorem
    is a direct audit of the worked example itself, showing the initial `[-1,1]²`
    robustness certificate was conservative. -/
theorem net_robust_global (x1 x2 : Int) :
    (net [x1, x2]).getD 1 0 < (net [x1, x2]).getD 0 0 := by
  simp [net, affineVec, reluVec, dot]
  omega

#check @affine_sound
#check @net_robust
#print axioms net_robust
#check @net_robust_global
#print axioms net_robust_global
