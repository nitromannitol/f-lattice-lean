import FLatticePaper.Graph
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Task 44, step 2: the comparison-field contacts (fixes/Q1.md paragraph 4, local part).

Paragraph 4, verbatim: "Each comparison field m is binary, is bounded above by F on the closed polygon by the window estimates,
and realizes the corresponding lower contact. If F=m at a black root, the sum of its two nonnegative input gaps is ΔF−Δm≤0, so
both inputs are contacts. If a forced white has a positive gap at its forced input, the same sum is at most one. The forced input
has gap one, the other input gap zero, and m is black there."

The input gap at an input `i` of a root `c` is `F i − m i`, nonnegative when `m ≤ F`. The three comparison fields of the fix are
`F(z − v) + ε a·z + c0 − 1`, `F(z + σ)` and `F(z − σ) − 2`; they are binary when `F` is, since the shifts preserve parity and the
affine and constant terms have zero Laplacian. -/

namespace FLatticePaper.Contacts

open FLatticePaper

/-- The two inputs of a site add to twice the site, coordinatewise. -/
theorem input_sum_coords (c : Site) :
    (incomingNeg c).1 + (incomingPos c).1 = 2 * c.1 ∧ (incomingNeg c).2 + (incomingPos c).2 = 2 * c.2 := by
  unfold incomingNeg incomingPos
  split_ifs <;> dsimp only <;> constructor <;> ring

/-- Even shifts preserve the parity of sites, and hence the input structure. -/
theorem incomingNeg_add_even (c s : Site) (hs : EvenSite s) : incomingNeg (c + s) = incomingNeg c + s := by
  unfold EvenSite at hs
  unfold incomingNeg
  by_cases h : (c.1 + c.2) % 2 = 0
  · have h' : ((c + s).1 + (c + s).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos (show EvenSite c from h), if_pos (show EvenSite (c + s) from h')]
    ext <;> simp
    ring
  · have h' : ¬ ((c + s).1 + (c + s).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg (show ¬ EvenSite c from h), if_neg (show ¬ EvenSite (c + s) from h')]
    ext <;> simp
    ring

theorem incomingPos_add_even (c s : Site) (hs : EvenSite s) : incomingPos (c + s) = incomingPos c + s := by
  unfold EvenSite at hs
  unfold incomingPos
  by_cases h : (c.1 + c.2) % 2 = 0
  · have h' : ((c + s).1 + (c + s).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos (show EvenSite c from h), if_pos (show EvenSite (c + s) from h')]
    ext <;> simp
    ring
  · have h' : ¬ ((c + s).1 + (c + s).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg (show ¬ EvenSite c from h), if_neg (show ¬ EvenSite (c + s) from h')]
    ext <;> simp
    ring

/-- Shifting the field by an even site shifts its Laplacian. -/
theorem laplacian_shift_even (F : Field) (s : Site) (hs : EvenSite s) (c : Site) :
    laplacian (fun z => F (z + s)) c = laplacian F (c + s) := by
  unfold laplacian
  rw [incomingNeg_add_even c s hs, incomingPos_add_even c s hs]

theorem evenSite_neg {v : Site} (hv : EvenSite v) : EvenSite (-v) := by
  unfold EvenSite at hv ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

/-- An affine term `ε (a₁ z₁ + a₂ z₂)` and a constant do not change the Laplacian. -/
theorem laplacian_affine (g : Field) (ε : ℤ) (a : Site) (k : ℤ) (c : Site) :
    laplacian (fun z => g z + ε * (a.1 * z.1 + a.2 * z.2) + k) c = laplacian g c := by
  obtain ⟨h1, h2⟩ := input_sum_coords c
  unfold laplacian
  dsimp only
  linear_combination (ε * a.1) * h1 + (ε * a.2) * h2

theorem laplacian_sub_const (g : Field) (k : ℤ) (c : Site) :
    laplacian (fun z => g z - k) c = laplacian g c := by
  unfold laplacian
  dsimp only
  ring

/-- The lower comparison field `F(z − v) + ε a·z + c0 − 1`, with `z − v` written `z + (−v)`. -/
def cmpLow (F : Field) (v : Site) (ε : ℤ) (a : Site) (c0 : ℤ) : Field :=
  fun z => F (z + -v) + ε * (a.1 * z.1 + a.2 * z.2) + (c0 - 1)

/-- The upper comparison field `F(z + σ)`. -/
def cmpUp (F : Field) (σ : Site) : Field := fun z => F (z + σ)

/-- The lower-contact comparison field `F(z − σ) − 2`, with `z − σ` written `z + (−σ)`. -/
def cmpDown (F : Field) (σ : Site) : Field := fun z => F (z + -σ) - 2

/-- The lower comparison field is binary when `F` is binary and `v` is even. -/
theorem cmpLow_binary {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {v : Site} (hv : EvenSite v)
    (ε : ℤ) (a : Site) (c0 : ℤ) (c : Site) :
    laplacian (cmpLow F v ε a c0) c = -1 ∨ laplacian (cmpLow F v ε a c0) c = 0 := by
  unfold cmpLow
  rw [laplacian_affine (fun z => F (z + -v)) ε a (c0 - 1) c, laplacian_shift_even F (-v) (evenSite_neg hv) c]
  exact hF _

/-- The upper comparison field is binary when `F` is binary and `σ` is even. -/
theorem cmpUp_binary {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {σ : Site} (hσ : EvenSite σ)
    (c : Site) : laplacian (cmpUp F σ) c = -1 ∨ laplacian (cmpUp F σ) c = 0 := by
  unfold cmpUp
  rw [laplacian_shift_even F σ hσ c]
  exact hF _

/-- The lower-contact comparison field is binary when `F` is binary and `σ` is even. -/
theorem cmpDown_binary {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {σ : Site} (hσ : EvenSite σ)
    (c : Site) : laplacian (cmpDown F σ) c = -1 ∨ laplacian (cmpDown F σ) c = 0 := by
  unfold cmpDown
  rw [laplacian_sub_const (fun z => F (z + -σ)) 2 c, laplacian_shift_even F (-σ) (evenSite_neg hσ) c]
  exact hF _

/-- **Contact at a black root.** If `F` is black at `c`, `m` is binary and `F = m` at `c` with `m ≤ F` at the two inputs, then both
inputs are contacts: the sum of the two nonnegative input gaps is `ΔF − Δm ≤ 0`. -/
theorem contact_black {F m : Field} {c : Site} (hF : laplacian F c = -1)
    (hm : laplacian m c = -1 ∨ laplacian m c = 0) (heq : F c = m c)
    (hle1 : m (incomingNeg c) ≤ F (incomingNeg c)) (hle2 : m (incomingPos c) ≤ F (incomingPos c)) :
    F (incomingNeg c) = m (incomingNeg c) ∧ F (incomingPos c) = m (incomingPos c) := by
  have hm1 : -1 ≤ laplacian m c := by
    rcases hm with h | h <;> linarith
  unfold laplacian at hF hm1
  have hsum : (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) ≤ 0 := by
    linarith
  constructor
  · apply le_antisymm <;> linarith
  · apply le_antisymm <;> linarith

/-- **Contact at a white root, forced input on the negative side.** If `F` is white at `c` with `F = m` there, `m` binary, `m ≤ F`
at the inputs, and the negative input has positive gap, then the gap is one, the positive input's gap is zero, and `m` is black. -/
theorem contact_white_neg {F m : Field} {c : Site} (hF : laplacian F c = 0)
    (hm : laplacian m c = -1 ∨ laplacian m c = 0) (heq : F c = m c)
    (hle2 : m (incomingPos c) ≤ F (incomingPos c))
    (hpos : m (incomingNeg c) < F (incomingNeg c)) :
    laplacian m c = -1 ∧ F (incomingNeg c) = m (incomingNeg c) + 1 ∧ F (incomingPos c) = m (incomingPos c) := by
  unfold laplacian at hF
  have hb : laplacian m c = -1 := by
    rcases hm with h | h
    · exact h
    · exfalso
      unfold laplacian at h
      linarith
  unfold laplacian at hb
  have hsum : (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) = 1 := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold laplacian
    exact hb
  · linarith
  · linarith

/-- **Contact at a white root, forced input on the positive side.** The mirror of `contact_white_neg`. -/
theorem contact_white_pos {F m : Field} {c : Site} (hF : laplacian F c = 0)
    (hm : laplacian m c = -1 ∨ laplacian m c = 0) (heq : F c = m c)
    (hle1 : m (incomingNeg c) ≤ F (incomingNeg c))
    (hpos : m (incomingPos c) < F (incomingPos c)) :
    laplacian m c = -1 ∧ F (incomingPos c) = m (incomingPos c) + 1 ∧ F (incomingNeg c) = m (incomingNeg c) := by
  unfold laplacian at hF
  have hb : laplacian m c = -1 := by
    rcases hm with h | h
    · exact h
    · exfalso
      unfold laplacian at h
      linarith
  unfold laplacian at hb
  have hsum : (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) = 1 := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold laplacian
    exact hb
  · linarith
  · linarith

/-- **Black contact for the upper comparison field.** At a black root `c` of `F` with `F c = F (c + σ)` and `F (· + σ) ≤ F` at the
inputs, both inputs of `c` are contacts of `F(· + σ)`. -/
theorem cmpUp_contact_black {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {σ : Site} (hσ : EvenSite σ)
    {c : Site} (hFc : laplacian F c = -1) (heq : F c = F (c + σ))
    (hle1 : F (incomingNeg c + σ) ≤ F (incomingNeg c)) (hle2 : F (incomingPos c + σ) ≤ F (incomingPos c)) :
    F (incomingNeg c) = F (incomingNeg c + σ) ∧ F (incomingPos c) = F (incomingPos c + σ) :=
  contact_black hFc (cmpUp_binary hF hσ c) heq hle1 hle2

/-- Black contact for the lower comparison field, at a black root of `F`. -/
theorem cmpLow_contact_black {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {v : Site} (hv : EvenSite v)
    (ε : ℤ) (a : Site) (c0 : ℤ) {c : Site} (hFc : laplacian F c = -1)
    (heq : F c = cmpLow F v ε a c0 c)
    (hle1 : cmpLow F v ε a c0 (incomingNeg c) ≤ F (incomingNeg c))
    (hle2 : cmpLow F v ε a c0 (incomingPos c) ≤ F (incomingPos c)) :
    F (incomingNeg c) = cmpLow F v ε a c0 (incomingNeg c) ∧
      F (incomingPos c) = cmpLow F v ε a c0 (incomingPos c) :=
  contact_black hFc (cmpLow_binary hF hv ε a c0 c) heq hle1 hle2

/-- Black contact for the lower-contact comparison field, at a black root of `F`. -/
theorem cmpDown_contact_black {F : Field} (hF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {σ : Site} (hσ : EvenSite σ)
    {c : Site} (hFc : laplacian F c = -1) (heq : F c = cmpDown F σ c)
    (hle1 : cmpDown F σ (incomingNeg c) ≤ F (incomingNeg c))
    (hle2 : cmpDown F σ (incomingPos c) ≤ F (incomingPos c)) :
    F (incomingNeg c) = cmpDown F σ (incomingNeg c) ∧ F (incomingPos c) = cmpDown F σ (incomingPos c) :=
  contact_black hFc (cmpDown_binary hF hσ c) heq hle1 hle2

end FLatticePaper.Contacts
