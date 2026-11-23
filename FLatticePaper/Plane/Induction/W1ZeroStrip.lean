import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.W1Lower

/-! Task 59, step 1 and step 2 (the zero fields at a general word).

For a child frame with child `n/d` (both odd), write `Nu = (d − n)/2` and `Du = (d + n)/2` (these are the values of
`parentN`, `parentD` of the word whose standard field is the frame's own field). Put `Z x = (−x₂, x₁ − 1)` and `y = Z x`.
Then `quarterTurnField F x = F y − h₀ y` (`harmonicGrid_quarter_inv`), and the parent band of `x` is a band of the child's
s-grade of `y`:

  `2 · (Nu x₁ − Du x₂) = s(y) + (d − n)`,  so  `s(y) = 2 τ − 2 Nu` with `τ = Nu x₁ − Du x₂`.

* `1 − Du ≤ τ ≤ Nu + 2Du − 1` gives `1 − 2d ≤ s(y) ≤ 2L − 1`, the ordinary h₀ strip of `HasStrips` (second clause). So the
  zero strip field is the packet's ordinary strip, with no further input.
* `τ = −Du` (the even line, `x` even) gives `s(y) = −2d` on odd sites, and `τ = 1 − d` (the odd seed) gives `s(y) = 2 − 3d + n`:
  both lie in the odd lower extension `[2 − 3d + n, 1 − 2d]`, which is the input `hlow`.
* The sandwich `h(s) ≤ h(s − 2)` on the odd fibre, with `h = 0` at both ends, forces `h = 0` between the ends (`sandwich_zero`).
-/

namespace FLatticePaper.W1ZeroStrip

open Farey FLatticePaper FLatticePaper.Induction

/-- The quarter turn of `F` at `x` is `F(y) − h₀(y)` with `y = Z x` (the identity `h₀(x) = −h₀(Z x)`). -/
theorem quarterTurn_eq_sub (F : Field) (x : Site) :
    quarterTurnField F x = F (-x.2, x.1 - 1) - harmonicGrid (-x.2, x.1 - 1) := by
  have hx1 : (-x.2, x.1 - 1).2 + 1 = x.1 := by simp
  have hx2 : -(-x.2, x.1 - 1).1 = x.2 := by simp
  have hq := FLatticePaper.W1Seeds.harmonicGrid_quarter_inv (-x.2, x.1 - 1)
  rw [hx1, hx2, Prod.mk.eta] at hq
  unfold quarterTurnField
  rw [quarterTurn_site, hq]
  ring

/-- The s-grade of `Z x` in terms of `τ = Nu x₁ − Du x₂`, for odd `n`, `d`. -/
theorem sGrade_Z (frame : ChildFrame) (x : Site) (Nu Du : ℤ)
    (hNu : 2 * Nu = frame.child.den - frame.child.num) (hDu : 2 * Du = frame.child.den + frame.child.num) :
    frame.sGrade (-x.2, x.1 - 1) = 2 * (Nu * x.1 - Du * x.2) - (frame.child.den - frame.child.num) := by
  unfold ChildFrame.sGrade
  linear_combination x.2 * hDu - x.1 * hNu

/-- The zero of the quarter turn at `x` follows from `F = h₀` at `Z x`. -/
theorem quarterTurn_zero_of_harmonic (F : Field) (x : Site)
    (h : F (-x.2, x.1 - 1) = harmonicGrid (-x.2, x.1 - 1)) : quarterTurnField F x = 0 := by
  rw [quarterTurn_eq_sub, h, sub_self]

/-- **The zero strip of the quarter turn** from the ordinary h₀ strip of the packet (the second clause of `HasStrips`). -/
theorem zeroStrip_of_strips (frame : ChildFrame) {F : Field} (hstrips : frame.HasStrips F) (x : Site)
    (h1 : 1 - (frame.child.den + frame.child.num) / 2 ≤
      (frame.child.den - frame.child.num) / 2 * x.1 - (frame.child.den + frame.child.num) / 2 * x.2)
    (h2 : (frame.child.den - frame.child.num) / 2 * x.1 - (frame.child.den + frame.child.num) / 2 * x.2 ≤
      (frame.child.den - frame.child.num) / 2 + 2 * ((frame.child.den + frame.child.num) / 2) - 1) :
    quarterTurnField F x = 0 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  obtain ⟨Nu, hNuDef⟩ : ∃ Nu, Nu = (frame.child.den - frame.child.num) / 2 := ⟨_, rfl⟩
  obtain ⟨Du, hDuDef⟩ : ∃ Du, Du = (frame.child.den + frame.child.num) / 2 := ⟨_, rfl⟩
  have hNu : 2 * Nu = frame.child.den - frame.child.num := by rw [hNuDef]; omega
  have hDu : 2 * Du = frame.child.den + frame.child.num := by rw [hDuDef]; omega
  rw [← hNuDef, ← hDuDef] at h1 h2
  obtain ⟨τ, hτ⟩ : ∃ τ, Nu * x.1 - Du * x.2 = τ := ⟨_, rfl⟩
  rw [hτ] at h1 h2
  have hsy : frame.sGrade (-x.2, x.1 - 1) = 2 * τ - (frame.child.den - frame.child.num) := by
    rw [sGrade_Z frame x Nu Du hNu hDu, hτ]
  apply quarterTurn_zero_of_harmonic
  apply hstrips.2
  · rw [hsy]; omega
  · rw [hsy]; omega

/-- The packet of a standard field gives the zero strip field of `StrongEstimates` at `u`. -/
theorem zeroStripInterval_of_packet (u : Word) (hP : (frameAt u).Packet (standardField u)) :
    ∀ x : Site,
      1 - parentD u ≤ parentN u * x.1 - parentD u * x.2 →
        parentN u * x.1 - parentD u * x.2 ≤ parentN u + 2 * parentD u - 1 →
          quarterTurnField (standardField u) x = 0 :=
  fun x h1 h2 => zeroStrip_of_strips (frameAt u) hP.strips x h1 h2

/-- The sandwich: if `h` does not increase along the odd fibre (`h(s + 2) ≤ h(s)`) and vanishes at both ends, it vanishes
between them. This is the mechanism of `NO_ODD_SLIP_AUDIT` §3: it fills the interval from its two endpoints. -/
theorem sandwich_zero (h : ℤ → ℤ) (a b : ℤ) (hstep : ∀ s, a ≤ s → s + 2 ≤ b → h (s + 2) ≤ h s)
    (ha : h a = 0) (hb : h b = 0) (hab : (b - a) % 2 = 0) (s : ℤ) (hs : a ≤ s) (hsb : s ≤ b)
    (hpar : (s - a) % 2 = 0) : h s = 0 := by
  have mono : ∀ j : ℕ, ∀ t : ℤ, a ≤ t → t + 2 * (j : ℤ) ≤ b → h (t + 2 * (j : ℤ)) ≤ h t := by
    intro j
    induction j with
    | zero => intro t _ _; simp
    | succ j ih =>
      intro t ht htj
      have hj : t + 2 * (j : ℤ) + 2 ≤ b := by push_cast at htj; omega
      have h1 := ih t ht (by omega)
      have h2 := hstep (t + 2 * (j : ℤ)) (by omega) hj
      have e : t + 2 * ((j + 1 : ℕ) : ℤ) = t + 2 * (j : ℤ) + 2 := by push_cast; ring
      rw [e]
      omega
  have hsa : h s ≤ h a := by
    obtain ⟨j, hj⟩ : ∃ j : ℕ, s = a + 2 * (j : ℤ) := ⟨((s - a) / 2).toNat, by omega⟩
    have := mono j a le_rfl (by omega)
    rw [← hj] at this
    exact this
  have hbs : h b ≤ h s := by
    obtain ⟨j, hj⟩ : ∃ j : ℕ, b = s + 2 * (j : ℤ) := ⟨((b - s) / 2).toNat, by omega⟩
    have := mono j s (by omega) (by omega)
    rw [← hj] at this
    exact this
  omega

/-- The even line `t_p = −D` (`x` even) is the point `s(Z x) = −2d` on odd sites, inside the odd lower extension. -/
theorem zeroEvenLine_of_lower (frame : ChildFrame) {F : Field} (hlt : frame.child.num < frame.child.den)
    (hlow : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 1 - 2 * frame.child.den → F z = harmonicGrid z)
    (x : Site) (hx : EvenSite x)
    (hline : (frame.child.den - frame.child.num) / 2 * x.1 - (frame.child.den + frame.child.num) / 2 * x.2 =
      -((frame.child.den + frame.child.num) / 2)) :
    quarterTurnField F x = 0 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  obtain ⟨Nu, hNuDef⟩ : ∃ Nu, Nu = (frame.child.den - frame.child.num) / 2 := ⟨_, rfl⟩
  obtain ⟨Du, hDuDef⟩ : ∃ Du, Du = (frame.child.den + frame.child.num) / 2 := ⟨_, rfl⟩
  have hNu : 2 * Nu = frame.child.den - frame.child.num := by rw [hNuDef]; omega
  have hDu : 2 * Du = frame.child.den + frame.child.num := by rw [hDuDef]; omega
  rw [← hNuDef, ← hDuDef] at hline
  apply quarterTurn_zero_of_harmonic
  apply hlow
  · -- `Z x` is an odd site when `x` is even
    unfold EvenSite at hx ⊢
    simp only at hx ⊢
    omega
  · rw [sGrade_Z frame x Nu Du hNu hDu]
    rw [hline]
    omega
  · rw [sGrade_Z frame x Nu Du hNu hDu]
    rw [hline]
    omega

/-- The seed `odd_zero` (the even line `τ = 1 − d`) is the lower endpoint `s = 2 − 3d + n` of the odd extension. -/
theorem odd_zero_of_lower (frame : ChildFrame) {F : Field} (hlt : frame.child.num < frame.child.den)
    (hlow : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 1 - 2 * frame.child.den → F z = harmonicGrid z)
    (x : Site) (hx : EvenSite x)
    (hseed : (frame.child.den - frame.child.num) / 2 * x.1 - (frame.child.den + frame.child.num) / 2 * x.2 =
      1 - (frame.child.den + frame.child.num) / 2 - (frame.child.den - frame.child.num) / 2) :
    quarterTurnField F x = 0 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  obtain ⟨Nu, hNuDef⟩ : ∃ Nu, Nu = (frame.child.den - frame.child.num) / 2 := ⟨_, rfl⟩
  obtain ⟨Du, hDuDef⟩ : ∃ Du, Du = (frame.child.den + frame.child.num) / 2 := ⟨_, rfl⟩
  have hNu : 2 * Nu = frame.child.den - frame.child.num := by rw [hNuDef]; omega
  have hDu : 2 * Du = frame.child.den + frame.child.num := by rw [hDuDef]; omega
  rw [← hNuDef, ← hDuDef] at hseed
  apply quarterTurn_zero_of_harmonic
  apply hlow
  · unfold EvenSite at hx ⊢
    simp only at hx ⊢
    omega
  · rw [sGrade_Z frame x Nu Du hNu hDu]
    rw [hseed]
    omega
  · rw [sGrade_Z frame x Nu Du hNu hDu]
    rw [hseed]
    omega

/-- The even line from the price chain: the odd lower extension `hlow` is `lower_odd_h0`, which uses the price range, the two
drifts, the packet strips and the odd seed `hseed`. So the even line is produced from `priceRange`, the drifts and the seed. -/
theorem zeroEvenLine_of_price (frame : ChildFrame) {F : Field} (hlt : frame.child.num < frame.child.den)
    (hstrips : frame.HasStrips F)
    (hPR : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice)
    (hPU : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z - 1)
    (hPV : ∀ z, frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z)
    (hseed : ∀ w : Site, ¬ EvenSite w → frame.sGrade w = 2 - 3 * frame.child.den + frame.child.num →
      F w = harmonicGrid w)
    (x : Site) (hx : EvenSite x)
    (hline : (frame.child.den - frame.child.num) / 2 * x.1 - (frame.child.den + frame.child.num) / 2 * x.2 =
      -((frame.child.den + frame.child.num) / 2)) :
    quarterTurnField F x = 0 :=
  zeroEvenLine_of_lower frame hlt
    (fun z hz h1 h2 => FLatticePaper.W1Lower.lower_odd_h0 frame hstrips hPR hPU hPV hseed z hz h1 h2) x hx hline


/-- The `zeroEvenLine` field of `StrongEstimates u`, from the packet of `u`, the price range and drifts of `u`, and the odd seed
of `u` (the inputs of `zeroEvenLine_of_price`). -/
theorem zeroEvenLine_field (u : Word) (hP : (frameAt u).Packet (standardField u))
    (hPR : ∀ z ∈ (frameAt u).closedPolygon,
      (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) z ∧
        (frameAt u).price (standardField u) z ≤ (frameAt u).cutPrice)
    (hPU : ∀ z, (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.kernel) =
      (frameAt u).price (standardField u) z - 1)
    (hPV : ∀ z, (frameAt u).price (standardField u) (z + (frameAt u).child.modifiedDeck.transverse) =
      (frameAt u).price (standardField u) z)
    (hseed : ∀ w : Site, ¬ EvenSite w → (frameAt u).sGrade w = 2 - 3 * (frameAt u).child.den + (frameAt u).child.num →
      standardField u w = harmonicGrid w) :
    ∀ x : Site, (x.1 + x.2) % 2 = 0 →
      parentN u * x.1 - parentD u * x.2 = -parentD u → quarterTurnField (standardField u) x = 0 :=
  fun x hx hline =>
    zeroEvenLine_of_price (frameAt u) (frameAt u).child_facts.2.1 hP.strips hPR hPU hPV hseed x hx hline

end FLatticePaper.W1ZeroStrip
