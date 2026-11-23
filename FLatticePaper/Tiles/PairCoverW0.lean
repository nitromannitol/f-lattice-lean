import FLatticePaper.Tiles.PairW0P
import FLatticePaper.Tiles.PairW0Q
import FLatticePaper.Tiles.PairCoverW1

/-! Task 53, item 2 (covering reduction), section 12: the flag-false odd child (W0, `δ = dr − ne = +1`) covers its cell.

The cell of `X = P + Q` is split (`α = d/D`, `β = e/D`, `α + β = 1`) into four boxes in the cell coordinates `(u, v)`, with the
sources of `oddChildS false`:

* `[0, β]²`: `Q@0` (the point `z`) or `Q@Q` (the point `z − (e, r)`), by the integer test of `PairW0Q.Q0_cover`;
* `[α, 1]²`: the reflection `z ↦ R₀ − z`, `R₀ = (d+e+n+r+1, d+e+3n+3r−1)`, of the `Q0` box. The window of `Q` is symmetric about
  `c = (r+1, e+2r−1)` (`refl_Q`), with `c + (2P+V_P+Q) = R₀` and `c + (2P+V_P) = R₀ − Q`;
* `[β, 1] × [0, α]`: `P@2Q`, the reflection of the `P@V_Q` box (`PairW0P.PVQ_box_W0`) under `R₀ − z` (`PairCoverW1.refl_P`);
* `[0, α] × [β, 1]`: `P@V_Q` (`PairW0P.PVQ_box_W0`). -/

namespace FLatticePaper.Tiles.PairCoverW0

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteCell
open FLatticePaper.Tiles.PairW0P FLatticePaper.Tiles.PairW0Q FLatticePaper.Tiles.PairCoverW1

/-- Equal points give equivalent `InH` statements. -/
theorem InH_congr (f : Fraction) {x y : ℤ × ℤ} (h : x = y) : InH f x ↔ InH f y := by
  rw [h]

/-- The window of `Q` (even, `μ = 1`) is symmetric about `c = (r+1, e+2r−1)`. -/
theorem refl_Q (r e : ℤ) (heven : (e + r) % 2 = 0) (x : ℤ × ℤ) :
    InH ⟨r, e⟩ x ↔ InH ⟨r, e⟩ (r + 1 - x.1, e + 2 * r - 1 - x.2) := by
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  have ht : r * (r + 1 - x.1) - e * (e + 2 * r - 1 - x.2) =
      (e + r - (e ^ 2 + 2 * e * r - r ^ 2)) - (r * x.1 - e * x.2) := by
    ring
  have hs : (e + r) * (r + 1 - x.1) + (e - r) * (e + 2 * r - 1 - x.2) =
      (e ^ 2 + 2 * e * r - r ^ 2 + 2 * r) - ((e + r) * x.1 + (e - r) * x.2) := by
    ring
  have hdec : decide (((r + 1 - x.1) + (e + 2 * r - 1 - x.2)) % 2 = 0) = decide ((x.1 + x.2) % 2 = 0) := by
    have : ((r + 1 - x.1) + (e + 2 * r - 1 - x.2)) % 2 = (x.1 + x.2) % 2 := by omega
    rw [this]
  unfold InH
  dsimp only
  rw [hdec, hmu]
  simp only [tOf, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The cell reflection: the coordinates of `R₀ − z` are `(1 − u, 1 − v)`. -/
theorem refl_cell (d n e r : ℤ) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    ((d + e + n + r + 1 - z.1 : ℤ) : ℚ) - 1 / 2 =
        (1 - u) * (2 * ((d : ℚ) + e)) + (1 - v) * ((n : ℚ) + r - ((d : ℚ) + e)) ∧
    ((d + e + 3 * n + 3 * r - 1 - z.2 : ℤ) : ℚ) + 1 / 2 =
        (1 - u) * (2 * ((n : ℚ) + r)) + (1 - v) * ((d : ℚ) + e + ((n : ℚ) + r)) := by
  constructor
  · push_cast; linear_combination (-1 : ℚ) * hz1
  · push_cast; linear_combination (-1 : ℚ) * hz2

/-- The four boxes cover the unit square when `α + β = 1`. -/
theorem cover4 (u v α β : ℚ) :
    (u ≤ β ∧ v ≤ β) ∨ (α ≤ u ∧ α ≤ v) ∨ (β ≤ u ∧ v ≤ α) ∨ (u ≤ α ∧ β ≤ v) := by
  rcases le_total u β with h1 | h1 <;> rcases le_total v β with h2 | h2 <;>
    rcases le_total u α with h3 | h3 <;> rcases le_total v α with h4 | h4 <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-- The `Q`-copies over `[α, 1]²`: `z − (d+n+e, 3n+d+r)` or `z − (d+n, 3n+d)` lies in `HSet Q`. -/
theorem QAB_InH (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hαβ : α + β = 1) (hu1 : α ≤ u) (hu2 : u ≤ 1) (hv1 : α ≤ v) (hv2 : v ≤ 1) :
    InH ⟨r, e⟩ (z.1 - (d + n + e), z.2 - (3 * n + d + r)) ∨ InH ⟨r, e⟩ (z.1 - (d + n), z.2 - (3 * n + d)) := by
  obtain ⟨hc1, hc2⟩ := refl_cell d n e r z u v hz1 hz2
  have hβ0 : 0 ≤ β := by linarith
  have hQ0 := Q0_cover d n e r hn hnd hr hre hdet hodd heven (d + e + n + r + 1 - z.1, d + e + 3 * n + 3 * r - 1 - z.2)
    α β κ (1 - u) (1 - v) hc1 hc2 hα hβ hκ (by linarith) (by linarith) (by linarith) (by linarith)
  have hS1 : ((r + 1 - (z.1 - (d + n + e)), e + 2 * r - 1 - (z.2 - (3 * n + d + r))) : ℤ × ℤ) =
      (d + e + n + r + 1 - z.1, d + e + 3 * n + 3 * r - 1 - z.2) := by
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  have hS2 : ((r + 1 - (z.1 - (d + n)), e + 2 * r - 1 - (z.2 - (3 * n + d))) : ℤ × ℤ) =
      (d + e + n + r + 1 - z.1 - e, d + e + 3 * n + 3 * r - 1 - z.2 - r) := by
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  rcases hQ0 with h | h
  · left
    exact (refl_Q r e heven (z.1 - (d + n + e), z.2 - (3 * n + d + r))).mpr ((InH_congr ⟨r, e⟩ hS1).mpr h)
  · right
    exact (refl_Q r e heven (z.1 - (d + n), z.2 - (3 * n + d))).mpr ((InH_congr ⟨r, e⟩ hS2).mpr h)

/-- The `P`-copy `P@2Q` over `[β, 1] × [0, α]`: `z − (2e, 2r) ∈ HSet P`. -/
theorem P2Q_InH (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hαβ : α + β = 1) (hu1 : β ≤ u) (hu2 : u ≤ 1) (hv1 : 0 ≤ v) (hv2 : v ≤ α) :
    InH ⟨n, d⟩ (z.1 - 2 * e, z.2 - 2 * r) := by
  obtain ⟨hc1, hc2⟩ := refl_cell d n e r z u v hz1 hz2
  have hP := PVQ_box_W0 d n e r hn hnd hr hre hdet hodd heven
    (d + e + n + r + 1 - z.1, d + e + 3 * n + 3 * r - 1 - z.2) α β κ (1 - u) (1 - v) hc1 hc2 hα hβ hκ
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hpair : ((d + n + 1 - (z.1 - 2 * e), d + 3 * n - 1 - (z.2 - 2 * r)) : ℤ × ℤ) =
      (d + e + n + r + 1 - z.1 - (r - e), d + e + 3 * n + 3 * r - 1 - z.2 - (r + e)) := by
    refine Prod.ext ?_ ?_ <;> dsimp only <;> ring
  exact (refl_P d n hodd (z.1 - 2 * e, z.2 - 2 * r)).mpr ((InH_congr ⟨n, d⟩ hpair).mpr hP)

/-- The `P`-copy `P@V_Q` over `[0, α] × [β, 1]`: `z − (r − e, r + e) ∈ HSet P`. -/
theorem PVQ_InH (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) :
    InH ⟨n, d⟩ (z.1 - (r - e), z.2 - (r + e)) :=
  PVQ_box_W0 d n e r hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1

/-! The memberships in `oddChildS false` (the six sources of the flag-false child). -/

theorem memF_Q0 (p q : Fraction) (z : ℤ × ℤ) (h : z ∈ HSet q) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  simp only [oddChildS, Set.mem_union]
  tauto

theorem memF_QQ (p q : Fraction) (z : ℤ × ℤ) (h : z - texV1Even q ∈ HSet q) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  have := mem_shift h
  simp only [oddChildS, Set.mem_union]
  tauto

theorem memF_QAB (p q : Fraction) (z : ℤ × ℤ) (h : z - (texV1Odd p + texV2 p + texV1Even q) ∈ HSet q) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  have := mem_shift h
  simp only [oddChildS, Set.mem_union]
  tauto

theorem memF_QAB' (p q : Fraction) (z : ℤ × ℤ) (h : z - (texV1Odd p + texV2 p) ∈ HSet q) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  have := mem_shift h
  simp only [oddChildS, Set.mem_union]
  tauto

theorem memF_P2Q (p q : Fraction) (z : ℤ × ℤ) (h : z - (texV1Even q + texV1Even q) ∈ HSet p) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  have := mem_shift h
  simp only [oddChildS, Set.mem_union]
  tauto

theorem memF_PVQ (p q : Fraction) (z : ℤ × ℤ) (h : z - texV2 q ∈ HSet p) :
    z ∈ oddChildS false (HSet p) (HSet q) p q := by
  have := mem_shift h
  simp only [oddChildS, Set.mem_union]
  tauto

/-- **The flag-false odd child covers each integer point of its cell.** -/
theorem cell_in_child_W0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (hz : InCell (perU ⟨n + r, d + e⟩) (perV ⟨n + r, d + e⟩) z) :
    z ∈ oddChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hmuX : muOf ⟨n + r, d + e⟩ = 2 := by
    show (if (n + r + (d + e)) % 2 = 1 then 2 else 1) = 2
    rw [if_pos (by omega)]
  have hU : perU ⟨n + r, d + e⟩ = (2 * (d + e), 2 * (n + r)) := by
    unfold perU; rw [hmuX]
  have hV : perV ⟨n + r, d + e⟩ = (n + r - (d + e), d + e + (n + r)) := by
    unfold perV; rfl
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hz1, hz2⟩ := hz
  rw [hU, hV] at hz1 hz2
  dsimp only at hz1 hz2
  push_cast at hz1 hz2
  obtain ⟨α, hαd⟩ : ∃ α : ℚ, α = (d : ℚ) / ((d : ℚ) + e) := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℚ, β = (e : ℚ) / ((d : ℚ) + e) := ⟨_, rfl⟩
  obtain ⟨κ, hκd⟩ : ∃ κ : ℚ, κ = ((e : ℚ) - r) / ((d : ℚ) + e) := ⟨_, rfl⟩
  obtain ⟨κP, hκPd⟩ : ∃ κP : ℚ, κP = ((d : ℚ) - n) / ((d : ℚ) + e) := ⟨_, rfl⟩
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hDne : (d : ℚ) + e ≠ 0 := ne_of_gt hD
  have hα : α * ((d : ℚ) + e) = d := by rw [hαd]; field_simp
  have hβ : β * ((d : ℚ) + e) = e := by rw [hβd]; field_simp
  have hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r := by rw [hκd]; field_simp
  have hκP : κP * ((d : ℚ) + e) = (d : ℚ) - n := by rw [hκPd]; field_simp
  have hαβ : α + β = 1 := by
    have : (α + β) * ((d : ℚ) + e) = 1 * ((d : ℚ) + e) := by linear_combination hα + hβ
    exact mul_right_cancel₀ hDne this
  have hu1' : u ≤ 1 := hu1.le
  have hv1' : v ≤ 1 := hv1.le
  rcases cover4 u v α β with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases Q0_cover d n e r hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hu0 h1 hv0 h2 with h | h
    · exact memF_Q0 ⟨n, d⟩ ⟨r, e⟩ z h
    · exact memF_QQ ⟨n, d⟩ ⟨r, e⟩ z h
  · rcases QAB_InH d n e r hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hαβ h1 hu1' h2 hv1' with h | h
    · apply memF_QAB
      have hp : z - (texV1Odd (⟨n, d⟩ : Fraction) + texV2 (⟨n, d⟩ : Fraction) + texV1Even (⟨r, e⟩ : Fraction)) =
          (z.1 - (d + n + e), z.2 - (3 * n + d + r)) := by
        refine Prod.ext ?_ ?_ <;> simp [texV1Odd, texV2, texV1Even] <;> ring
      rw [hp]; exact h
    · apply memF_QAB'
      have hp : z - (texV1Odd (⟨n, d⟩ : Fraction) + texV2 (⟨n, d⟩ : Fraction)) = (z.1 - (d + n), z.2 - (3 * n + d)) := by
        refine Prod.ext ?_ ?_ <;> simp [texV1Odd, texV2] <;> ring
      rw [hp]; exact h
  · apply memF_P2Q
    have hp : z - (texV1Even (⟨r, e⟩ : Fraction) + texV1Even (⟨r, e⟩ : Fraction)) = (z.1 - 2 * e, z.2 - 2 * r) := by
      refine Prod.ext ?_ ?_ <;> simp [texV1Even] <;> ring
    rw [hp]
    exact P2Q_InH d n e r hn hnd hr hre hdet hodd heven z α β κP u v hz1 hz2 hα hβ hκP hαβ h1 hu1' hv0 h2
  · apply memF_PVQ
    have hp : z - texV2 (⟨r, e⟩ : Fraction) = (z.1 - (r - e), z.2 - (r + e)) := by
      refine Prod.ext ?_ ?_ <;> simp [texV2]
    rw [hp]
    exact PVQ_InH d n e r hn hnd hr hre hdet hodd heven z α β κP u v hz1 hz2 hα hβ hκP hu0 h1 h2 hv1'

/-- **The flag-false odd child covers its quotient deck** (`SiteCell.cell_cover`). -/
theorem propOdd_W0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (oddChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ⟨n + r, d + e⟩) (perV ⟨n + r, d + e⟩) := by
  have h0 : 0 < (⟨n + r, d + e⟩ : Fraction).num := by
    show 0 < n + r
    omega
  have h1 : (⟨n + r, d + e⟩ : Fraction).num < (⟨n + r, d + e⟩ : Fraction).den := by
    show n + r < d + e
    omega
  exact cell_cover _ _ (det_perUV _ h0 h1) _
    (fun z hz => cell_in_child_W0 d n e r hn hnd hr hre hdet hodd heven z hz)

end FLatticePaper.Tiles.PairCoverW0
