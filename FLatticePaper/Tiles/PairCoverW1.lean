import FLatticePaper.Tiles.PairOwnerP0
import FLatticePaper.Tiles.PairQAbox
import FLatticePaper.Tiles.PairQBBox
import FLatticePaper.Tiles.SiteCell

/-! Task 53, item 2 (covering reduction), section 9: the flag-true odd child (`δ = dr − ne = −1`) covers its cell.

The cell `B0 + [0,1)U + [0,1)V` of `X = P + Q` is split in the cell coordinates `(u, v)` (`α = d/D`, `β = e/D`, `α + β = 1`):

* `[0, α]²`: `P` at zero offset (`inH_box0`), the source `HSet P`;
* `[α, 1] × [0, β]`: the repeated `Q` cells at `2P` and `2P + Q`, split at `u = (1 + α)/2` (`QA_first`, `QA_second`);
* `[0, β] × [α, 1]`: the repeated `Q` cells at `V_P` and `V_P + Q`, split at `u = β/2` (`QB_first`, `QB_second`);
* `[β, 1]²`: `P` at `2Q + V_Q`. The cell reflection `z ↦ R₀ − z`, `R₀ = (d+e+n+r+1, d+e+3n+3r−1)`, sends this box to the
  zero-offset box, and `c = (d+n+1, d+3n−1)` is a centre of symmetry of the window of `P` (`refl_P`).

Points of the cell lie in one of the four boxes, so every integer point of the cell lies in `oddChildS`. -/

namespace FLatticePaper.Tiles.PairCoverW1

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteCell
open FLatticePaper.Tiles.PairOwnerP0 FLatticePaper.Tiles.PairQAbox FLatticePaper.Tiles.PairQBBox

/-- The window of `P` (odd, `μ = 2`) is symmetric about `c = (d+n+1, d+3n−1)`: `t(c) = d+n−T`, `s(c) = 2T+2n`. -/
theorem refl_P (d n : ℤ) (hodd : (d + n) % 2 = 1) (x : ℤ × ℤ) :
    InH ⟨n, d⟩ x ↔ InH ⟨n, d⟩ (d + n + 1 - x.1, d + 3 * n - 1 - x.2) := by
  have hmu : muOf ⟨n, d⟩ = 2 := by
    show (if (n + d) % 2 = 1 then 2 else 1) = 2
    rw [if_pos (by omega)]
  have ht : n * (d + n + 1 - x.1) - d * (d + 3 * n - 1 - x.2) =
      (d + n - (d ^ 2 + 2 * d * n - n ^ 2)) - (n * x.1 - d * x.2) := by
    ring
  have hs : (d + n) * (d + n + 1 - x.1) + (d - n) * (d + 3 * n - 1 - x.2) =
      2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - ((d + n) * x.1 + (d - n) * x.2) := by
    ring
  have hdec : decide (((d + n + 1 - x.1) + (d + 3 * n - 1 - x.2)) % 2 = 0) = decide ((x.1 + x.2) % 2 = 0) := by
    have : ((d + n + 1 - x.1) + (d + 3 * n - 1 - x.2)) % 2 = (x.1 + x.2) % 2 := by omega
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

/-- `z − v ∈ S` gives `z ∈ shiftS S v`. -/
theorem mem_shift {S : Set (ℤ × ℤ)} {v z : ℤ × ℤ} (h : z - v ∈ S) : z ∈ shiftS S v :=
  ⟨z - v, h, sub_add_cancel z v⟩

/-- The zero-offset box gives a point of `oddChildS`. -/
theorem memP0 (p q : Fraction) (z : ℤ × ℤ) (h : z ∈ HSet p) :
    z ∈ oddChildS true (HSet p) (HSet q) p q := by
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The copy `Q@2P` (point `z − (2d, 2n) ∈ HSet Q`). -/
theorem memQ2P (d n e r : ℤ) (z : ℤ × ℤ) (h : InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n)) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have := mem_shift (show z - texV1Odd ⟨n, d⟩ ∈ HSet ⟨r, e⟩ from h)
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The copy `Q@2P + Q`: `InH Q (z.1 − 2d − e, z.2 − 2n − r)`. -/
theorem memQ2PQ (d n e r : ℤ) (z : ℤ × ℤ) (h : InH ⟨r, e⟩ (z.1 - 2 * d - e, z.2 - 2 * n - r)) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hc : z - (texV1Odd (⟨n, d⟩ : Fraction) + texV1Even (⟨r, e⟩ : Fraction)) = (z.1 - 2 * d - e, z.2 - 2 * n - r) := by
    refine Prod.ext ?_ ?_ <;> (simp [texV1Odd, texV1Even]; try ring)
  have := mem_shift (show z - (texV1Odd ⟨n, d⟩ + texV1Even ⟨r, e⟩) ∈ HSet ⟨r, e⟩ by rw [hc]; exact h)
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The copy `Q@V_P`: `InH Q (z.1 − (n−d), z.2 − (n+d))`. -/
theorem memQVP (d n e r : ℤ) (z : ℤ × ℤ) (h : InH ⟨r, e⟩ (z.1 - (n - d), z.2 - (n + d))) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have := mem_shift (show z - texV2 ⟨n, d⟩ ∈ HSet ⟨r, e⟩ from h)
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The copy `Q@V_P + Q`: `InH Q (z.1 − (n−d) − e, z.2 − (n+d) − r)`. -/
theorem memQVPQ (d n e r : ℤ) (z : ℤ × ℤ) (h : InH ⟨r, e⟩ (z.1 - (n - d) - e, z.2 - (n + d) - r)) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hc : z - (texV2 (⟨n, d⟩ : Fraction) + texV1Even (⟨r, e⟩ : Fraction)) = (z.1 - (n - d) - e, z.2 - (n + d) - r) := by
    refine Prod.ext ?_ ?_ <;> (simp [texV2, texV1Even]; try ring)
  have := mem_shift (show z - (texV2 ⟨n, d⟩ + texV1Even ⟨r, e⟩) ∈ HSet ⟨r, e⟩ by rw [hc]; exact h)
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The copy `P@2Q + V_Q`: `InH P (z.1 − (e+r), z.2 − (e+3r))`. -/
theorem memPCE (d n e r : ℤ) (z : ℤ × ℤ) (h : InH ⟨n, d⟩ (z.1 - (e + r), z.2 - (e + 3 * r))) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
  have hc : z - (texV1Even (⟨r, e⟩ : Fraction) + texV1Even (⟨r, e⟩ : Fraction) + texV2 (⟨r, e⟩ : Fraction)) =
      (z.1 - (e + r), z.2 - (e + 3 * r)) := by
    refine Prod.ext ?_ ?_ <;> (simp [texV1Even, texV2]; try ring)
  have := mem_shift (show z - (texV1Even ⟨r, e⟩ + texV1Even ⟨r, e⟩ + texV2 ⟨r, e⟩) ∈ HSet ⟨n, d⟩ by
    rw [hc]; exact h)
  simp only [oddChildS, Set.mem_union]
  tauto

/-- The reflected point of the `P(C+E)` box lies in the zero-offset box. -/
theorem PCE_InH (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu1 : (e : ℚ) / ((d : ℚ) + e) ≤ u) (hu2 : u ≤ 1)
    (hv1 : (e : ℚ) / ((d : ℚ) + e) ≤ v) (hv2 : v ≤ 1) :
    InH ⟨n, d⟩ (z.1 - (e + r), z.2 - (e + 3 * r)) := by
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hαβ : (d : ℚ) / ((d : ℚ) + e) + (e : ℚ) / ((d : ℚ) + e) = 1 := by
    field_simp
  have hstar := inH_box0 d n e r hn hnd hr hre hdet hodd heven (d + e + n + r + 1 - z.1, d + e + 3 * n + 3 * r - 1 - z.2)
    (1 - u) (1 - v)
    (by dsimp only; push_cast; linear_combination (-1 : ℚ) * hz1)
    (by dsimp only; push_cast; linear_combination (-1 : ℚ) * hz2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine (refl_P d n hodd _).mpr ?_
  show InH ⟨n, d⟩ (d + n + 1 - (z.1 - (e + r)), d + 3 * n - 1 - (z.2 - (e + 3 * r)))
  have hpair : ((d + n + 1 - (z.1 - (e + r)), d + 3 * n - 1 - (z.2 - (e + 3 * r))) : ℤ × ℤ) =
      (d + e + n + r + 1 - z.1, d + e + 3 * n + 3 * r - 1 - z.2) := by
    refine Prod.ext ?_ ?_ <;> (dsimp only; try ring)
  rw [hpair]
  exact hstar

/-- **The flag-true odd child covers each integer point of its cell.** -/
theorem cell_in_child (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (hz : InCell (perU ⟨n + r, d + e⟩) (perV ⟨n + r, d + e⟩) z) :
    z ∈ oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ := by
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
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hDne : (d : ℚ) + e ≠ 0 := ne_of_gt hD
  have hα : α * ((d : ℚ) + e) = d := by rw [hαd]; field_simp
  have hβ : β * ((d : ℚ) + e) = e := by rw [hβd]; field_simp
  have hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r := by rw [hκd]; field_simp
  by_cases hP0 : u ≤ α ∧ v ≤ α
  · apply memP0
    exact inH_box0 d n e r hn hnd hr hre hdet hodd heven z u v hz1 hz2 hu0
      (by rw [← hαd]; exact hP0.1) hv0 (by rw [← hαd]; exact hP0.2)
  by_cases hQA : α ≤ u ∧ v ≤ β
  · by_cases hθ : u ≤ (1 + α) / 2
    · exact memQ2P d n e r z (QA_first d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ
        hQA.1 hθ hv0 hQA.2)
    · push Not at hθ
      exact memQ2PQ d n e r z (QA_second d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ
        hθ.le hu1.le hv0 hQA.2)
  by_cases hQB : u ≤ β ∧ α ≤ v
  · by_cases hθ : u ≤ β / 2
    · exact memQVP d n e r z (QB_first d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ
        hu0 hθ hQB.2 hv1.le)
    · push Not at hθ
      exact memQVPQ d n e r z (QB_second d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ
        hθ.le hQB.1 hQB.2 hv1)
  -- the remaining points lie in [β, 1]²
  have hub : β ≤ u := by
    by_contra hc
    push Not at hc
    have hv : v < α := by
      by_contra hv'
      push Not at hv'
      exact hQB ⟨hc.le, hv'⟩
    have hu : α < u := by
      by_contra hu'
      push Not at hu'
      exact hP0 ⟨hu', hv.le⟩
    have hαβ' : α < β := lt_trans hu hc
    exact hQA ⟨hu.le, (hv.trans hαβ').le⟩
  have hvb : β ≤ v := by
    by_contra hc
    push Not at hc
    have hu : u < α := by
      by_contra hu'
      push Not at hu'
      exact hQA ⟨hu', hc.le⟩
    have hv : α < v := by
      by_contra hv'
      push Not at hv'
      exact hP0 ⟨hu.le, hv'⟩
    have hαβ' : α ≤ β := by linarith
    exact hQB ⟨(hu.trans_le hαβ').le, hv.le⟩
  exact memPCE d n e r z (PCE_InH d n e r hn hnd hr hre hdet hodd heven z u v hz1 hz2
    (by rw [← hβd]; exact hub) hu1.le (by rw [← hβd]; exact hvb) hv1.le)

/-- **The flag-true odd child covers its quotient deck.** The cell reduction `SiteCell.cell_cover` applies to the
integer points of the cell, which lie in `oddChildS` by `cell_in_child`. -/
theorem propOdd_W1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    QuotientCover (oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩)
      (perU ⟨n + r, d + e⟩) (perV ⟨n + r, d + e⟩) := by
  have h0 : 0 < (⟨n + r, d + e⟩ : Fraction).num := by
    show 0 < n + r
    omega
  have h1 : (⟨n + r, d + e⟩ : Fraction).num < (⟨n + r, d + e⟩ : Fraction).den := by
    show n + r < d + e
    omega
  exact cell_cover _ _ (det_perUV _ h0 h1) _
    (fun z hz => cell_in_child d n e r hn hnd hr hre hdet hodd heven z hz)

end FLatticePaper.Tiles.PairCoverW1
