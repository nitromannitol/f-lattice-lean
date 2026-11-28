import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.TileTranslation

/-! # Constants of the pieces of a tile decomposition from local identities

Three local facts determine the constants of the pieces of the tile decompositions in Case 3 of
`lemma:tile-odometer-existence` (the closed paths through the alternate parent piece):

* a **contact**: at a point of two pieces of an odometer, the difference of their constants is the difference of the placed
  piece odometers there (`contact_diff`);
* a **doubled pair**: two copies of a register at `c` and `c + S`, the second with the extra affine factor `a`, whose difference
  is a constant `d` on their overlap; the half-turn `x ↦ 2c + D + S - x` of the doubled tile exchanges the two copies on the
  overlap, so the half-turn `o(D - y) - o(y) = e^T (D/2 - y)` of the register gives `2 d = e^T S - a^T (2c + D + S)`
  (`tau_doubled`);
* a **half-turn pair**: an odometer with the half-turn `O(D̂ - x) - O(x) = Ê^T (D̂/2 - x)`, equal to copies of a register at `g`
  and at `D̂ - D - g` (with affine factors `α`, `α'`, `Ê = e + α + α'`) plus constants `b`, `b'`, has
  `2 (b' - b) = Ê^T D̂ - e^T D - 2 e^T g - 2 α'^T D̂` (`sigma_pair`).

The half-turn identities are those of `TileHalfTurn` and `AltHalfTurn` for the unnormalised odometer, which only involve
differences of values, so the normalising constant drops out (`halfTurn_raw`, `altHalfTurn_raw`). -/

namespace FLatticePaper.Tiles.AltParentConstants

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily

/-- **A contact.** At a point of two placed pieces, the constants differ by the difference of the placed pieces. -/
theorem contact_diff (O f g : Site → ℤ) (bf bg : ℤ) (z : Site) (hf : O z = f z + bf) (hg : O z = g z + bg) :
    bg - bf = f z - g z := by
  linarith

/-- **A doubled pair**, by the half-turn of the doubled tile. -/
theorem tau_doubled (o : Site → ℤ) (T : Set Site) (D e c S α a : Site)
    (hT : ∀ y ∈ T, D - y ∈ T ∧ 2 * (o (D - y) - o y) = dotS e D - 2 * dotS e y)
    (x : Site) (hx0 : x - c ∈ T) (hx1 : x - (c + S) ∈ T) (d : ℤ)
    (hd : ∀ y, y - c ∈ T → y - (c + S) ∈ T → (o (y - c) + dotS α y) - (o (y - (c + S)) + dotS (α + a) y) = d) :
    2 * d = dotS e S - dotS a (c + c + D + S) := by
  set τ := c + c + D + S - x with hτ
  have e0 : τ - c = D - (x - (c + S)) := by rw [hτ]; abel
  have e1 : τ - (c + S) = D - (x - c) := by rw [hτ]; abel
  have h0 := hT _ hx1
  have h1 := hT _ hx0
  have hτ0 : τ - c ∈ T := by rw [e0]; exact h0.1
  have hτ1 : τ - (c + S) ∈ T := by rw [e1]; exact h1.1
  have dx := hd x hx0 hx1
  have dτ := hd τ hτ0 hτ1
  rw [e0, e1] at dτ
  have hxs : x - (c + S) = (x - c) - S := by abel
  rw [hxs] at h0 dx
  rw [hxs] at dτ
  have hτx : τ = c + c + D + S - x := hτ
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hτx] at dx dτ h0 h1 ⊢
  nlinarith [h0.2, h1.2, dx, dτ]

/-- **A half-turn pair** of pieces of an odometer with a half-turn. -/
theorem sigma_pair (O o : Site → ℤ) (T : Set Site) (Dh E D e g α α' : Site) (b b' : ℤ)
    (hO : ∀ x, x - g ∈ T → 2 * (O (Dh - x) - O x) = dotS E Dh - 2 * dotS E x)
    (hT : ∀ y ∈ T, D - y ∈ T ∧ 2 * (o (D - y) - o y) = dotS e D - 2 * dotS e y)
    (hk : ∀ x, x - g ∈ T → O x = o (x - g) + dotS α x + b)
    (hpk : ∀ x, x - (Dh - D - g) ∈ T → O x = o (x - (Dh - D - g)) + dotS α' x + b')
    (hE : E = e + α + α') (x : Site) (hx : x - g ∈ T) :
    2 * (b' - b) = dotS E Dh - dotS e D - 2 * dotS e g - 2 * dotS α' Dh := by
  have hy := hT _ hx
  have e0 : Dh - x - (Dh - D - g) = D - (x - g) := by abel
  have h1 := hpk (Dh - x) (by rw [e0]; exact hy.1)
  rw [e0] at h1
  have h2 := hk x hx
  have h3 := hO x hx
  rw [h1, h2] at h3
  have h4 := hy.2
  rw [hE] at h3 ⊢
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h3 h4 ⊢
  nlinarith [h3, h4]

/-! ### The half-turns of the unnormalised odometers -/

theorem normed_diff (o : PartialOdometer) (α : Site) (β : ℤ) (x y : Site) :
    normed o α β x - normed o α β y = o.val x - o.val y - (dotS α x - dotS α y) := by
  unfold normed
  ring

/-- `TileHalfTurn` at slope zero, for the odometer itself. -/
theorem halfTurn_raw (o : PartialOdometer) (v1 v2 a2 : Site) (h : TileHalfTurn o v1 v2 a2) (hz : JointRot.SlopeZero o) :
    ∀ y ∈ (↑o.dom : Set Site), (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - y ∈ (↑o.dom : Set Site) ∧
      2 * (o.val ((v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - y) - o.val y) =
        dotS a2 (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS a2 y := by
  obtain ⟨α, β, hn, hh⟩ := h
  obtain ⟨β', hn'⟩ := hz
  obtain ⟨rfl, -⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hn hn'
  intro y hy
  obtain ⟨h1, h2⟩ := hh y hy
  refine ⟨h1, ?_⟩
  rw [normed_diff] at h2
  simpa [dotS] using h2

/-- `AltHalfTurn` at slope zero, for the odometer itself. -/
theorem altHalfTurn_raw (o : PartialOdometer) (Dh E : Site) (h : AltHalfTurn o Dh E) (hz : JointRot.SlopeZero o) :
    ∀ x ∈ (↑o.dom : Set Site), Dh - x ∈ (↑o.dom : Set Site) ∧ 2 * (o.val (Dh - x) - o.val x) = dotS E Dh - 2 * dotS E x := by
  obtain ⟨α, β, hn, hh⟩ := h
  obtain ⟨β', hn'⟩ := hz
  obtain ⟨rfl, -⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hn hn'
  intro x hx
  obtain ⟨h1, h2⟩ := hh x hx
  refine ⟨h1, ?_⟩
  rw [normed_diff] at h2
  simpa [dotS] using h2

/-- **A doubled pair, in the form of the shift constant**: if `o(x + S) - o(x) - a^T x = k` wherever `x, x + S` lie in the tile,
and the tile meets its translate by `S`, then `2 k = e^T S + a^T S - a^T D`. -/
theorem tau_shift (o : Site → ℤ) (T : Set Site) (D e S a : Site)
    (hT : ∀ y ∈ T, D - y ∈ T ∧ 2 * (o (D - y) - o y) = dotS e D - 2 * dotS e y) (k : ℤ)
    (hk : ∀ x, x ∈ T → x + S ∈ T → o (x + S) - o x - dotS a x = k) (x : Site) (hx : x ∈ T) (hxS : x + S ∈ T) :
    2 * k = dotS e S + dotS a S - dotS a D := by
  have h1 := hT x hx
  have h2 := hT (x + S) hxS
  have ey : D - (x + S) + S = D - x := by abel
  have hy := hk (D - (x + S)) h2.1 (by rw [ey]; exact h1.1)
  rw [ey] at hy
  have hx' := hk x hx hxS
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h1 h2 hy hx' ⊢
  nlinarith [h1.2, h2.2, hy, hx']

/-- The corner values of `StdCornerValues` at slope zero, for the odometer itself. -/
theorem corner_raw (o : PartialOdometer) (β : ℤ) (X Y e : Site) (h : TileTranslation.StdCornerValues o 0 β X Y e) :
    o.val 0 = β ∧ o.val (1, 0) = β ∧ o.val (X - (0, 1)) = β ∧ o.val X = β ∧
      o.val (Y + (1, 0)) = -h0 Y + e.1 + β ∧ o.val (Y + (1, -1)) = -h0 Y + e.1 - e.2 + β ∧
      o.val (X + Y + (1, -1)) = -h0 Y + e.1 - e.2 + β ∧ o.val (X + Y + (1, -1) - (1, 0)) = -h0 Y - e.2 + β := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩, ⟨-, h4⟩, ⟨-, h5⟩, ⟨-, h6⟩, ⟨-, h7⟩, ⟨-, h8⟩⟩ := h
  simp only [normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end FLatticePaper.Tiles.AltParentConstants
