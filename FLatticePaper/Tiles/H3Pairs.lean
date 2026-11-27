import FLatticePaper.Tiles.H3Data
import FLatticePaper.Tiles.H3Bounds
import FLatticePaper.Tiles.CellRegisters

/-! (H3) of item (d) of `lemma:standard_tile_properties`: in the standard decomposition of a non-base standard tile, no cell
lies in a copy of the odd parent tile `T(p₁)` and in a copy of the even parent tile `T(q₁)` (`cellsDisjointOdd` for the odd
child, `cellsDisjointEven` for the even child, in the form `CellRegisters.CellsDisjointOdd` and `CellsDisjointEven` of the
consumers).

The proof follows steps 2-4 of the text. For a pair of copies `X = T(r) + a`, `Y = T(r') + b` sharing a cell `s`, the corner
`s + 1` lies in `X` and `s + i` in `Y`, and `Λ₀ = d₀ y - n₀ x` increases by `d₀ + n₀` from the first to the second; so the pair
shares no cell once `max_Y Λ₀ - min_X Λ₀ < d₀ + n₀` (`lam_sep`). The minimum over a copy is attained on its bottom walk and the
maximum on its top side (`CellExtremes`), and on the bottom walks `Λ₀` is bounded below by the arithmetic of step 4
(`H3Bounds.bound_LP`, `bound_LQ`), with property (ii) of the text taken from the closed form of the tile (`H3Data`).

Two points differ from the text.
* Property (ii) is not carried along the induction: it holds on the whole standard tile by its closed form
  (`H3Data.lam_bound_odd`, `lam_bound_even`).
* The four same-sign pairs are not mapped to opposite-sign pairs by the quarter turn of step 5. They are separated directly by
  the vertical functional `S₀ = (d₀ + n₀) x + (d₀ - n₀) y`: the corner `s` lies in the right copy and `s + 1 + i` in the left
  copy, `S₀` increases by `2 d₀` between them (`sig_sep`), its minimum over a copy is on the left side and its maximum on the
  right side (`CellExtremes`), and on the right walks it is bounded by `H3Bounds.bound_SP`, `bound_SQ`, from the slope bound of
  the closed form. These are the bounds of step 4 for the rotated quadruple, written in the unrotated coordinates.

For each of the eight pairs of each child and phase, one of the two functionals separates the pair; the final inequality is
linear in `n₀, d₀` once the determinant is used, with `n₀ ≥ c + 1` and `d₀ - n₀ ≥ c + 1` (and `d₀ - n₀ ≥ 4` for the even child
by parity). -/

namespace FLatticePaper.Tiles.H3Pairs

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.SiteInduction
  FLatticePaper.Tiles.RecursionIdentity FLatticePaper.Tiles.CellRegisters FLatticePaper.Tiles.H3Bounds
  FLatticePaper.Tiles.MixedPieces

/-- The functional `Λ₀ = d₀ y - n₀ x`. -/
def lam (n0 d0 : ℤ) (z : GInt) : ℤ := d0 * z.2 - n0 * z.1

/-- The functional `S₀ = (d₀ + n₀) x + (d₀ - n₀) y`. -/
def sig (n0 d0 : ℤ) (z : GInt) : ℤ := (d0 + n0) * z.1 + (d0 - n0) * z.2

theorem lam_add (n0 d0 : ℤ) (u v : GInt) : lam n0 d0 (u + v) = lam n0 d0 u + lam n0 d0 v := by
  unfold lam; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem lam_sub (n0 d0 : ℤ) (u v : GInt) : lam n0 d0 (u - v) = lam n0 d0 u - lam n0 d0 v := by
  unfold lam; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem lam_zero (n0 d0 : ℤ) : lam n0 d0 0 = 0 := by
  unfold lam; simp

theorem sig_add (n0 d0 : ℤ) (u v : GInt) : sig n0 d0 (u + v) = sig n0 d0 u + sig n0 d0 v := by
  unfold sig; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sig_sub (n0 d0 : ℤ) (u v : GInt) : sig n0 d0 (u - v) = sig n0 d0 u - sig n0 d0 v := by
  unfold sig; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem sig_zero (n0 d0 : ℤ) : sig n0 d0 0 = 0 := by
  unfold sig; simp

/-! ### Separation of two copies -/

/-- The four corners of a cell of the cell tile lie in the site set. -/
theorem corners_mem {P : Finset GInt} {c : GInt} (hc : c ∈ cellTileOf P) :
    c ∈ P ∧ c + gOne ∈ P ∧ c + gI ∈ P ∧ c + (gOne + gI) ∈ P := by
  have hc' : c ∈ P.filter (fun a => cellCorners a ⊆ P) := hc
  have hsub := (Finset.mem_filter.1 hc').2
  refine ⟨hsub ?_, hsub ?_, hsub ?_, hsub ?_⟩ <;> simp [cellCorners]

theorem cell_of_shift {P : Finset GInt} {a s : GInt} (h : s ∈ shiftS (cellSet P) a) : s - a ∈ cellTileOf P := by
  rw [CellRegisters.mem_shiftS_iff] at h
  exact Finset.mem_coe.1 h

/-- **Separation by `Λ₀`**, the copy of `P` on the side of the minimum. -/
theorem lam_sep {P Q : Finset GInt} {n0 d0 : ℤ} {a b : GInt} {mX MY : ℤ}
    (hX : ∀ z ∈ P, mX ≤ lam n0 d0 z) (hY : ∀ z ∈ Q, lam n0 d0 z ≤ MY)
    (hineq : MY + lam n0 d0 b - mX - lam n0 d0 a < d0 + n0) :
    ∀ s, s ∈ shiftS (cellSet P) a → s ∈ shiftS (cellSet Q) b → False := by
  intro s h1 h2
  have k1 := hX _ (corners_mem (cell_of_shift h1)).2.1
  have k2 := hY _ (corners_mem (cell_of_shift h2)).2.2.1
  rw [lam_add, lam_sub] at k1 k2
  have e1 : lam n0 d0 gOne = -n0 := by unfold lam; simp [gOne]
  have e2 : lam n0 d0 gI = d0 := by unfold lam; simp [gI]
  rw [e1] at k1
  rw [e2] at k2
  linarith

/-- **Separation by `Λ₀`**, the copy of `Q` on the side of the minimum. -/
theorem lam_sep' {P Q : Finset GInt} {n0 d0 : ℤ} {a b : GInt} {mX MY : ℤ}
    (hX : ∀ z ∈ Q, mX ≤ lam n0 d0 z) (hY : ∀ z ∈ P, lam n0 d0 z ≤ MY)
    (hineq : MY + lam n0 d0 a - mX - lam n0 d0 b < d0 + n0) :
    ∀ s, s ∈ shiftS (cellSet P) a → s ∈ shiftS (cellSet Q) b → False := by
  intro s h1 h2
  have k1 := hX _ (corners_mem (cell_of_shift h2)).2.1
  have k2 := hY _ (corners_mem (cell_of_shift h1)).2.2.1
  rw [lam_add, lam_sub] at k1 k2
  have e1 : lam n0 d0 gOne = -n0 := by unfold lam; simp [gOne]
  have e2 : lam n0 d0 gI = d0 := by unfold lam; simp [gI]
  rw [e1] at k1
  rw [e2] at k2
  linarith

/-- **Separation by `S₀`**, the copy of `P` on the side of the minimum (the right copy). -/
theorem sig_sep {P Q : Finset GInt} {n0 d0 : ℤ} {a b : GInt} {mR ML : ℤ}
    (hR : ∀ z ∈ P, mR ≤ sig n0 d0 z) (hL : ∀ z ∈ Q, sig n0 d0 z ≤ ML)
    (hineq : ML + sig n0 d0 b - mR - sig n0 d0 a < 2 * d0) :
    ∀ s, s ∈ shiftS (cellSet P) a → s ∈ shiftS (cellSet Q) b → False := by
  intro s h1 h2
  have k1 := hR _ (corners_mem (cell_of_shift h1)).1
  have k2 := hL _ (corners_mem (cell_of_shift h2)).2.2.2
  rw [sig_sub] at k1
  rw [sig_add, sig_sub] at k2
  have e : sig n0 d0 (gOne + gI) = 2 * d0 := by unfold sig; simp [gOne, gI]; ring
  rw [e] at k2
  linarith

/-- **Separation by `S₀`**, the copy of `Q` on the side of the minimum (the right copy). -/
theorem sig_sep' {P Q : Finset GInt} {n0 d0 : ℤ} {a b : GInt} {mR ML : ℤ}
    (hR : ∀ z ∈ Q, mR ≤ sig n0 d0 z) (hL : ∀ z ∈ P, sig n0 d0 z ≤ ML)
    (hineq : ML + sig n0 d0 a - mR - sig n0 d0 b < 2 * d0) :
    ∀ s, s ∈ shiftS (cellSet P) a → s ∈ shiftS (cellSet Q) b → False := by
  intro s h1 h2
  have k1 := hR _ (corners_mem (cell_of_shift h2)).1
  have k2 := hL _ (corners_mem (cell_of_shift h1)).2.2.2
  rw [sig_sub] at k1
  rw [sig_add, sig_sub] at k2
  have e : sig n0 d0 (gOne + gI) = 2 * d0 := by unfold sig; simp [gOne, gI]; ring
  rw [e] at k2
  linarith

/-! ### The bounds of a parent tile -/

/-- The four bounds of the functionals on a tile with a boundary word, from the bounds on its bottom walk and on its right walk:
`Λ₀` is at least `mL` on the tile and at most `Λ₀(Σ w1 + Σ w2) - mL`; `S₀` is at least `S₀(Σ w2) - MS` and at most
`S₀(Σ w1) + MS`. -/
theorem tile_bounds {P : Finset GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt (cellTileOf P) (0, 0) (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (hP : HasCornerCell P) (n0 d0 : ℤ) (hn0 : 0 ≤ n0) (hdn : n0 ≤ d0)
    (mL MS : ℤ) (hmL : ∀ p ∈ F2Word.walk (0, 0) w1, p ∈ P → mL ≤ lam n0 d0 p)
    (hMS : ∀ p ∈ F2Word.walk (0, 0) w2, F2Word.sum w1 + p ∈ P → sig n0 d0 p ≤ MS) :
    (∀ z ∈ P, mL ≤ lam n0 d0 z) ∧ (∀ z ∈ P, lam n0 d0 z ≤ lam n0 d0 (F2Word.sum w1 + F2Word.sum w2) - mL) ∧
      (∀ z ∈ P, sig n0 d0 (F2Word.sum w2) - MS ≤ sig n0 d0 z) ∧
      (∀ z ∈ P, sig n0 d0 z ≤ sig n0 d0 (F2Word.sum w1) + MS) := by
  have mem : ∀ p : GInt, (∃ s ∈ cellTileOf P, p ∈ cellCorners s) → p ∈ P := by
    rintro p ⟨s, hs, hps⟩
    have hs' : s ∈ P.filter (fun a => cellCorners a ⊆ P) := hs
    exact (Finset.mem_filter.1 hs').2 hps
  have corner : ∀ z ∈ P, ∃ s ∈ cellTileOf P, z ∈ cellCorners s :=
    fun z hz => FLatticePaper.Tiles.OverlapSides.corner_of_hcc hP hz
  have hd0 : 0 ≤ d0 := le_trans hn0 hdn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hle⟩ := CellExtremes.lam_min_bottom hT hA1 hA2 d0 n0 hd0 hn0 z (corner z hz)
    have := hmL p hp (mem p (CellExtremes.bottom_corner hT hA1 p hp))
    unfold lam at *
    linarith
  · intro z hz
    obtain ⟨p, hp, hle⟩ := CellExtremes.lam_max_top hT hA1 hA2 d0 n0 hd0 hn0 z (corner z hz)
    have h1 := hmL p hp (mem p (CellExtremes.bottom_corner hT hA1 p hp))
    have e := lam_sub n0 d0 (F2Word.sum w1 + F2Word.sum w2) p
    unfold lam at *
    linarith
  · intro z hz
    obtain ⟨p, hp, hle⟩ := CellExtremes.sig_min_left hT hA1 hA2 (d0 + n0) (d0 - n0) (by linarith) (by linarith) z
      (corner z hz)
    have hq : F2Word.sum w1 + p ∈ P :=
      mem _ (CellExtremes.right_corner hT hA1 _ (FLatticePaper.Tiles.OverlapSides.mem_walk_of_sub _ _ _ (by simpa using hp)))
    have h1 := hMS p hp hq
    have e := sig_sub n0 d0 (F2Word.sum w2) p
    unfold sig at *
    linarith
  · intro z hz
    obtain ⟨p, hp, hle⟩ := CellExtremes.sig_max_right hT hA1 hA2 (d0 + n0) (d0 - n0) (by linarith) (by linarith) z
      (corner z hz)
    have hq : F2Word.sum w1 + p ∈ P :=
      mem _ (CellExtremes.right_corner hT hA1 _ (FLatticePaper.Tiles.OverlapSides.mem_walk_of_sub _ _ _ (by simpa using hp)))
    have h1 := hMS p hp hq
    have e := sig_add n0 d0 (F2Word.sum w1) p
    unfold sig at *
    linarith

theorem sum_snd_eq_cntI (u : F2Word) (h : ∀ x ∈ u, x = .one ∨ x = .i) : (F2Word.sum u).2 = cntI u :=
  sum_snd u (fun x hx => by rcases h x hx with h | h <;> simp [h])

/-- The bounds on the odd parent tile `T(p)`, the tile of the odd register (a word `U` with `curO U = p`). -/
theorem odd_bounds (U : Word) (p q : Fraction) (hpU : curO U = p) (c e n0 d0 : ℤ) (A A' : Bool)
    (hn0 : n0 = c * p.num + q.num) (hd0 : d0 = c * p.den + q.den)
    (hc : 1 ≤ c) (hn1 : 1 ≤ p.num) (hd1 : p.num < p.den) (hn2 : 1 ≤ q.num) (hd2 : q.num < q.den)
    (hdet : p.num * q.den - q.num * p.den = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → 2 * p.num ≤ p.den) (hB : A = false → p.den ≤ 2 * p.num)
    (hA' : A' = true → p.den ≤ 3 * p.num) (hB' : A' = false → 3 * p.num ≤ p.den) :
    (∀ z ∈ oddTile U, mLP A e n0 d0 ≤ lam n0 d0 z) ∧
      (∀ z ∈ oddTile U, lam n0 d0 z ≤ lam n0 d0 (texV1Odd p - gI + (texV2 p + gOne)) - mLP A e n0 d0) ∧
      (∀ z ∈ oddTile U, sig n0 d0 (texV2 p + gOne) - mSP A' e n0 d0 ≤ sig n0 d0 z) ∧
      (∀ z ∈ oddTile U, sig n0 d0 z ≤ sig n0 d0 (texV1Odd p - gI) + mSP A' e n0 d0) := by
  have hfr : fracOdd U = p := hpU
  have hs1 : F2Word.sum (oddBottom U) = texV1Odd p - gI := by
    have h := FLatticePaper.Tiles.StandardBoundary.sum_oddBottom U
    rw [hfr] at h
    unfold almostV₁ at h
    rw [← h]; abel
  have hs2 : F2Word.sum (oddRight U) = texV2 p + gOne := by
    have h := FLatticePaper.Tiles.StandardBoundary.sum_oddRight U
    rw [hfr] at h
    unfold almostV₂ at h
    rw [← h]; abel
  have hA1 := (admissible_oddStandard U).1
  have hA2 := (admissible_oddStandard U).2
  have h1 : ∀ x ∈ oddBottom U, x = .one ∨ x = .i := hA1.1
  have h2 := FLatticePaper.Tiles.OverlapSides.letters_w2 hA2
  have hS1 := H3Data.sum_oddBottom_eq U
  have hS2 := H3Data.sum_oddRight_eq U
  rw [hpU] at hS1 hS2
  have hc1 := sum_snd_eq_cntI (oddBottom U) h1
  have hc2 : (F2Word.sum (oddRight U)).2 = cntI (oddRight U) :=
    sum_snd _ (fun x hx => by rcases h2 x hx with h | h <;> simp [h])
  have hmL : ∀ x ∈ F2Word.walk (0, 0) (oddBottom U), x ∈ oddTile U → mLP A e n0 d0 ≤ lam n0 d0 x := by
    intro x hx hxP
    obtain ⟨r1, r2, r3, r4⟩ := CellExtremes.walk_range_one_i (oddBottom U) h1 (0, 0) x hx
    have hL := H3Data.lam_bound_odd U x hxP
    rw [hpU] at hL
    rw [hS1] at r2
    rw [← hc1, hS1] at r4
    simp only [zero_add] at r1 r2 r3 r4
    have := bound_LP A p.num p.den q.num q.den c e x.1 x.2 hc hn1 hd1 hn2 hd2 hdet he hA hB r1 r2 r3 r4 hL
    rw [← hn0, ← hd0] at this
    exact this
  have hMS : ∀ x ∈ F2Word.walk (0, 0) (oddRight U), F2Word.sum (oddBottom U) + x ∈ oddTile U → sig n0 d0 x ≤ mSP A' e n0 d0 := by
    intro x hx hxP
    obtain ⟨r1, r2, r3, r4⟩ := CellExtremes.walk_range_i_neg (oddRight U) h2 (0, 0) x hx
    have hsb := H3Data.sig_bound_odd U _ hxP
    rw [hpU, hS1] at hsb
    rw [hS2] at r1
    rw [← hc2, hS2] at r4
    simp only [zero_add] at r1 r2 r3 r4
    simp only [Prod.fst_add, Prod.snd_add, tOf] at hsb
    have hx : (p.den + p.num) * x.1 + (p.den - p.num) * x.2 ≤
        p.den + p.num - min 0 (min (p.den - p.num) (3 * p.num - p.den)) := by nlinarith
    have := bound_SP A' p.num p.den q.num q.den c e x.1 x.2 hc hn1 hd1 hn2 hd2 hdet he hA' hB' r1 r2 r3 r4 hx
    rw [← hn0, ← hd0] at this
    exact this
  obtain ⟨b1, b2, b3, b4⟩ := tile_bounds (FLatticePaper.Tiles.OverlapSides.boundary_odd U) hA1 hA2 (oddTile_hcc U)
    n0 d0 (by rw [hn0]; nlinarith) (by rw [hn0, hd0]; nlinarith) (mLP A e n0 d0) (mSP A' e n0 d0) hmL hMS
  rw [hs1, hs2] at b2
  rw [hs2] at b3
  rw [hs1] at b4
  exact ⟨b1, b2, b3, b4⟩

/-- The bounds on the even parent tile `T(q)`, the tile of the even register (a word `U` with `curE U = q`). -/
theorem even_bounds (U : Word) (p q : Fraction) (hqU : curE U = q) (c e n0 d0 : ℤ) (A A' : Bool)
    (hn0 : n0 = c * p.num + q.num) (hd0 : d0 = c * p.den + q.den)
    (hc : 1 ≤ c) (hn1 : 1 ≤ p.num) (hd1 : p.num < p.den) (hn2 : 1 ≤ q.num) (hd2 : q.num < q.den)
    (hdet : p.num * q.den - q.num * p.den = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → 2 * q.num ≤ q.den) (hB : A = false → q.den ≤ 2 * q.num)
    (hA' : A' = true → q.den ≤ 3 * q.num) (hB' : A' = false → 3 * q.num ≤ q.den) :
    (∀ z ∈ evenTile U, mLQ A e c n0 d0 ≤ lam n0 d0 z) ∧
      (∀ z ∈ evenTile U, lam n0 d0 z ≤ lam n0 d0 (texV1Even q - gI + (texV2 q + gOne)) - mLQ A e c n0 d0) ∧
      (∀ z ∈ evenTile U, sig n0 d0 (texV2 q + gOne) - mSQ A' e c n0 d0 ≤ sig n0 d0 z) ∧
      (∀ z ∈ evenTile U, sig n0 d0 z ≤ sig n0 d0 (texV1Even q - gI) + mSQ A' e c n0 d0) := by
  have hfr : fracEven U = q := hqU
  have hs1 : F2Word.sum (evenBottom U) = texV1Even q - gI := by
    have h := FLatticePaper.Tiles.StandardBoundary.sum_evenBottom U
    rw [hfr] at h
    unfold almostV₁ at h
    rw [← h]; abel
  have hs2 : F2Word.sum (evenRight U) = texV2 q + gOne := by
    have h := FLatticePaper.Tiles.StandardBoundary.sum_evenRight U
    rw [hfr] at h
    unfold almostV₂ at h
    rw [← h]; abel
  have hA1 := (admissible_evenStandard U).1
  have hA2 := (admissible_evenStandard U).2
  have h1 : ∀ x ∈ evenBottom U, x = .one ∨ x = .i := hA1.1
  have h2 := FLatticePaper.Tiles.OverlapSides.letters_w2 hA2
  have hS1 := H3Data.sum_evenBottom_eq U
  have hS2 := H3Data.sum_evenRight_eq U
  rw [hqU] at hS1 hS2
  have hc1 := sum_snd_eq_cntI (evenBottom U) h1
  have hc2 : (F2Word.sum (evenRight U)).2 = cntI (evenRight U) :=
    sum_snd _ (fun x hx => by rcases h2 x hx with h | h <;> simp [h])
  have hmL : ∀ x ∈ F2Word.walk (0, 0) (evenBottom U), x ∈ evenTile U → mLQ A e c n0 d0 ≤ lam n0 d0 x := by
    intro x hx hxP
    obtain ⟨r1, r2, r3, r4⟩ := CellExtremes.walk_range_one_i (evenBottom U) h1 (0, 0) x hx
    have hL := H3Data.lam_bound_even U x hxP
    rw [hqU] at hL
    rw [hS1] at r2
    rw [← hc1, hS1] at r4
    simp only [zero_add] at r1 r2 r3 r4
    have := bound_LQ A p.num p.den q.num q.den c e x.1 x.2 hc hn1 hd1 hn2 hd2 hdet he hA hB r1 r2 r3 r4 hL
    rw [← hn0, ← hd0] at this
    exact this
  have hMS : ∀ x ∈ F2Word.walk (0, 0) (evenRight U), F2Word.sum (evenBottom U) + x ∈ evenTile U → sig n0 d0 x ≤ mSQ A' e c n0 d0 := by
    intro x hx hxP
    obtain ⟨r1, r2, r3, r4⟩ := CellExtremes.walk_range_i_neg (evenRight U) h2 (0, 0) x hx
    have hsb := H3Data.sig_bound_even U _ hxP
    rw [hqU, hS1] at hsb
    rw [hS2] at r1
    rw [← hc2, hS2] at r4
    simp only [zero_add] at r1 r2 r3 r4
    simp only [Prod.fst_add, Prod.snd_add, tOf] at hsb
    have hx : (q.den + q.num) * x.1 + (q.den - q.num) * x.2 ≤
        q.den + q.num - min 0 (min (q.den - q.num) (3 * q.num - q.den)) := by nlinarith
    have := bound_SQ A' p.num p.den q.num q.den c e x.1 x.2 hc hn1 hd1 hn2 hd2 hdet he hA' hB' r1 r2 r3 r4 hx
    rw [← hn0, ← hd0] at this
    exact this
  obtain ⟨b1, b2, b3, b4⟩ := tile_bounds (FLatticePaper.Tiles.OverlapSides.boundary_even U) hA1 hA2 (evenTile_hcc U)
    n0 d0 (by rw [hn0]; nlinarith) (by rw [hn0, hd0]; nlinarith) (mLQ A e c n0 d0) (mSQ A' e c n0 d0) hmL hMS
  rw [hs1, hs2] at b2
  rw [hs2] at b3
  rw [hs1] at b4
  exact ⟨b1, b2, b3, b4⟩

/-- (H3) in the form of the consumers for the even child of `w` (as `CellRegisters.CellsDisjointOdd` for the odd child): no cell
of a copy of the odd register at the offsets of the even child is a cell of a copy of the even register. -/
def CellsDisjointEven (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ a ∈ pOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ qOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even,
      ∀ s, s ∈ shiftS (cellSet (oddTile u1)) a → s ∈ shiftS (cellSet (evenTile u2)) b → False

/-- **(H3) for the odd child**: for a non-base word, no cell lies in a copy of the odd parent tile and in a copy of the even
parent tile of the standard decomposition of the odd child. -/
theorem cellsDisjointOdd (w : Word) (hw : ¬ IsBase w) : CellsDisjointOdd w := by
  intro u1 u2 hT1 hT2 a ha b hb s hs1 hs2
  have h12 := H3Data.nonbase_one_two hw
  have h13 := H3Data.nonbase_one_three hw
  rw [hT1.symm.trans (RegisterTiles.tOdd_eq_oddTile w h12)] at hs1
  rw [hT2.symm.trans (RegisterTiles.tEven_eq_evenTile w h13)] at hs2
  have hpU := H3Data.src_odd_frac w h12
  have hqU := H3Data.src_even_frac w h13
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w h12
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w h13
  have hdet := H3Data.eps_det w
  have hqpar : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hhalf : (2 * (parentsAt w).odd.num ≤ (parentsAt w).odd.den ∧ 2 * (parentsAt w).even.num ≤ (parentsAt w).even.den) ∨
      ((parentsAt w).odd.den ≤ 2 * (parentsAt w).odd.num ∧ (parentsAt w).even.den ≤ 2 * (parentsAt w).even.num) :=
    H3Data.half_dichotomy w hne
  have hthird : ((parentsAt w).odd.den ≤ 3 * (parentsAt w).odd.num ∧ (parentsAt w).even.den ≤ 3 * (parentsAt w).even.num) ∨
      (3 * (parentsAt w).odd.num ≤ (parentsAt w).odd.den ∧ 3 * (parentsAt w).even.num ≤ (parentsAt w).even.den) :=
    H3Data.third_dichotomy w hne
  set p := (parentsAt w).odd with hp
  set q := (parentsAt w).even with hq
  obtain ⟨A, hAt, hAf⟩ : ∃ A : Bool, (A = true → 2 * p.num ≤ p.den ∧ 2 * q.num ≤ q.den) ∧
      (A = false → p.den ≤ 2 * p.num ∧ q.den ≤ 2 * q.num) := by
    rcases hhalf with h | h
    · exact ⟨true, fun _ => h, fun h' => absurd h' (by decide)⟩
    · exact ⟨false, fun h' => absurd h' (by decide), fun _ => h⟩
  obtain ⟨A', hA't, hA'f⟩ : ∃ A' : Bool, (A' = true → p.den ≤ 3 * p.num ∧ q.den ≤ 3 * q.num) ∧
      (A' = false → 3 * p.num ≤ p.den ∧ 3 * q.num ≤ q.den) := by
    rcases hthird with h | h
    · exact ⟨true, fun _ => h, fun h' => absurd h' (by decide)⟩
    · exact ⟨false, fun h' => absurd h' (by decide), fun _ => h⟩
  by_cases hph : phase w = 1
  · rw [if_pos hph] at hdet
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = 1 * p.num + q.num := ⟨_, rfl⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : ℤ, d0 = 1 * p.den + q.den := ⟨_, rfl⟩
    obtain ⟨PL, PH, PSL, PSH⟩ := odd_bounds (srcOf w).1 p q hpU 1 1 n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inl rfl) (fun h => (hAt h).1) (fun h => (hAf h).1) (fun h => (hA't h).1) (fun h => (hA'f h).1)
    obtain ⟨QL, QH, QSL, QSH⟩ := even_bounds (srcOf w).2 p q hqU 1 1 n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inl rfl) (fun h => (hAt h).2) (fun h => (hAf h).2) (fun h => (hA't h).2) (fun h => (hA'f h).2)
    have vL1o : lam n0 d0 (texV1Odd p) = 2 * 1 := by
      rw [hn0, hd0]; simp only [lam, texV1Odd]; linear_combination 2 * hdet
    have vL1e : lam n0 d0 (texV1Even q) = -(1 * 1) := by
      rw [hn0, hd0]; simp only [lam, texV1Even]; linear_combination (-1 : ℤ) * hdet
    have vS2p : sig n0 d0 (texV2 p) = 2 * 1 := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination 2 * hdet
    have vS2q : sig n0 d0 (texV2 q) = -(2 * 1 * 1) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination (-2 * 1 : ℤ) * hdet
    have hdn : 0 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have hsn : 0 ≤ d0 + n0 := by rw [hn0, hd0]; omega
    have vL2p : 0 ≤ lam n0 d0 (texV2 p) := by
      have : lam n0 d0 (texV2 p) = (d0 - n0) * p.num + (d0 + n0) * p.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vL2q : 0 ≤ lam n0 d0 (texV2 q) := by
      have : lam n0 d0 (texV2 q) = (d0 - n0) * q.num + (d0 + n0) * q.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vS1o : 0 ≤ sig n0 d0 (texV1Odd p) := by
      have : sig n0 d0 (texV1Odd p) = (d0 + n0) * (2 * p.den) + (d0 - n0) * (2 * p.num) := by simp only [sig, texV1Odd]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vS1e : 0 ≤ sig n0 d0 (texV1Even q) := by
      have : sig n0 d0 (texV1Even q) = (d0 + n0) * q.den + (d0 - n0) * q.num := by simp only [sig, texV1Even]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vLgI : lam n0 d0 gI = d0 := by simp [lam, gI]
    have vLgO : lam n0 d0 gOne = -n0 := by simp [lam, gOne]
    have vSgI : sig n0 d0 gI = d0 - n0 := by simp [sig, gI]
    have vSgO : sig n0 d0 gOne = d0 + n0 := by simp [sig, gOne]
    have hc1 : 2 ≤ n0 := by rw [hn0]; omega
    have hc2 : 2 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have i1 : ((1 : ℤ) = -1) = False := by norm_num
    have i2 : ((-1 : ℤ) = 1) = False := by norm_num
    have hflag : (phase w == 1) = true := by simp [hph]
    have ha' : a = 0 ∨ a = texV1Even q + texV1Even q + texV2 q := by simpa [pOffsetsOdd, hflag] using ha
    have hb' : b = texV1Odd p ∨ b = texV1Odd p + texV1Even q ∨ b = texV2 p ∨ b = texV2 p + texV1Even q := by simpa [qOffsetsOdd, hflag] using hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1o, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1o, vL1e, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
  · rw [if_neg hph] at hdet
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = 1 * p.num + q.num := ⟨_, rfl⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : ℤ, d0 = 1 * p.den + q.den := ⟨_, rfl⟩
    obtain ⟨PL, PH, PSL, PSH⟩ := odd_bounds (srcOf w).1 p q hpU 1 (-1) n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inr rfl) (fun h => (hAt h).1) (fun h => (hAf h).1) (fun h => (hA't h).1) (fun h => (hA'f h).1)
    obtain ⟨QL, QH, QSL, QSH⟩ := even_bounds (srcOf w).2 p q hqU 1 (-1) n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inr rfl) (fun h => (hAt h).2) (fun h => (hAf h).2) (fun h => (hA't h).2) (fun h => (hA'f h).2)
    have vL1o : lam n0 d0 (texV1Odd p) = 2 * (-1) := by
      rw [hn0, hd0]; simp only [lam, texV1Odd]; linear_combination 2 * hdet
    have vL1e : lam n0 d0 (texV1Even q) = -(1 * (-1)) := by
      rw [hn0, hd0]; simp only [lam, texV1Even]; linear_combination (-1 : ℤ) * hdet
    have vS2p : sig n0 d0 (texV2 p) = 2 * (-1) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination 2 * hdet
    have vS2q : sig n0 d0 (texV2 q) = -(2 * 1 * (-1)) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination (-2 * 1 : ℤ) * hdet
    have hdn : 0 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have hsn : 0 ≤ d0 + n0 := by rw [hn0, hd0]; omega
    have vL2p : 0 ≤ lam n0 d0 (texV2 p) := by
      have : lam n0 d0 (texV2 p) = (d0 - n0) * p.num + (d0 + n0) * p.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vL2q : 0 ≤ lam n0 d0 (texV2 q) := by
      have : lam n0 d0 (texV2 q) = (d0 - n0) * q.num + (d0 + n0) * q.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vS1o : 0 ≤ sig n0 d0 (texV1Odd p) := by
      have : sig n0 d0 (texV1Odd p) = (d0 + n0) * (2 * p.den) + (d0 - n0) * (2 * p.num) := by simp only [sig, texV1Odd]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vS1e : 0 ≤ sig n0 d0 (texV1Even q) := by
      have : sig n0 d0 (texV1Even q) = (d0 + n0) * q.den + (d0 - n0) * q.num := by simp only [sig, texV1Even]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vLgI : lam n0 d0 gI = d0 := by simp [lam, gI]
    have vLgO : lam n0 d0 gOne = -n0 := by simp [lam, gOne]
    have vSgI : sig n0 d0 gI = d0 - n0 := by simp [sig, gI]
    have vSgO : sig n0 d0 gOne = d0 + n0 := by simp [sig, gOne]
    have hc1 : 2 ≤ n0 := by rw [hn0]; omega
    have hc2 : 2 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have i1 : ((1 : ℤ) = -1) = False := by norm_num
    have i2 : ((-1 : ℤ) = 1) = False := by norm_num
    have hflag : (phase w == 1) = false := by simp [hph]
    have ha' : a = texV1Even q + texV1Even q ∨ a = texV2 q := by simpa [pOffsetsOdd, hflag] using ha
    have hb' : b = 0 ∨ b = texV1Even q ∨ b = texV1Odd p + texV2 p ∨ b = texV1Odd p + texV2 p + texV1Even q := by simpa [qOffsetsOdd, hflag] using hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2p, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2

/-- **(H3) for the even child**: for a non-base word, no cell lies in a copy of the odd parent tile and in a copy of the even
parent tile of the standard decomposition of the even child. -/
theorem cellsDisjointEven (w : Word) (hw : ¬ IsBase w) : CellsDisjointEven w := by
  intro u1 u2 hT1 hT2 a ha b hb s hs1 hs2
  have h12 := H3Data.nonbase_one_two hw
  have h13 := H3Data.nonbase_one_three hw
  rw [hT1.symm.trans (RegisterTiles.tOdd_eq_oddTile w h12)] at hs1
  rw [hT2.symm.trans (RegisterTiles.tEven_eq_evenTile w h13)] at hs2
  have hpU := H3Data.src_odd_frac w h12
  have hqU := H3Data.src_even_frac w h13
  obtain ⟨hn1, hd1⟩ := H3Data.odd_parent_interior w h12
  obtain ⟨hn2, hd2⟩ := H3Data.even_parent_interior w h13
  have hdet := H3Data.eps_det w
  have hqpar : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hne : w ≠ [] := fun h => hw (Or.inl h)
  have hhalf : (2 * (parentsAt w).odd.num ≤ (parentsAt w).odd.den ∧ 2 * (parentsAt w).even.num ≤ (parentsAt w).even.den) ∨
      ((parentsAt w).odd.den ≤ 2 * (parentsAt w).odd.num ∧ (parentsAt w).even.den ≤ 2 * (parentsAt w).even.num) :=
    H3Data.half_dichotomy w hne
  have hthird : ((parentsAt w).odd.den ≤ 3 * (parentsAt w).odd.num ∧ (parentsAt w).even.den ≤ 3 * (parentsAt w).even.num) ∨
      (3 * (parentsAt w).odd.num ≤ (parentsAt w).odd.den ∧ 3 * (parentsAt w).even.num ≤ (parentsAt w).even.den) :=
    H3Data.third_dichotomy w hne
  set p := (parentsAt w).odd with hp
  set q := (parentsAt w).even with hq
  obtain ⟨A, hAt, hAf⟩ : ∃ A : Bool, (A = true → 2 * p.num ≤ p.den ∧ 2 * q.num ≤ q.den) ∧
      (A = false → p.den ≤ 2 * p.num ∧ q.den ≤ 2 * q.num) := by
    rcases hhalf with h | h
    · exact ⟨true, fun _ => h, fun h' => absurd h' (by decide)⟩
    · exact ⟨false, fun h' => absurd h' (by decide), fun _ => h⟩
  obtain ⟨A', hA't, hA'f⟩ : ∃ A' : Bool, (A' = true → p.den ≤ 3 * p.num ∧ q.den ≤ 3 * q.num) ∧
      (A' = false → 3 * p.num ≤ p.den ∧ 3 * q.num ≤ q.den) := by
    rcases hthird with h | h
    · exact ⟨true, fun _ => h, fun h' => absurd h' (by decide)⟩
    · exact ⟨false, fun h' => absurd h' (by decide), fun _ => h⟩
  by_cases hph : phase w = 1
  · rw [if_pos hph] at hdet
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = 2 * p.num + q.num := ⟨_, rfl⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : ℤ, d0 = 2 * p.den + q.den := ⟨_, rfl⟩
    obtain ⟨PL, PH, PSL, PSH⟩ := odd_bounds (srcOf w).1 p q hpU 2 1 n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inl rfl) (fun h => (hAt h).1) (fun h => (hAf h).1) (fun h => (hA't h).1) (fun h => (hA'f h).1)
    obtain ⟨QL, QH, QSL, QSH⟩ := even_bounds (srcOf w).2 p q hqU 2 1 n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inl rfl) (fun h => (hAt h).2) (fun h => (hAf h).2) (fun h => (hA't h).2) (fun h => (hA'f h).2)
    have vL1o : lam n0 d0 (texV1Odd p) = 2 * 1 := by
      rw [hn0, hd0]; simp only [lam, texV1Odd]; linear_combination 2 * hdet
    have vL1e : lam n0 d0 (texV1Even q) = -(2 * 1) := by
      rw [hn0, hd0]; simp only [lam, texV1Even]; linear_combination (-2 : ℤ) * hdet
    have vS2p : sig n0 d0 (texV2 p) = 2 * 1 := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination 2 * hdet
    have vS2q : sig n0 d0 (texV2 q) = -(2 * 2 * 1) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination (-2 * 2 : ℤ) * hdet
    have hdn : 0 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have hsn : 0 ≤ d0 + n0 := by rw [hn0, hd0]; omega
    have vL2p : 0 ≤ lam n0 d0 (texV2 p) := by
      have : lam n0 d0 (texV2 p) = (d0 - n0) * p.num + (d0 + n0) * p.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vL2q : 0 ≤ lam n0 d0 (texV2 q) := by
      have : lam n0 d0 (texV2 q) = (d0 - n0) * q.num + (d0 + n0) * q.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vS1o : 0 ≤ sig n0 d0 (texV1Odd p) := by
      have : sig n0 d0 (texV1Odd p) = (d0 + n0) * (2 * p.den) + (d0 - n0) * (2 * p.num) := by simp only [sig, texV1Odd]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vS1e : 0 ≤ sig n0 d0 (texV1Even q) := by
      have : sig n0 d0 (texV1Even q) = (d0 + n0) * q.den + (d0 - n0) * q.num := by simp only [sig, texV1Even]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vLgI : lam n0 d0 gI = d0 := by simp [lam, gI]
    have vLgO : lam n0 d0 gOne = -n0 := by simp [lam, gOne]
    have vSgI : sig n0 d0 gI = d0 - n0 := by simp [sig, gI]
    have vSgO : sig n0 d0 gOne = d0 + n0 := by simp [sig, gOne]
    have hc1 : 3 ≤ n0 := by rw [hn0]; omega
    have hc2 : 4 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have i1 : ((1 : ℤ) = -1) = False := by norm_num
    have i2 : ((-1 : ℤ) = 1) = False := by norm_num
    have hflag : (phase w == 1) = true := by simp [hph]
    have ha' : a = 0 ∨ a = texV2 p ∨ a = texV1Even q + texV2 q ∨ a = texV1Even q + texV2 q + texV2 p := by simpa [pOffsetsEven, hflag] using ha
    have hb' : b = texV1Odd p ∨ b = texV2 p + texV2 p := by simpa [qOffsetsEven, hflag] using hb
    rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1o, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i1, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
  · rw [if_neg hph] at hdet
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = 2 * p.num + q.num := ⟨_, rfl⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : ℤ, d0 = 2 * p.den + q.den := ⟨_, rfl⟩
    obtain ⟨PL, PH, PSL, PSH⟩ := odd_bounds (srcOf w).1 p q hpU 2 (-1) n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inr rfl) (fun h => (hAt h).1) (fun h => (hAf h).1) (fun h => (hA't h).1) (fun h => (hA'f h).1)
    obtain ⟨QL, QH, QSL, QSH⟩ := even_bounds (srcOf w).2 p q hqU 2 (-1) n0 d0 A A' hn0 hd0 (by norm_num) (by omega) hd1
      (by omega) hd2 hdet (Or.inr rfl) (fun h => (hAt h).2) (fun h => (hAf h).2) (fun h => (hA't h).2) (fun h => (hA'f h).2)
    have vL1o : lam n0 d0 (texV1Odd p) = 2 * (-1) := by
      rw [hn0, hd0]; simp only [lam, texV1Odd]; linear_combination 2 * hdet
    have vL1e : lam n0 d0 (texV1Even q) = -(2 * (-1)) := by
      rw [hn0, hd0]; simp only [lam, texV1Even]; linear_combination (-2 : ℤ) * hdet
    have vS2p : sig n0 d0 (texV2 p) = 2 * (-1) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination 2 * hdet
    have vS2q : sig n0 d0 (texV2 q) = -(2 * 2 * (-1)) := by
      rw [hn0, hd0]; simp only [sig, texV2]; linear_combination (-2 * 2 : ℤ) * hdet
    have hdn : 0 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have hsn : 0 ≤ d0 + n0 := by rw [hn0, hd0]; omega
    have vL2p : 0 ≤ lam n0 d0 (texV2 p) := by
      have : lam n0 d0 (texV2 p) = (d0 - n0) * p.num + (d0 + n0) * p.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vL2q : 0 ≤ lam n0 d0 (texV2 q) := by
      have : lam n0 d0 (texV2 q) = (d0 - n0) * q.num + (d0 + n0) * q.den := by simp only [lam, texV2]; ring
      rw [this]; exact add_nonneg (mul_nonneg hdn (by omega)) (mul_nonneg hsn (by omega))
    have vS1o : 0 ≤ sig n0 d0 (texV1Odd p) := by
      have : sig n0 d0 (texV1Odd p) = (d0 + n0) * (2 * p.den) + (d0 - n0) * (2 * p.num) := by simp only [sig, texV1Odd]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vS1e : 0 ≤ sig n0 d0 (texV1Even q) := by
      have : sig n0 d0 (texV1Even q) = (d0 + n0) * q.den + (d0 - n0) * q.num := by simp only [sig, texV1Even]
      rw [this]; exact add_nonneg (mul_nonneg hsn (by omega)) (mul_nonneg hdn (by omega))
    have vLgI : lam n0 d0 gI = d0 := by simp [lam, gI]
    have vLgO : lam n0 d0 gOne = -n0 := by simp [lam, gOne]
    have vSgI : sig n0 d0 gI = d0 - n0 := by simp [sig, gI]
    have vSgO : sig n0 d0 gOne = d0 + n0 := by simp [sig, gOne]
    have hc1 : 3 ≤ n0 := by rw [hn0]; omega
    have hc2 : 4 ≤ d0 - n0 := by rw [hn0, hd0]; omega
    have i1 : ((1 : ℤ) = -1) = False := by norm_num
    have i2 : ((-1 : ℤ) = 1) = False := by norm_num
    have hflag : (phase w == 1) = false := by simp [hph]
    have ha' : a = texV1Even q ∨ a = texV1Even q + texV2 p ∨ a = texV2 q ∨ a = texV2 q + texV2 p := by simpa [pOffsetsEven, hflag] using ha
    have hb' : b = 0 ∨ b = texV1Odd p + (texV2 p + texV2 p) := by simpa [qOffsetsEven, hflag] using hb
    rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2p, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep PSL QSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, sig_zero, vS2p, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep' QL PH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, vL1o, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact lam_sep PL QH (by cases A <;> cases A' <;> simp only [mLP, mLQ, lam_add, lam_sub, lam_zero, vL1e, vLgI, vLgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2
    · exact sig_sep' QSL PSH (by cases A <;> cases A' <;> simp only [mSP, mSQ, sig_add, sig_sub, vS2p, vS2q, vSgI, vSgO, i2, Bool.false_eq_true, if_true, if_false] <;> linarith [vL2p, vL2q, vS1o, vS1e, hc1, hc2]) s hs1 hs2

end FLatticePaper.Tiles.H3Pairs
