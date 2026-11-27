import FLatticePaper.Tiles.StandardInstance
import FLatticePaper.Tiles.HKappaAssembly
import FLatticePaper.Tiles.HorizontalAdjacency
import FLatticePaper.Tiles.OverlapStrings
import FLatticePaper.Tiles.ClosedWalkVertical

/-! The horizontal constancy `hκ` at the unit step `(0,-1)` for the odd standard tile: on the overlap of the tile `T` with
its translate `T - v2` (`v2 = texV2 (fracOdd w)`), the odometer difference is constant, with the affine factor
`a = (-num, den)` (that is `-a_{n/d,2}`). The covering hypotheses `H2X` and `H2Y` are the open H2 input, as tile-list
covering of the bottom string `hStringAt wh 0` and of the top reversed string `hRevStringAt wh.reverse (1,-2)`. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.CellDerivation FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.TexVPositions FLatticePaper.Tiles.OverlapStrings FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardAll

theorem texV2_fracOdd_ne_zero (w : FLatticePaper.Farey.Word) : texV2 (fracOdd w) ≠ 0 := by
  intro h
  apply texV1_odd_ne_zero w
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [texV2, Prod.fst_zero, Prod.snd_zero] at h1 h2
  have hn : (fracOdd w).num = 0 := by omega
  have hd : (fracOdd w).den = 0 := by omega
  simp [texV1Odd, hn, hd]

/-- The translate of the odd tile by `-v2` is disjoint from the tile at the cell level (the `v2` analogue of `odd_hdisj`). -/
theorem odd_hdisj_neg2 (w : FLatticePaper.Farey.Word) :
    ∀ s, s ∈ cellTileOf (oddTile w) → s - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w) → False := by
  intro s hs hsv
  obtain ⟨huniq, -⟩ := clauseA_standard_odd_all w
  have hmem : -texV2 (fracOdd w) ∈ latticeOf (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
    ⟨0, -1, by ext <;> simp⟩
  have h := huniq s 0 (zero_mem_lattice _ _) (-texV2 (fracOdd w)) hmem (by rw [sub_zero]; exact hs) hsv
  exact texV2_fracOdd_ne_zero w (neg_eq_zero.mp h.symm)

theorem horizontal_kappa (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w false) 0) z)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2)) z) :
    ∃ κ : ℤ, ∀ z : GInt, z ∈ (↑(oddTile w) : Set GInt) → z - (-texV2 (fracOdd w)) ∈ (↑(oddTile w) : Set GInt) →
      (oddO w).val z - (oddO w).val (z - (-texV2 (fracOdd w))) -
        ((-((fracOdd w).num)) * z.1 + (fracOdd w).den * z.2) = κ := by
  obtain ⟨v, a, FA, P, M, FB, hv, ha, hFAodo, hFB, htsP, htsM, hFAts, hPts, hMts, hFAR, hFBR, hPR, hMR,
    hWP, hWM, hCr, hPa, hlin⟩ := hlin_standard_horizontal S oddO evenO h w
  have hv2 : v = -texV2 (fracOdd w) := by
    rw [hv]
    rfl
  have ha2 : a = (-((fracOdd w).num), (fracOdd w).den) := by
    rw [ha]
    rfl
  subst hv2
  subst ha2
  have hFBts : FB.ts = hRevStringAt (hWordOf w false).reverse (1, -2) := by
    rw [← htsM]
    exact hMts
  have hcov : ∀ z, (z ∈ (↑(oddTile w) : Set GInt) ∧ z - (-texV2 (fracOdd w)) ∈ (↑(oddTile w) : Set GInt)) →
      (∃ k < FA.n, z ∈ FA.dom k) ∧ (∃ j < FB.n, z ∈ FB.dom j) := by
    intro z hz
    have hO := common_in_strings_of_translate (oddTile_hcc w) (-texV2 (fracOdd w)) (odd_hdisj_neg2 w)
      {z | ∃ k < FA.n, z ∈ FA.dom k} {z | ∃ j < FB.n, z ∈ FB.dom j}
      (fun z' hz' => (covers_iff_dom FA _ hFAts z').2 (H2X z' hz'))
      (fun z' hz' => (covers_iff_dom FB _ hFBts z').2 (H2Y z' hz'))
      z (Finset.mem_coe.1 hz.1) (Finset.mem_coe.1 hz.2)
    exact ⟨hO.1, hO.2⟩
  have hadjP : ∀ k, k + 1 < P.n → (∃ x, x ∈ P.dom k ∧ x ∈ P.dom (k + 1)) ∨
      ∃ x, x ∈ P.dom k ∧ ∃ y, y ∈ P.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_hStringAt (hWordOf w false) (0, 0) P hPts k hk
  have hadjM : ∀ k, k + 1 < M.n → (∃ x, x ∈ M.dom k ∧ x ∈ M.dom (k + 1)) ∨
      ∃ x, x ∈ M.dom k ∧ ∃ y, y ∈ M.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_hRevStringAt (hWordOf w false).reverse (1, -2) M hMts k hk
  obtain ⟨κ, hκ⟩ := PTFamily.hkappa_of_families (oddO w).val (-texV2 (fracOdd w))
    ((-((fracOdd w).num)), (fracOdd w).den)
    (fun z => z ∈ (↑(oddTile w) : Set GInt) ∧ z - (-texV2 (fracOdd w)) ∈ (↑(oddTile w) : Set GInt))
    FA P M FB Orientation.horizontal false true hFAodo hFB htsP htsM hFAR hPR hFBR hMR hWP hWM hadjP hadjM
    hCr hcov hlin
  exact ⟨κ, fun z hz1 hz2 => hκ z ⟨hz1, hz2⟩⟩

end FLatticePaper.Tiles
