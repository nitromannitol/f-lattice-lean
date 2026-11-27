import FLatticePaper.Tiles.EvenStandardInstance
import FLatticePaper.Tiles.ClosedWalkVertical
import FLatticePaper.Tiles.ClosedWalkOdd
import FLatticePaper.Tiles.HorizontalAdjacency
import FLatticePaper.Tiles.VerticalAdjacency
import FLatticePaper.Tiles.OverlapStrings
import FLatticePaper.Tiles.CommonExtensionFamily
import FLatticePaper.Tiles.CommonExtensionStandard
import FLatticePaper.Tiles.CommonExtensionWitness
import FLatticePaper.Tiles.PointNonNeighbour

/-! The closed-walk theorem for the even standard tile: the odd constructions of `ClosedWalkVertical`, `ClosedWalkHorizontal`
and `ClosedWalkOdd`, with the even tile, the even fraction (`texV1Even (fracEven w) = (den, num)`, the first disjunct of the
closed-walk hypothesis `v1 = (d, n)`), the even instances, and the same constant `oddKappa` (its values depend only on the
numbers `num`, `den` of the fraction). The covering hypotheses are the open H2 input for the even pair. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.CellDerivation FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.TexVPositions FLatticePaper.Tiles.OverlapStrings FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardAll FLatticePaper.Tiles.CommonExtFamily FLatticePaper.Tiles.CommonExtStandard
  FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.CommonExtWitness

theorem vertical_kappa_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z) :
    ∃ κ : ℤ, ∀ z : GInt, z ∈ (↑(evenTile w) : Set GInt) → z - texV1Even (fracEven w) ∈ (↑(evenTile w) : Set GInt) →
      (evenO w).val z - (evenO w).val (z - texV1Even (fracEven w)) = κ := by
  obtain ⟨FA, P, M, FB, hFAodo, hFB, htsP, htsM, hPM, hFAts, hFBts, hFAR, hPR, hFBR, hMR, hWP, hWM, hCr, hlin⟩ :=
    vlin_standard_vertical_even S oddO evenO h w
  rw [almostV1_evenBottom_eq] at hFB hFBts
  have hFB0 : ∀ k < FB.n, ∀ x ∈ FB.dom k,
      (evenO w).val (x - texV1Even (fracEven w)) + (0 : GInt).1 * x.1 + (0 : GInt).2 * x.2 = FB.odo k x := by
    intro k hk x hx
    simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
    exact hFB k hk x hx
  have hadjP : ∀ k, k + 1 < P.n → (∃ x, x ∈ P.dom k ∧ x ∈ P.dom (k + 1)) ∨
      ∃ x, x ∈ P.dom k ∧ ∃ y, y ∈ P.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_vStringAt (vWordOf w true) _ P (htsP.trans hFAts) k hk
  have hadjM : ∀ k, k + 1 < M.n → (∃ x, x ∈ M.dom k ∧ x ∈ M.dom (k + 1)) ∨
      ∃ x, x ∈ M.dom k ∧ ∃ y, y ∈ M.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_vRevStringAt (vWordOf w true).reverse _ M (htsM.trans hFBts) k hk
  have hcov : ∀ z, (z ∈ (↑(evenTile w) : Set GInt) ∧ z - texV1Even (fracEven w) ∈ (↑(evenTile w) : Set GInt)) →
      (∃ k < FA.n, z ∈ FA.dom k) ∧ (∃ j < FB.n, z ∈ FB.dom j) := by
    intro z hz
    have hO := evenTile_common_in_strings w {z | ∃ k < FA.n, z ∈ FA.dom k} {z | ∃ j < FB.n, z ∈ FB.dom j}
      (fun z' hz' => (covers_iff_dom FA _ hFAts z').2 (H2X z' hz'))
      (fun z' hz' => (covers_iff_dom FB _ hFBts z').2 (H2Y z' hz'))
      z (Finset.mem_coe.1 hz.1) (Finset.mem_coe.1 hz.2)
    exact ⟨hO.1, hO.2⟩
  obtain ⟨κ, hκ⟩ := PTFamily.hkappa_of_families (evenO w).val (texV1Even (fracEven w)) 0
    (fun z => z ∈ (↑(evenTile w) : Set GInt) ∧ z - texV1Even (fracEven w) ∈ (↑(evenTile w) : Set GInt))
    FA P M FB Orientation.vertical false true hFAodo hFB0 htsP htsM hFAR hPR hFBR hMR hWP hWM hadjP hadjM
    hCr hcov hlin
  exact ⟨κ, fun z hz1 hz2 => by simpa using hκ z ⟨hz1, hz2⟩⟩


theorem texV2_fracEven_ne_zero (w : FLatticePaper.Farey.Word) : texV2 (fracEven w) ≠ 0 := by
  intro h
  apply texV1_even_ne_zero w
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [texV2, Prod.fst_zero, Prod.snd_zero] at h1 h2
  have hn : (fracEven w).num = 0 := by omega
  have hd : (fracEven w).den = 0 := by omega
  simp [texV1Even, hn, hd]

/-- The translate of the odd tile by `-v2` is disjoint from the tile at the cell level (the `v2` analogue of `odd_hdisj`). -/
theorem even_hdisj_neg2 (w : FLatticePaper.Farey.Word) :
    ∀ s, s ∈ cellTileOf (evenTile w) → s - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w) → False := by
  intro s hs hsv
  obtain ⟨huniq, -⟩ := clauseA_standard_even_all w
  have hmem : -texV2 (fracEven w) ∈ latticeOf (texV1Even (fracEven w)) (texV2 (fracEven w)) :=
    ⟨0, -1, by ext <;> simp⟩
  have h := huniq s 0 (zero_mem_lattice _ _) (-texV2 (fracEven w)) hmem (by rw [sub_zero]; exact hs) hsv
  exact texV2_fracEven_ne_zero w (neg_eq_zero.mp h.symm)

theorem horizontal_kappa_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w true) 0) z)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z) :
    ∃ κ : ℤ, ∀ z : GInt, z ∈ (↑(evenTile w) : Set GInt) → z - (-texV2 (fracEven w)) ∈ (↑(evenTile w) : Set GInt) →
      (evenO w).val z - (evenO w).val (z - (-texV2 (fracEven w))) -
        ((-((fracEven w).num)) * z.1 + (fracEven w).den * z.2) = κ := by
  obtain ⟨v, a, FA, P, M, FB, hv, ha, hFAodo, hFB, htsP, htsM, hFAts, hPts, hMts, hFAR, hFBR, hPR, hMR,
    hWP, hWM, hCr, hPa, hlin⟩ := hlin_standard_horizontal_even S oddO evenO h w
  have hv2 : v = -texV2 (fracEven w) := by
    rw [hv]
    rfl
  have ha2 : a = (-((fracEven w).num), (fracEven w).den) := by
    rw [ha]
    rfl
  subst hv2
  subst ha2
  have hFBts : FB.ts = hRevStringAt (hWordOf w true).reverse (1, -2) := by
    rw [← htsM]
    exact hMts
  have hcov : ∀ z, (z ∈ (↑(evenTile w) : Set GInt) ∧ z - (-texV2 (fracEven w)) ∈ (↑(evenTile w) : Set GInt)) →
      (∃ k < FA.n, z ∈ FA.dom k) ∧ (∃ j < FB.n, z ∈ FB.dom j) := by
    intro z hz
    have hO := common_in_strings_of_translate (evenTile_hcc w) (-texV2 (fracEven w)) (even_hdisj_neg2 w)
      {z | ∃ k < FA.n, z ∈ FA.dom k} {z | ∃ j < FB.n, z ∈ FB.dom j}
      (fun z' hz' => (covers_iff_dom FA _ hFAts z').2 (H2X z' hz'))
      (fun z' hz' => (covers_iff_dom FB _ hFBts z').2 (H2Y z' hz'))
      z (Finset.mem_coe.1 hz.1) (Finset.mem_coe.1 hz.2)
    exact ⟨hO.1, hO.2⟩
  have hadjP : ∀ k, k + 1 < P.n → (∃ x, x ∈ P.dom k ∧ x ∈ P.dom (k + 1)) ∨
      ∃ x, x ∈ P.dom k ∧ ∃ y, y ∈ P.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_hStringAt (hWordOf w true) (0, 0) P hPts k hk
  have hadjM : ∀ k, k + 1 < M.n → (∃ x, x ∈ M.dom k ∧ x ∈ M.dom (k + 1)) ∨
      ∃ x, x ∈ M.dom k ∧ ∃ y, y ∈ M.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_hRevStringAt (hWordOf w true).reverse (1, -2) M hMts k hk
  obtain ⟨κ, hκ⟩ := PTFamily.hkappa_of_families (evenO w).val (-texV2 (fracEven w))
    ((-((fracEven w).num)), (fracEven w).den)
    (fun z => z ∈ (↑(evenTile w) : Set GInt) ∧ z - (-texV2 (fracEven w)) ∈ (↑(evenTile w) : Set GInt))
    FA P M FB Orientation.horizontal false true hFAodo hFB htsP htsM hFAR hPR hFBR hMR hWP hWM hadjP hadjM
    hCr hcov hlin
  exact ⟨κ, fun z hz1 hz2 => hκ z ⟨hz1, hz2⟩⟩


theorem closed_walks_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w true) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z) :
    ∃ κ : ℤ × ℤ → ℤ, ∀ (u : ℤ × ℤ)
      (wk : (overlapGraph (dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)))).Walk u u),
      walkSum (offFam κ (texV1Even (fracEven w)) (texV2 (fracEven w)) (0, 0)
        ((fracEven w).num, -(fracEven w).den)) wk = 0 := by
  obtain ⟨κv, hv⟩ := vertical_kappa_even S oddO evenO h w H2X_v H2Y_v
  obtain ⟨κh, hh⟩ := horizontal_kappa_even S oddO evenO h w H2X_h H2Y_h
  have hκ : ∀ (d' : ℤ × ℤ) (y : ℤ × ℤ), y ∈ (↑(evenTile w) : Set (ℤ × ℤ)) →
      y - vP (texV1Even (fracEven w)) (texV2 (fracEven w)) d' ∈ (↑(evenTile w) : Set (ℤ × ℤ)) →
      (evenO w).val y - ((evenO w).val (y - vP (texV1Even (fracEven w)) (texV2 (fracEven w)) d') +
        dotZ (aP (0, 0) ((fracEven w).num, -(fracEven w).den) d') y) =
        oddKappa κv κh (fracEven w).num (fracEven w).den d' := by
    intro d' y hy hyd
    rcases d' with ⟨d1, d2⟩
    by_cases h0 : (d1, d2) = (0, 0)
    · simp only [Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      have h00 : y - ((0 : ℤ), (0 : ℤ)) = y := by ext <;> simp
      simp [vP, aP, dotZ, oddKappa, h00]
    · obtain ⟨hd1, hd2, hd3, hd4⟩ := evenTile_diagonal_disjoint w
      have hc := unit_of_contact (P := evenTile w) (v1 := texV1Even (fracEven w)) (v2 := texV2 (fracEven w))
        (fun k k' hns z hz => evenTile_nonneighbour w k k' hns z hz)
        (fun z hz => ⟨hd1 z hz, hd2 z hz, hd3 z hz, hd4 z hz⟩) h0 (Finset.mem_coe.1 hy)
        (Finset.mem_coe.1 hyd)
      rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 1 ∧ d2 = 0 := ⟨e1, e2⟩
        have e := hv y hy (by simpa [vP] using hyd)
        simp only [vP, aP, dotZ, oddKappa]
        simp
        linarith
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = -1 ∧ d2 = 0 := ⟨e1, e2⟩
        have hvn : vP (texV1Even (fracEven w)) (texV2 (fracEven w)) (-1, 0) = -texV1Even (fracEven w) := by
          ext <;> simp [vP]
        have haP : aP (0, 0) ((fracEven w).num, -(fracEven w).den) (-1, 0) = (0, 0) := by
          ext <;> simp [aP]
        rw [hvn] at hyd ⊢
        rw [haP]
        have e := hv (y - -texV1Even (fracEven w)) hyd
          (by rw [sub_neg_eq_add, add_sub_cancel_right]; exact hy)
        rw [sub_neg_eq_add, add_sub_cancel_right] at e
        have hk : oddKappa κv κh (fracEven w).num (fracEven w).den (-1, 0) = -κv := by
          simp [oddKappa]
        rw [hk]
        simp only [dotZ, zero_mul, add_zero, sub_neg_eq_add]
        linarith
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 0 ∧ d2 = 1 := ⟨e1, e2⟩
        have hvP : vP (texV1Even (fracEven w)) (texV2 (fracEven w)) (0, 1) = texV2 (fracEven w) := by
          ext <;> simp [vP]
        rw [hvP] at hyd
        have hzy : y - texV2 (fracEven w) - -texV2 (fracEven w) = y := by
          simp
        have e := hh (y - texV2 (fracEven w)) (by simpa using hyd) (by rw [hzy]; exact hy)
        rw [hzy] at e
        simp only [vP, aP, dotZ, oddKappa, texV2, Prod.fst_sub, Prod.snd_sub] at e ⊢
        simp
        linear_combination (-1 : ℤ) * e
      · simp only at e1 e2
        obtain ⟨rfl, rfl⟩ : d1 = 0 ∧ d2 = -1 := ⟨e1, e2⟩
        have hvP : vP (texV1Even (fracEven w)) (texV2 (fracEven w)) (0, -1) = -texV2 (fracEven w) := by
          ext <;> simp [vP]
        have haP : aP (0, 0) ((fracEven w).num, -(fracEven w).den) (0, -1) =
            (-(fracEven w).num, (fracEven w).den) := by
          ext <;> simp [aP]
        rw [hvP] at hyd ⊢
        rw [haP]
        have hk : oddKappa κv κh (fracEven w).num (fracEven w).den (0, -1) = κh := by
          simp [oddKappa]
        rw [hk]
        have e := hh y hy hyd
        simp only [dotZ]
        linear_combination e
  refine ⟨oddKappa κv κh (fracEven w).num (fracEven w).den, fun u wk => ?_⟩
  refine family_closed_walks_zero_paper (↑(evenTile w) : Set (ℤ × ℤ)) (evenO w).val (fracEven w).num
    (fracEven w).den (texV1Even (fracEven w)) (texV2 (fracEven w)) (0, 0) ((fracEven w).num, -(fracEven w).den)
    (oddKappa κv κh (fracEven w).num (fracEven w).den) hκ (evenTile_hA1h w) (evenTile_hA1v w) (evenTile_hA2 w)
    rfl rfl (Or.inl rfl) u wk


end FLatticePaper.Tiles
