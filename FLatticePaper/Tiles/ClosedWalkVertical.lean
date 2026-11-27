import FLatticePaper.Tiles.StandardInstance
import FLatticePaper.Tiles.HKappaAssembly
import FLatticePaper.Tiles.VerticalAdjacency
import FLatticePaper.Tiles.OverlapStrings
import FLatticePaper.Tiles.TexVPositions

/-! The vertical constancy `hκ` at the unit step `(1,0)` for the odd standard tile: on the overlap of the tile `T` with its
translate `T + v1` (`v1 = texV1Odd (fracOdd w)`), the odometer difference `S z - S (z - v1)` is constant.

The hypotheses `H2X` and `H2Y` are the boundary covering (the input `H2` of the common-extension argument, open for w3):
the boundary vertices of `T`, and of the translate, lie in the domains of the vertical strings of the instance. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.CellDerivation FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.TexVPositions FLatticePaper.Tiles.OverlapStrings FLatticePaper.Tiles.Standard

/-- The tile list `ts` covers the site `z`: `z` lies in the domain of one of its tiles. -/
def tileCovers (ts : List (ZTile × GInt)) (z : GInt) : Prop :=
  ∃ k < ts.length, z ∈ (tileShape (ts.getD k (ZTile.zero, (0 : GInt))).1).map
    (· + (ts.getD k (ZTile.zero, (0 : GInt))).2)

theorem covers_iff_dom (F : PTFamily) (ts : List (ZTile × GInt)) (h : F.ts = ts) (z : GInt) :
    (∃ k < F.n, z ∈ F.dom k) ↔ tileCovers ts z := by
  unfold tileCovers PTFamily.dom PTFamily.tile PTFamily.n
  rw [h]

theorem vertical_kappa (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z - texV1Odd (fracOdd w) ∈ oddTile w →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z)
    (H2Y : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z → z ∈ oddTile w →
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z) :
    ∃ κ : ℤ, ∀ z : GInt, z ∈ (↑(oddTile w) : Set GInt) → z - texV1Odd (fracOdd w) ∈ (↑(oddTile w) : Set GInt) →
      (oddO w).val z - (oddO w).val (z - texV1Odd (fracOdd w)) = κ := by
  obtain ⟨FA, P, M, FB, hFAodo, hFB, htsP, htsM, hPM, hFAts, hFBts, hFAR, hPR, hFBR, hMR, hWP, hWM, hCr, hlin⟩ :=
    vlin_standard_vertical S oddO evenO h w
  rw [almostV1_oddBottom_eq] at hFB hFBts
  have hFB0 : ∀ k < FB.n, ∀ x ∈ FB.dom k,
      (oddO w).val (x - texV1Odd (fracOdd w)) + (0 : GInt).1 * x.1 + (0 : GInt).2 * x.2 = FB.odo k x := by
    intro k hk x hx
    simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
    exact hFB k hk x hx
  have hadjP : ∀ k, k + 1 < P.n → (∃ x, x ∈ P.dom k ∧ x ∈ P.dom (k + 1)) ∨
      ∃ x, x ∈ P.dom k ∧ ∃ y, y ∈ P.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_vStringAt (vWordOf w false) _ P (htsP.trans hFAts) k hk
  have hadjM : ∀ k, k + 1 < M.n → (∃ x, x ∈ M.dom k ∧ x ∈ M.dom (k + 1)) ∨
      ∃ x, x ∈ M.dom k ∧ ∃ y, y ∈ M.dom (k + 1) ∧ unitApart x y :=
    fun k hk => adj_vRevStringAt (vWordOf w false).reverse _ M (htsM.trans hFBts) k hk
  have hcov : ∀ z, (z ∈ (↑(oddTile w) : Set GInt) ∧ z - texV1Odd (fracOdd w) ∈ (↑(oddTile w) : Set GInt)) →
      (∃ k < FA.n, z ∈ FA.dom k) ∧ (∃ j < FB.n, z ∈ FB.dom j) := by
    intro z hz
    have hO := oddTile_common_in_strings w {z | ∃ k < FA.n, z ∈ FA.dom k} {z | ∃ j < FB.n, z ∈ FB.dom j}
      (fun z' hz' hz'' => (covers_iff_dom FA _ hFAts z').2 (H2X z' hz' hz''))
      (fun z' hz' hz'' => (covers_iff_dom FB _ hFBts z').2 (H2Y z' hz' hz''))
      z (Finset.mem_coe.1 hz.1) (Finset.mem_coe.1 hz.2)
    exact ⟨hO.1, hO.2⟩
  obtain ⟨κ, hκ⟩ := PTFamily.hkappa_of_families (oddO w).val (texV1Odd (fracOdd w)) 0
    (fun z => z ∈ (↑(oddTile w) : Set GInt) ∧ z - texV1Odd (fracOdd w) ∈ (↑(oddTile w) : Set GInt))
    FA P M FB Orientation.vertical false true hFAodo hFB0 htsP htsM hFAR hPR hFBR hMR hWP hWM hadjP hadjM
    hCr hcov hlin
  exact ⟨κ, fun z hz1 hz2 => by simpa using hκ z ⟨hz1, hz2⟩⟩

end FLatticePaper.Tiles
