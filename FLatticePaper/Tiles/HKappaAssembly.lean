import FLatticePaper.Tiles.PTUniqueness
import FLatticePaper.Tiles.StackedMoreover

/-! The constancy of `κ` on the overlap of a standard tile `T` with its translate `T + v` (the input `hκ` of the closed-walk
theorem), assembled from the families. The odometer is `S` on `T`, and the odometer on `T + v` is `x ↦ S (x - v) + a·x`.

* `FA` is the family of `S` on the string of `T` (RespectsTiles: `S = FA.odo` on `FA.dom`), and `FB` the family of the
  translated odometer on the string of `T + v`.
* `P` and `M` are the Moreover families with `CrossCommon P M`; they respect the same strings as `FA` and `FB`
  (`htsP`, `htsM`), so uniqueness (`exists_affine_of_respects_gen`) gives `FA = P + affine` and `FB = M + affine`.
* The linear parts of the two affine functions agree (`hlin`, the corner identity: the named hypothesis).
* The forward pair `(FA, P)` and the reversed pair `(FB, M)` have different orientations in general, so each pair has its own
  `rev` (`revA`, `revB`): the forward Moreover `P` and the reversed Moreover `M` cannot respect the same `rev`.

Then on the overlap, `S z - S (z - v) - a·z = β - δ`, a constant. The covering of the overlap by the domains of `FA` and `FB`
(`hcov`, the `(e)` of `OverlapStrings` with the tile-list sites) and the adjacency of the lists (`hadjP`, `hadjM`) are named
hypotheses. -/

namespace FLatticePaper.Tiles

theorem PTFamily.hkappa_of_families (S : GInt → ℤ) (v a : GInt) (E : GInt → Prop)
    (FA P M FB : PTFamily) (o : Orientation) (revA revB : Bool)
    (hFA : ∀ k < FA.n, ∀ x ∈ FA.dom k, S x = FA.odo k x)
    (hFB : ∀ k < FB.n, ∀ x ∈ FB.dom k, S (x - v) + a.1 * x.1 + a.2 * x.2 = FB.odo k x)
    (htsP : P.ts = FA.ts) (htsM : M.ts = FB.ts)
    (hFAR : FA.Respects o revA) (hPR : P.Respects o revA)
    (hFBR : FB.Respects o revB) (hMR : M.Respects o revB)
    (hWP : ∀ k < P.n, ∀ j < P.n, ∀ x ∈ P.dom k, x ∈ P.dom j → P.odo k x = P.odo j x)
    (hWM : ∀ k < M.n, ∀ j < M.n, ∀ x ∈ M.dom k, x ∈ M.dom j → M.odo k x = M.odo j x)
    (hadjP : ∀ k, k + 1 < P.n → (∃ x, x ∈ P.dom k ∧ x ∈ P.dom (k + 1)) ∨
      ∃ x, x ∈ P.dom k ∧ ∃ y, y ∈ P.dom (k + 1) ∧ unitApart x y)
    (hadjM : ∀ k, k + 1 < M.n → (∃ x, x ∈ M.dom k ∧ x ∈ M.dom (k + 1)) ∨
      ∃ x, x ∈ M.dom k ∧ ∃ y, y ∈ M.dom (k + 1) ∧ unitApart x y)
    (hCross : CrossCommon P M)
    (hcov : ∀ z, E z → (∃ k < FA.n, z ∈ FA.dom k) ∧ (∃ j < FB.n, z ∈ FB.dom j))
    (hlin : ∀ (α γ : GInt) (β δ : ℤ),
      (∀ k < P.n, ∀ x : GInt, FA.odo k x = P.odo k x + α.1 * x.1 + α.2 * x.2 + β) →
      (∀ j < M.n, ∀ x : GInt, FB.odo j x = M.odo j x + γ.1 * x.1 + γ.2 * x.2 + δ) → α = γ) :
    ∃ κ : ℤ, ∀ z, E z → S z - S (z - v) - (a.1 * z.1 + a.2 * z.2) = κ := by
  have hWFA : ∀ k < FA.n, ∀ j < FA.n, ∀ x ∈ FA.dom k, x ∈ FA.dom j → FA.odo k x = FA.odo j x := by
    intro k hk j hj x hx hxj
    rw [← hFA k hk x hx, hFA j hj x hxj]
  have hWFB : ∀ k < FB.n, ∀ j < FB.n, ∀ x ∈ FB.dom k, x ∈ FB.dom j → FB.odo k x = FB.odo j x := by
    intro k hk j hj x hx hxj
    rw [← hFB k hk x hx, hFB j hj x hxj]
  obtain ⟨α, β, hα⟩ := PTFamily.exists_affine_of_respects_gen o revA P FA htsP.symm hPR hFAR hWP hWFA hadjP
  obtain ⟨γ, δ, hγ⟩ := PTFamily.exists_affine_of_respects_gen o revB M FB htsM.symm hMR hFBR hWM hWFB hadjM
  have hαγ : α = γ := hlin α γ β δ hα hγ
  refine ⟨β - δ, fun z hz => ?_⟩
  obtain ⟨⟨k, hk, hzk⟩, ⟨j, hj, hzj⟩⟩ := hcov z hz
  have hkP : k < P.n := by
    rw [PTFamily.n_eq_of_ts FA P htsP]
    exact hk
  have hjM : j < M.n := by
    rw [PTFamily.n_eq_of_ts FB M htsM]
    exact hj
  have hzkP : z ∈ P.dom k := by
    rw [PTFamily.dom_eq_of_ts FA P htsP k]
    exact hzk
  have hzjM : z ∈ M.dom j := by
    rw [PTFamily.dom_eq_of_ts FB M htsM j]
    exact hzj
  have h1 := hFA k hk z hzk
  have h2 := hα k hkP z
  have h3 := hFB j hj z hzj
  have h4 := hγ j hjM z
  have h5 := hCross k hkP j hjM z hzkP hzjM
  rw [hαγ] at h2
  linarith

end FLatticePaper.Tiles
