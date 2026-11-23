import FLatticePaper.Plane.Induction.WeightChange
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 42, step 2: the policy field reduces to one strict rank and two monotone deck-affine functions.

The policy field of `StrongEstimates` asks for `RankWithIncrements policy kernel transverse (−a) (c η)` for every pair of positive
weights `a, c`. Here it is enough to have the case `a = c = 1` (one strict rank) and two deck-affine functions `P` (increments
`(−1, 0)`) and `J` (increments `(0, η)`) that do not increase along the retained steps. Then every pair of weights follows. -/

namespace FLatticePaper.Induction

open FLatticePaper

/-- **Every pair of weights from one strict rank.** Let `retained` be invariant under the deck `(U, V)` with nonzero determinant, and
let `P, J` be deck-affine with increments `(−1, 0)` and `(0, η)`, both nonincreasing along retained steps. If one strict rank with
increments `(−1, 1·η)` exists, then for all positive `a, b` the rank with increments `(−a, b η)` exists. -/
theorem rankWithIncrements_of_monotone {retained : Site → Site → Prop} {U V : Site}
    (hD : U.1 * V.2 - U.2 * V.1 ≠ 0)
    (hiffU : ∀ c i, retained c i ↔ retained (c + U) (i + U))
    (hiffV : ∀ c i, retained c i ↔ retained (c + V) (i + V))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {P J : Site → ℤ}
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η)
    (hmono : ∀ x y, retained x y → P y ≤ P x ∧ J y ≤ J x)
    (hrank : RankWithIncrements retained U V (-1) (1 * η))
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    RankWithIncrements retained U V (-a) (b * η) := by
  unfold RankWithIncrements at hrank
  obtain ⟨r0, lam0, hlam0, hstrict0, hU0, hV0⟩ := hrank
  have hr0U : ∀ z, r0 (z + U) = r0 z + (-lam0) := fun z => by
    have := hU0 z
    linarith
  have hr0V : ∀ z, r0 (z + V) = r0 z + η * lam0 := fun z => by
    have := hV0 z
    linarith
  have hdec : ∀ x y, retained x y → r0 y < r0 x := fun x y h => hstrict0 x y h
  obtain ⟨lam, hlam, rank, hstrict, hU, hV⟩ :=
    FLatticePaper.WeightChange.exists_rank_increments U V hD hiffU hiffV η hη P J r0 (-lam0) (η * lam0) hPU hPV hJU hJV hr0U hr0V hmono hdec a b ha hb
  exact ⟨rank, lam, hlam, hstrict, fun z => by linarith [hU z], fun z => by linarith [hV z]⟩

/-! The deck hull of a retained relation: it is invariant under the deck, so the rank construction applies to it without a
periodicity hypothesis on the policy. A rank strict on the hull is strict on the policy (take zero translations). -/

/-- The deck hull of a relation: `c → i` when some deck translate of the pair is related. -/
abbrev deckHull (U V : Site) (retained : Site → Site → Prop) (c i : Site) : Prop :=
  ∃ n m : ℤ, retained (c + FLatticePaper.WeightChange.latPt U V n m) (i + FLatticePaper.WeightChange.latPt U V n m)

theorem latPt_add_one_U (U V : Site) (n m : ℤ) :
    FLatticePaper.WeightChange.latPt U V (n + 1) m = FLatticePaper.WeightChange.latPt U V n m + U := by
  ext <;> simp only [FLatticePaper.WeightChange.latPt, Prod.fst_add, Prod.snd_add] <;> ring

theorem latPt_add_one_V (U V : Site) (n m : ℤ) :
    FLatticePaper.WeightChange.latPt U V n (m + 1) = FLatticePaper.WeightChange.latPt U V n m + V := by
  ext <;> simp only [FLatticePaper.WeightChange.latPt, Prod.fst_add, Prod.snd_add] <;> ring

theorem deckShift_U (U V c : Site) (k m : ℤ) :
    c + U + FLatticePaper.WeightChange.latPt U V k m = c + FLatticePaper.WeightChange.latPt U V (k + 1) m := by
  rw [latPt_add_one_U]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem deckShift_V (U V c : Site) (k m : ℤ) :
    c + V + FLatticePaper.WeightChange.latPt U V k m = c + FLatticePaper.WeightChange.latPt U V k (m + 1) := by
  rw [latPt_add_one_V]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The deck hull is invariant under the translation by `U`. -/
theorem deckHull_iff_U (U V : Site) (retained : Site → Site → Prop) (c i : Site) :
    deckHull U V retained (c + U) (i + U) ↔ deckHull U V retained c i := by
  constructor
  · rintro ⟨n, m, h⟩
    refine ⟨n + 1, m, ?_⟩
    rw [← deckShift_U U V c n m, ← deckShift_U U V i n m]
    exact h
  · rintro ⟨n, m, h⟩
    refine ⟨n - 1, m, ?_⟩
    rw [deckShift_U U V c (n - 1) m, deckShift_U U V i (n - 1) m, Int.sub_add_cancel n 1]
    exact h

/-- The deck hull is invariant under the translation by `V`. -/
theorem deckHull_iff_V (U V : Site) (retained : Site → Site → Prop) (c i : Site) :
    deckHull U V retained (c + V) (i + V) ↔ deckHull U V retained c i := by
  constructor
  · rintro ⟨n, m, h⟩
    refine ⟨n, m + 1, ?_⟩
    rw [← deckShift_V U V c n m, ← deckShift_V U V i n m]
    exact h
  · rintro ⟨n, m, h⟩
    refine ⟨n, m - 1, ?_⟩
    rw [deckShift_V U V c n (m - 1), deckShift_V U V i n (m - 1), Int.sub_add_cancel m 1]
    exact h

/-- **Every pair of weights from one strict rank, for the deck hull.** The policy need not be deck-periodic: the rank is built on
the deck hull of `retained`, and is strict there, hence strict on `retained`. -/
theorem rankWithIncrements_of_monotone_hull {retained : Site → Site → Prop} {U V : Site}
    (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) {η : ℤ} (hη : η = 1 ∨ η = -1) {P J : Site → ℤ}
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η)
    (hmono : ∀ x y, retained x y → P y ≤ P x ∧ J y ≤ J x)
    (hrank : RankWithIncrements retained U V (-1) η)
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    RankWithIncrements retained U V (-a) (b * η) := by
  unfold RankWithIncrements at hrank
  obtain ⟨r0, lam0, hlam0, hstrict0, hU0, hV0⟩ := hrank
  have hr0U : ∀ z, r0 (z + U) = r0 z + (-lam0) := fun z => by linarith [hU0 z]
  have hr0V : ∀ z, r0 (z + V) = r0 z + η * lam0 := fun z => by linarith [hV0 z]
  have hPU' : ∀ x, P (x + U) = P x + (-1) := fun x => by rw [hPU]; ring
  have hPV' : ∀ x, P (x + V) = P x + 0 := fun x => by rw [hPV]; ring
  have hJU' : ∀ x, J (x + U) = J x + 0 := fun x => by rw [hJU]; ring
  have hJV' : ∀ x, J (x + V) = J x + η := hJV
  have hmonoH : ∀ x y, deckHull U V retained x y → P y ≤ P x ∧ J y ≤ J x := by
    rintro x y ⟨n, m, h⟩
    obtain ⟨hp1, hp2⟩ := hmono _ _ h
    have eP1 := FLatticePaper.WeightChange.affine_lattice hPU' hPV' x n m
    have eP2 := FLatticePaper.WeightChange.affine_lattice hPU' hPV' y n m
    have eJ1 := FLatticePaper.WeightChange.affine_lattice hJU' hJV' x n m
    have eJ2 := FLatticePaper.WeightChange.affine_lattice hJU' hJV' y n m
    exact ⟨by linarith, by linarith⟩
  have hdecH : ∀ x y, deckHull U V retained x y → r0 y < r0 x := by
    rintro x y ⟨n, m, h⟩
    have hs := hstrict0 _ _ h
    have e1 := FLatticePaper.WeightChange.affine_lattice hr0U hr0V x n m
    have e2 := FLatticePaper.WeightChange.affine_lattice hr0U hr0V y n m
    linarith
  have hiffU : ∀ c i, deckHull U V retained c i ↔ deckHull U V retained (c + U) (i + U) :=
    fun c i => (deckHull_iff_U U V retained c i).symm
  have hiffV : ∀ c i, deckHull U V retained c i ↔ deckHull U V retained (c + V) (i + V) :=
    fun c i => (deckHull_iff_V U V retained c i).symm
  obtain ⟨lam, hlam, rank, hstrict, hU, hV⟩ :=
    FLatticePaper.WeightChange.exists_rank_increments (ret := deckHull U V retained) U V hD hiffU hiffV η hη P J r0
      (-lam0) (η * lam0) hPU hPV hJU hJV hr0U hr0V hmonoH hdecH a b ha hb
  have h0 : ∀ x : Site, x + FLatticePaper.WeightChange.latPt U V 0 0 = x := fun x => by
    rw [FLatticePaper.WeightChange.latPt_zero]
    ext <;> simp
  refine ⟨rank, lam, hlam, fun x i h => hstrict x i ⟨0, 0, ?_⟩, fun z => ?_, fun z => ?_⟩
  · rw [h0, h0]
    exact h
  · have := hU z
    rw [this]
    ring
  · have := hV z
    rw [this]
    ring

end FLatticePaper.Induction
