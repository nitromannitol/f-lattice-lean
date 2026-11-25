import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.H0Core

/-! # Game forts of the fixed free directions (FIXED_FREE_GAME_AUDIT §1, §3–§4)

A game fort for the field `F` and the sign `η` is a set `S` obstructing an acyclic policy whose free directions are fixed:
* black (Laplacian `−1`): at least one actual input is in `S`;
* nonfree white (Laplacian `0`, `Nonfree`): BOTH actual inputs are in `S`;
* free white (Laplacian `0`, a free site): its ONE canonical input `z + prescribed` is in `S`;
* white translate-free (neither nonfree nor free): at least one input (a relaxation of the audit's rule; it only enlarges the class of
  forts, so an argument using the other three rules applies to the audit's forts).

The route lemmas below use only the free-white rule at the root, the nonfree-white rule at the middles, and the whiteness of the middles.
The whiteness of a middle is a hypothesis unless it follows from zero values (the even H middle does, from the zero strip and the even zero
extension `[1 − d, 2L − 2]`). The audit's claim that the middles are white is quoted at each hypothesis. -/

open scoped Classical

namespace FLatticePaper.GameFort

open FLatticePaper FLatticePaper.Induction FLatticePaper.H0Core Farey

/-- The canonical input of a free site: `z + prescribedH η z` on the H trace, `z + prescribedV η z` on the V cut. -/
noncomputable def canonicalInput (frame : ChildFrame) (η : ℤ) (z : Site) : Site :=
  if z ∈ frame.freeH then z + frame.prescribedH η z else z + frame.prescribedV η z

/-- A game fort of `F` for the sign `η` (the four rules above). -/
def IsGameFort (frame : ChildFrame) (η : ℤ) (F : Field) (S : Set Site) : Prop :=
  ∀ z ∈ S,
    (laplacian F z = -1 ∧ (incomingNeg z ∈ S ∨ incomingPos z ∈ S)) ∨
    (laplacian F z = 0 ∧ Nonfree frame z ∧ incomingNeg z ∈ S ∧ incomingPos z ∈ S) ∨
    (laplacian F z = 0 ∧ (z ∈ frame.freeH ∪ frame.freeV) ∧ canonicalInput frame η z ∈ S) ∨
    (laplacian F z = 0 ∧ z ∉ frame.freeH ∪ frame.freeV ∧ ¬ Nonfree frame z ∧
      (incomingNeg z ∈ S ∨ incomingPos z ∈ S))

/-- A free site is not nonfree (the zero translate). -/
theorem not_nonfree_of_free (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH ∪ frame.freeV) :
    ¬ Nonfree frame z := by
  intro hN
  have h0 : (0 : Site) ∈ frame.child.modifiedDeck.span := ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩
  have := hN 0 h0
  simp only [add_zero] at this
  exact this hz

/-- The even H prescribed direction is east. -/
theorem prescribedH_even (frame : ChildFrame) (η : ℤ) {z : Site} (hz : z ∈ frame.freeH) (he : EvenSite z) :
    frame.prescribedH η z = (1, 0) := by
  have hpar := FLatticePaper.W1Exit.child_parity frame
  have hF : z ≠ hFirst := by
    intro h; subst h; unfold EvenSite at he; simp only [hFirst] at he; omega
  have hL : z ≠ frame.hLast := by
    intro h; subst h; unfold EvenSite at he; simp only [ChildFrame.hLast] at he; omega
  unfold ChildFrame.prescribedH
  rw [if_neg hF, if_neg hL, if_pos he]

/-- The canonical input of an even free H root is its east neighbour, the input `incomingPos`. -/
theorem canonicalInput_H_even (frame : ChildFrame) (η : ℤ) {z : Site} (hz : z ∈ frame.freeH) (he : EvenSite z) :
    canonicalInput frame η z = (z.1 + 1, z.2) := by
  unfold canonicalInput
  rw [if_pos hz, prescribedH_even frame η hz he]
  ext <;> simp

/-- **The H route, east then north** (FIXED_FREE §3, the E–N route of an even free H root `z`). If `z` is a white free contact of the
game fort, then its east middle `u = z + (1,0)` is in `S`; if `u` is white, its north input `z + (1,1)` is in `S`. The middle `u` is nonfree
(`H_EN_middle_nonfree`), and its whiteness follows from the zero values of its three neighbours: `F u = 0` (strip), `F (north u) = 0` and
`F (south u) = 0` (even zero extension, `t(south u) = t z + n + d ≤ 2L − 2` since `t z ≤ L − 2`). -/
theorem game_EN {F : Field} {S : Set Site} (frame : ChildFrame) (η : ℤ) (hP : frame.Packet F)
    (hG : IsGameFort frame η F S)
    (hEZ : ∀ w : Site, EvenSite w → 1 - frame.child.den ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {z : Site} (hzS : z ∈ S) (hzH : z ∈ frame.freeH) (hev : EvenSite z) (hzW : laplacian F z = 0)
    (hzcl : z ∈ frame.closedPolygon) (hT : frame.child.den - frame.child.num + 2 ≤ frame.tGrade z)
    (hS : frame.sGrade z < frame.child.periodDenominator + 2 - 2 * frame.child.den) :
    (z.1 + 1, z.2 + 1) ∈ S := by
  have hsp : frame.hSpectrum (frame.tGrade z) := hzH.2.2
  have ht2 : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · have : ¬ (frame.tGrade z % 2 = 1) := by
        rw [FLatticePaper.Induction.tGrade_parity frame z]
        unfold EvenSite at hev
        omega
      omega
  have hu_can : canonicalInput frame η z = (z.1 + 1, z.2) := canonicalInput_H_even frame η hzH hev
  have hzfree : z ∈ frame.freeH ∪ frame.freeV := Or.inl hzH
  have hu_S : (z.1 + 1, z.2) ∈ S := by
    rcases hG z hzS with ⟨hl, -⟩ | ⟨-, hnf, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, hnfree, -, -⟩
    · rw [hzW] at hl; norm_num at hl
    · exact absurd hnf (not_nonfree_of_free frame hzfree)
    · rw [hu_can] at hc; exact hc
    · exact absurd hzfree hnfree
  -- the middle `u = z + (1,0)` is nonfree (ShortPassages) and white (zero values of its neighbours)
  have hu_nf : Nonfree frame (z.1 + 1, z.2) := by
    have h := FLatticePaper.Induction.ShortPassages.H_EN_middle_nonfree frame z hev hzcl hT hS
    have e : z + ((1 : ℤ), (0 : ℤ)) = (z.1 + 1, z.2) := by ext <;> simp
    rw [e] at h
    exact h
  have hu_odd : ¬ EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hu_white : laplacian F (z.1 + 1, z.2) = 0 := by
    have hin : incomingNeg (z.1 + 1, z.2) = (z.1 + 1, z.2 - 1) := incomingNeg_of_not_even _ hu_odd
    have hip : incomingPos (z.1 + 1, z.2) = (z.1 + 1, z.2 + 1) := incomingPos_of_not_even _ hu_odd
    unfold laplacian
    rw [hin, hip]
    have hev_s : EvenSite (z.1 + 1, z.2 - 1) := by unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
    have hev_n : EvenSite (z.1 + 1, z.2 + 1) := by unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
    have ht_u : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
      unfold ChildFrame.tGrade; ring
    have ht_s : frame.tGrade (z.1 + 1, z.2 - 1) = frame.tGrade z + frame.child.num + frame.child.den := by
      unfold ChildFrame.tGrade; ring
    have ht_n : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
      unfold ChildFrame.tGrade; ring
    obtain ⟨hn, hnd, hd2, -, -⟩ := frame.child_facts
    have hF_s : F (z.1 + 1, z.2 - 1) = 0 := by
      apply hEZ _ hev_s
      · rw [ht_s]; omega
      · rw [ht_s]; omega
    have hF_n : F (z.1 + 1, z.2 + 1) = 0 := by
      apply hEZ _ hev_n
      · rw [ht_n]; omega
      · rw [ht_n]; omega
    have hF_u : F (z.1 + 1, z.2) = 0 := by
      apply hP.strips.1 _
      · rw [ht_u]; omega
      · rw [ht_u]; omega
    rw [hF_s, hF_n, hF_u]
    ring
  -- the white nonfree middle has both inputs in `S`: its north input is `z + (1,1)`
  have hu_both : incomingNeg (z.1 + 1, z.2) ∈ S ∧ incomingPos (z.1 + 1, z.2) ∈ S := by
    rcases hG (z.1 + 1, z.2) hu_S with ⟨hl, -⟩ | ⟨-, -, hn, hp⟩ | ⟨-, hfree, -⟩ | ⟨-, -, hnf, -⟩
    · rw [hu_white] at hl; norm_num at hl
    · exact ⟨hn, hp⟩
    · exact absurd hu_nf (not_nonfree_of_free frame hfree)
    · exact absurd hu_nf hnf
  have hip : incomingPos (z.1 + 1, z.2) = (z.1 + 1, z.2 + 1) := incomingPos_of_not_even _ hu_odd
  rw [hip] at hu_both
  exact hu_both.2

/-- The odd V prescribed direction is `(0, −η)` (north for `η = −1`); `V_0` and `V_last` are even. -/
theorem prescribedV_odd (frame : ChildFrame) (η : ℤ) {z : Site} (ho : ¬ EvenSite z) :
    frame.prescribedV η z = (0, -η) := by
  have hF : z ≠ vFirst := by
    intro h; subst h; apply ho; unfold EvenSite; simp [vFirst]
  have hL : z ≠ frame.vLast := by
    intro h; subst h; apply ho; unfold EvenSite; simp only [ChildFrame.vLast]; ring_nf; omega
  unfold ChildFrame.prescribedV
  rw [if_neg hF, if_neg hL, if_neg ho]

/-- The even internal V prescribed direction is `(η, 0)` (west for `η = −1`). -/
theorem prescribedV_even (frame : ChildFrame) (η : ℤ) {z : Site} (he : EvenSite z) (hF : z ≠ vFirst)
    (hL : z ≠ frame.vLast) : frame.prescribedV η z = (η, 0) := by
  unfold ChildFrame.prescribedV
  rw [if_neg hF, if_neg hL, if_pos he]

/-- **The V route, north then west** (FIXED_FREE §4, ascending V with `η = −1`): an odd free V root `z` that is a white free
contact of the game fort has its north middle `u = z + (0,1)` in `S`; if `u` is white, its west input `z + (−1,1)` is in `S`.
The middle `u` is nonfree (`V_NW_middle_nonfree`); its whiteness is the named input `hu_white` (the audit's §1 and §6 remark
that the whiteness of the middles is essential; for the V middles it is not derived here). -/
theorem game_NW {F : Field} {S : Set Site} (frame : ChildFrame) (hG : IsGameFort frame (-1) F S)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ frame.freeV) (hzH : z ∉ frame.freeH) (ho : ¬ EvenSite z)
    (hzW : laplacian F z = 0)
    (hS1 : 2 * frame.child.num + 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hS2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2)
    (ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator + frame.child.den < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.den)
    (hu_white : laplacian F (z.1, z.2 + 1) = 0) :
    (z.1 - 1, z.2 + 1) ∈ S := by
  have hzfree : z ∈ frame.freeH ∪ frame.freeV := Or.inr hzV
  have hcan : canonicalInput frame (-1) z = (z.1, z.2 + 1) := by
    unfold canonicalInput
    rw [if_neg hzH, prescribedV_odd frame (-1) ho]
    ext <;> simp
  have hu_S : (z.1, z.2 + 1) ∈ S := by
    rcases hG z hzS with ⟨hl, -⟩ | ⟨-, hnf, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, hnfree, -, -⟩
    · rw [hzW] at hl; norm_num at hl
    · exact absurd hnf (not_nonfree_of_free frame hzfree)
    · rw [hcan] at hc; exact hc
    · exact absurd hzfree hnfree
  have hu_even : EvenSite (z.1, z.2 + 1) := by unfold EvenSite at ho ⊢; simp only at ho ⊢; omega
  have hu_nf : Nonfree frame (z.1, z.2 + 1) := by
    have h := FLatticePaper.Induction.ShortPassages.V_NW_middle_nonfree frame z ho hS1 hS2 ht1 ht2
    rw [show z + ((0 : ℤ), (1 : ℤ)) = (z.1, z.2 + 1) by ext <;> simp] at h
    exact h
  have hu_both : incomingNeg (z.1, z.2 + 1) ∈ S ∧ incomingPos (z.1, z.2 + 1) ∈ S := by
    rcases hG (z.1, z.2 + 1) hu_S with ⟨hl, -⟩ | ⟨-, -, hn, hp⟩ | ⟨-, hfree, -⟩ | ⟨-, -, hnf, -⟩
    · rw [hu_white] at hl; norm_num at hl
    · exact ⟨hn, hp⟩
    · exact absurd hu_nf (not_nonfree_of_free frame hfree)
    · exact absurd hu_nf hnf
  have hin : incomingNeg (z.1, z.2 + 1) = (z.1 - 1, z.2 + 1) := incomingNeg_of_even _ hu_even
  rw [hin] at hu_both
  exact hu_both.1

/-- **The V route, west then north then east** (FIXED_FREE §4, the W,N,E route of an even internal V root `z` with `η = −1`): the west
middle `u = z + (−1,0)` (odd, nonfree by `V_WNE_middle0_nonfree`) is in `S`; if white, its north input `m = z + (−1,1)` (even, nonfree by
`V_WNE_middle1_nonfree`) is in `S`; if `m` is white, its east input `z + (0,1)` is in `S`. The whiteness of `u` and `m` is the named inputs
`hu_white`, `hm_white`. -/
theorem game_WNE {F : Field} {S : Set Site} (frame : ChildFrame) (hG : IsGameFort frame (-1) F S)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ frame.freeV) (hzH : z ∉ frame.freeH) (he : EvenSite z)
    (hF : z ≠ vFirst) (hL : z ≠ frame.vLast) (hzW : laplacian F z = 0)
    (hS1 : 2 ≤ frame.sGrade z) (hS2 : frame.sGrade z ≤ 2 * frame.child.num - 2)
    (ht1 : 2 * (frame.child.num + frame.child.den) - 1 - frame.child.periodDenominator < frame.tGrade z)
    (ht2 : frame.tGrade z < frame.child.num)
    (hu_white : laplacian F (z.1 - 1, z.2) = 0)
    (hm_white : laplacian F (z.1 - 1, z.2 + 1) = 0) :
    (z.1, z.2 + 1) ∈ S := by
  have hzfree : z ∈ frame.freeH ∪ frame.freeV := Or.inr hzV
  have hcan : canonicalInput frame (-1) z = (z.1 - 1, z.2) := by
    unfold canonicalInput
    rw [if_neg hzH, prescribedV_even frame (-1) he hF hL]
    ext <;> simp [sub_eq_add_neg]
  have hu_S : (z.1 - 1, z.2) ∈ S := by
    rcases hG z hzS with ⟨hl, -⟩ | ⟨-, hnf, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, hnfree, -, -⟩
    · rw [hzW] at hl; norm_num at hl
    · exact absurd hnf (not_nonfree_of_free frame hzfree)
    · rw [hcan] at hc; exact hc
    · exact absurd hzfree hnfree
  have hu_odd : ¬ EvenSite (z.1 - 1, z.2) := by unfold EvenSite at he ⊢; simp only at he ⊢; omega
  have hu_nf : Nonfree frame (z.1 - 1, z.2) := by
    have h := FLatticePaper.Induction.ShortPassages.V_WNE_middle0_nonfree frame z he hS1 hS2 ht1 ht2
    rw [show z + ((-1 : ℤ), (0 : ℤ)) = (z.1 - 1, z.2) by ext <;> simp [sub_eq_add_neg]] at h
    exact h
  have hm_S : (z.1 - 1, z.2 + 1) ∈ S := by
    rcases hG (z.1 - 1, z.2) hu_S with ⟨hl, -⟩ | ⟨-, -, hn, hp⟩ | ⟨-, hfree, -⟩ | ⟨-, -, hnf, -⟩
    · rw [hu_white] at hl; norm_num at hl
    · have hip : incomingPos (z.1 - 1, z.2) = (z.1 - 1, z.2 + 1) := incomingPos_of_not_even _ hu_odd
      rw [hip] at hp; exact hp
    · exact absurd hu_nf (not_nonfree_of_free frame hfree)
    · exact absurd hu_nf hnf
  have hm_even : EvenSite (z.1 - 1, z.2 + 1) := by unfold EvenSite at he ⊢; simp only at he ⊢; omega
  have hm_nf : Nonfree frame (z.1 - 1, z.2 + 1) := by
    have h := FLatticePaper.Induction.ShortPassages.V_WNE_middle1_nonfree frame z he hS1 hS2 ht1 ht2
    rw [show z + ((-1 : ℤ), (1 : ℤ)) = (z.1 - 1, z.2 + 1) by ext <;> simp [sub_eq_add_neg]] at h
    exact h
  have hm_both : incomingNeg (z.1 - 1, z.2 + 1) ∈ S ∧ incomingPos (z.1 - 1, z.2 + 1) ∈ S := by
    rcases hG (z.1 - 1, z.2 + 1) hm_S with ⟨hl, -⟩ | ⟨-, -, hn, hp⟩ | ⟨-, hfree, -⟩ | ⟨-, -, hnf, -⟩
    · rw [hm_white] at hl; norm_num at hl
    · exact ⟨hn, hp⟩
    · exact absurd hm_nf (not_nonfree_of_free frame hfree)
    · exact absurd hm_nf hnf
  have hip : incomingPos (z.1 - 1, z.2 + 1) = (z.1, z.2 + 1) := by
    rw [incomingPos_of_even _ hm_even]; ext <;> simp
  rw [hip] at hm_both
  exact hm_both.2


/-- The canonical input of a free site is one of its two actual inputs (`η = ±1`). -/
theorem canonicalInput_is_input (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ frame.freeH ∪ frame.freeV) :
    canonicalInput frame η z = incomingNeg z ∨ canonicalInput frame η z = incomingPos z := by
  by_cases hH : z ∈ frame.freeH
  · unfold canonicalInput
    rw [if_pos hH]
    by_cases he : EvenSite z
    · rw [prescribedH_even frame η hH he, incomingPos_of_even _ he]
      right
      ext <;> simp
    · by_cases hF : z = hFirst
      · subst hF
        rw [frame.prescribedH_hFirst η]
        rw [incomingNeg_of_not_even _ he, incomingPos_of_not_even _ he]
        rcases hη with rfl | rfl
        · left; ext <;> simp [sub_eq_add_neg]
        · right; ext <;> simp
      · by_cases hL : z = frame.hLast
        · unfold ChildFrame.prescribedH
          rw [if_neg hF, if_pos hL, incomingPos_of_not_even _ he]
          right
          ext <;> simp
        · unfold ChildFrame.prescribedH
          rw [if_neg hF, if_neg hL, if_neg he, incomingPos_of_not_even _ he]
          right
          ext <;> simp
  · have hVz : z ∈ frame.freeV := hz.resolve_left hH
    unfold canonicalInput
    rw [if_neg hH]
    by_cases he : EvenSite z
    · by_cases hF : z = vFirst
      · subst hF
        rw [frame.prescribedV_vFirst η, incomingPos_of_even _ he]
        right
        ext <;> simp
      · by_cases hL : z = frame.vLast
        · unfold ChildFrame.prescribedV
          rw [if_neg hF, if_pos hL, incomingPos_of_even _ he, incomingNeg_of_even _ he]
          rcases hη with rfl | rfl
          · right; ext <;> simp
          · left; ext <;> simp [sub_eq_add_neg]
        · rw [prescribedV_even frame η he hF hL, incomingPos_of_even _ he, incomingNeg_of_even _ he]
          rcases hη with rfl | rfl
          · right; ext <;> simp
          · left; ext <;> simp [sub_eq_add_neg]
    · rw [prescribedV_odd frame η he, incomingPos_of_not_even _ he, incomingNeg_of_not_even _ he]
      rcases hη with rfl | rfl
      · left; ext <;> simp [sub_eq_add_neg]
      · right; ext <;> simp

/-- **The free white rule as a forced input** (the table's content in the game form): a free white root `z` of a game fort `S` has its
canonical input in `S`, and the canonical input is one of its actual inputs. -/
theorem free_white_forced_input {F : Field} {S : Set Site} (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hG : IsGameFort frame η F S) {z : Site} (hzS : z ∈ S) (hzf : z ∈ frame.freeH ∪ frame.freeV)
    (hzW : laplacian F z = 0) :
    canonicalInput frame η z ∈ S ∧
      (canonicalInput frame η z = incomingNeg z ∨ canonicalInput frame η z = incomingPos z) := by
  refine ⟨?_, canonicalInput_is_input frame η hη hzf⟩
  rcases hG z hzS with ⟨hl, -⟩ | ⟨-, hnf, -, -⟩ | ⟨-, -, hc⟩ | ⟨-, hnfree, -, -⟩
  · rw [hzW] at hl; norm_num at hl
  · exact absurd hnf (not_nonfree_of_free frame hzf)
  · exact hc
  · exact absurd hzf hnfree

end FLatticePaper.GameFort
