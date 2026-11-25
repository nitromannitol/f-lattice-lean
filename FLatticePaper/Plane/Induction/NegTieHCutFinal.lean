import FLatticePaper.Plane.Induction.FreeVReverse
import FLatticePaper.Plane.Induction.NegTieHCut
import FLatticePaper.Plane.Induction.NegTieFreeV
import FLatticePaper.Plane.Induction.NegTieTranslate
import FLatticePaper.Plane.Induction.NoBlackPair
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.Q3Para10
import FLatticePaper.Plane.Induction.CornerPositive

/-! Task Q21 (G) and (I): the negative tied target is impossible in the conjugate H cut.

The hypothesis `hQ21` of `negTie_false_of_V_block` is the statement `H_cut_hQ21` below. Its proof: the offers force
`a = 1` (`H_cut_a_eq_one`); the reversed root is then `x = v + (−b) U_p` with `v` a point of the word's free V cut
(`freeV_of_conj_freeH` off the corner, `freeV_corner_of_eps_neg` on the corner for `ε = −1`), and the two black centres
of the rising pair contradict the free V cut (`black_centres_contradiction`). On the corner for `ε = +1` the index is
`0` (`exceptional_i_zero`), so the root is `V_p + I` itself, and the tie `sheetDiffW c = 0` is excluded by `sheetDiffW_corner_ge_one` (the sheet difference at `V_p + I` is at least `1` for `ε = +1`, Q27). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The sheet shift is `0` when `ε = 1`. -/
theorem sheetShift_eps_one (frame : ChildFrame) (he : frame.eps = 1) : frame.sheetShift = 0 := by
  simp [ChildFrame.sheetShift, ChildFrame.phaseW, he]

/-- The sheet shift is the even kernel `U_q` when `ε = −1`. -/
theorem sheetShift_eps_neg_one (frame : ChildFrame) (he : frame.eps = -1) :
    frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
  simp [ChildFrame.sheetShift, ChildFrame.phaseW, he, Fraction.unmodifiedDeck]

/-- The two black centres of a rising pair: `x = c − shS` and `x + U_q`, both with Laplacian `−1`. -/
theorem rising_black_shS {word : Word} (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i) :
    laplacian (standardField word) (c - (frameAt word).sheetShift) = -1 ∧
      laplacian (standardField word) (c - (frameAt word).sheetShift +
        ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) = -1 := by
  rcases (frameAt word).eps_unit with he | he
  · rw [sheetShift_eps_one (frameAt word) he, sub_zero]
    refine ⟨hr.2.1, ?_⟩
    have e : c + ((frameAt word).parents.even.den, (frameAt word).parents.even.num) -
        ((frameAt word).child.den, (frameAt word).child.num) = c + -(frameAt word).shortShift := by
      unfold ChildFrame.shortShift
      rw [he]
      obtain ⟨hd, hn, -⟩ := (frameAt word).linear_facts
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] <;>
        omega
    have h1 := (frameAt word).laplacian_sub_child_kernel hpk
      (c + ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
    rw [e] at h1
    rw [← h1]
    exact hr.2.2.2.1
  · rw [sheetShift_eps_neg_one (frameAt word) he]
    constructor
    · have e : c - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) =
          (c + -(frameAt word).shortShift) - ((frameAt word).child.den, (frameAt word).child.num) := by
        unfold ChildFrame.shortShift
        rw [he]
        obtain ⟨hd, hn, -⟩ := (frameAt word).linear_facts
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] <;>
          omega
      rw [e, (frameAt word).laplacian_sub_child_kernel hpk]
      exact hr.2.2.2.1
    · rw [sub_add_cancel]
      exact hr.2.1

/-- The root and its upper neighbour are in the closed polygon, for a rising pair with `c, c + U_q ∈ E`. -/
theorem root_mem_of_rising {word : Word} {c : Site} (hcE : c ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon) :
    c - (frameAt word).sheetShift ∈ (frameAt word).closedPolygon ∧
      c - (frameAt word).sheetShift + ((frameAt word).parents.even.den, (frameAt word).parents.even.num) ∈
        (frameAt word).closedPolygon := by
  have hu1 : (frameAt word).eps = 1 → (frameAt word).uq = ((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    intro he
    unfold ChildFrame.uq
    rw [he]
    simp
  have hu2 : (frameAt word).eps = -1 →
      (frameAt word).uq = -((frameAt word).parents.even.den, (frameAt word).parents.even.num) := by
    intro he
    unfold ChildFrame.uq
    rw [he]
    ext <;> simp
  rcases (frameAt word).eps_unit with he | he
  · rw [sheetShift_eps_one (frameAt word) he, sub_zero, ← hu1 he]
    exact ⟨hcE, hcu⟩
  · have e : c - ((frameAt word).parents.even.den, (frameAt word).parents.even.num) = c + (frameAt word).uq := by
      rw [hu2 he]
      ext <;> simp [sub_eq_add_neg]
    rw [sheetShift_eps_neg_one (frameAt word) he]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hcu
    · rw [sub_add_cancel]
      exact hcE

/-- The black centres of a rising pair against a free V vertex of the word: `x = v + (−b) U_p` is impossible. -/
theorem H_cut_black_contra {word : Word} (_h : ∃ x ∈ word, x ≠ Digit.three)
    (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon) {b : ℤ} {v : Site}
    (hv : v ∈ (frameAt word).freeV)
    (hxv : c - (frameAt word).sheetShift =
      v + ((-b) * (2 * (frameAt word).parents.odd.den), (-b) * (2 * (frameAt word).parents.odd.num))) : False := by
  obtain ⟨hb, hbu⟩ := rising_black_shS hpk hr
  obtain ⟨hxE, hxuE⟩ := root_mem_of_rising hcE hcu
  exact (frameAt word).black_centres_contradiction hpk hv hxv hxE hxuE hb hbu

/-- **The conjugate H-cut translate case (Q21), the input of `negTie_false_of_V_block`.** With the corner bound `sheetDiffW_corner_ge_one` (Q27), no conjugate free H translate of the negative tied root exists. -/
theorem H_cut_hQ21 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    {c i : Site} (hr : RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i)
    (hcE : c ∈ (frameAt word).closedPolygon) (hiE : i ∈ (frameAt word).closedPolygon)
    (hcu : c + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hiu : i + (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : sheetDiffW word c = 0) {j : Site} (hj : FLatticePaper.Edge j c)
    (hjΨ : sheetDiffW word j ≤ -1) (hΨi : 0 ≤ sheetDiffW word i) :
    ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
      zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False := by
  intro v hv hf
  obtain ⟨a, b, rfl⟩ := hv
  have hxy := negTie_jumps h hSE hpk P hslip hr hcE hiE hcu hiu hΨc hj hjΨ hΨi
  have hyx : i - (frameAt word).sheetShift = incomingNeg (c - (frameAt word).sheetShift) ∨
      i - (frameAt word).sheetShift = incomingPos (c - (frameAt word).sheetShift) := by
    have hsn : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
    have hsneg : ((-(frameAt word).sheetShift).1 + (-(frameAt word).sheetShift).2) % 2 = 0 := by
      have hs := hsn
      unfold EvenSite at hs
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    rcases hr.1 with h1 | h1
    · left
      rw [sub_eq_add_neg c, incomingNeg_add_even _ _ hsneg, h1, sub_eq_add_neg]
    · right
      rw [sub_eq_add_neg c, incomingPos_add_even _ _ hsneg, h1, sub_eq_add_neg]
  have ha := H_cut_a_eq_one h hSE (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift) a b hyx
    hxy.1 hxy.2 hf
  subst ha
  have hvstar := vStar_eq h (c - (frameAt word).sheetShift) 1 b
  set x : Site := c - (frameAt word).sheetShift with hxdef
  set w : Site := zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine 1 b with hwdef
  have hxv : x = ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) +
      ((-b) * (2 * (frameAt word).parents.odd.den), (-b) * (2 * (frameAt word).parents.odd.num)) := by
    rw [hvstar]
    ext <;> simp
  by_cases hcorner : w = (1, 0)
  · have hw1 : w.1 = 1 := by rw [hcorner]
    have hw2 : w.2 = 0 := by rw [hcorner]
    have hvpt : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) =
        ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) :=
      Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    rw [hvpt] at hxv
    by_cases heps : (frameAt word).eps = 1
    · obtain ⟨hxE, hxuE⟩ := root_mem_of_rising hcE hcu
      have hxE' : x ∈ (frameAt word).closedPolygon := hxE
      have hxuE' : x + ((frameAt word).parents.even.den, (frameAt word).parents.even.num) ∈
          (frameAt word).closedPolygon := hxuE
      have hDN : (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1 =
          (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by ring
      have hxexc : x = ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
          (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1) +
          ((-b) * (2 * (frameAt word).parents.odd.den), (-b) * (2 * (frameAt word).parents.odd.num)) := by
        rw [hxv, hDN]
      have hi := (frameAt word).exceptional_i_zero heps x (-b) hxexc hxE' hxuE'
      have hb0 : b = 0 := by omega
      have hxeq : x = ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) := by
        rw [hxv, hb0]
        simp
      have hcx : c = x := by
        rw [hxdef, sheetShift_eps_one (frameAt word) heps, sub_zero]
      rw [hcx, hxeq] at hΨc
      have hge := sheetDiffW_corner_ge_one h hSE heps
      omega
    · have heps' : (frameAt word).eps = -1 := (frameAt word).eps_unit.resolve_left heps
      have hvfree := freeV_corner_of_eps_neg h heps'
      exact H_cut_black_contra h hpk hr hcE hcu hvfree hxv
  · have hvfree := freeV_of_conj_freeH h hf hcorner
    exact H_cut_black_contra h hpk hr hcE hcu hvfree hxv

end FLatticePaper.Induction
