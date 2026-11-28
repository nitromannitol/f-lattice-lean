import FLatticePaper.Tiles.LStepAssembly
import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.LCorrecRecursion

/-! Local height differences between consecutive stems in the two L-corrections.
The register translation determines the difference on their whole intersection,
including the initial affine factor of the L. -/

namespace FLatticePaper.Tiles.LStemCompat

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SurgicalAlt FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointInduction FLatticePaper.Tiles.JointGlue
open FLatticePaper.Tiles.LStepAssembly

private theorem neg_coords (v : Site) : (-v.1, -v.2) = -v := rfl
private theorem zero_coords : ((0, 0) : Site) = 0 := rfl
attribute [local simp] neg_coords zero_coords

private theorem negStep {o : PartialOdometer} {v a : Site} (h : LatticeSelfCompatible o v a) :
    LatticeSelfCompatible o (-v) (-a) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨dotS a v - K, fun x hx hy => ?_⟩
  have H := hK (x + -v) hy (by simpa using hx)
  simp only [neg_add_cancel_right] at H
  simp only [dotS, Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add] at H ⊢
  linear_combination -H

private theorem adjacent (o : PartialOdometer) (v a c s : Site) (h : LatticeSelfCompatible o v a) :
    ∃ C : ℤ, ∀ z ∈ (stdPiece o c s).placed, z ∈ (stdPiece o (c + v) (s + a)).placed →
      pieceVal (stdPiece o c s) z - pieceVal (stdPiece o (c + v) (s + a)) z = C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K - dotS a (c + v), fun z hp hq => ?_⟩
  have he : z - (c + v) + v = z - c := by abel
  have hp' : z - c ∈ o.dom := JointRot.mem_placed.mp hp
  have hq' : z - (c + v) ∈ o.dom := JointRot.mem_placed.mp hq
  have H := hK _ hq' (he.symm ▸ hp')
  rw [he] at H
  simp only [pieceVal, stdPiece, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at H ⊢
  linear_combination H

private theorem strip_run (d : Digit) (u : Word) (k : ℕ) :
    stripTrailing d (u ++ List.replicate k d) = stripTrailing d u := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ', ← List.append_assoc, JointRot.stripTrailing_snoc, if_pos rfl, ih]

private theorem odd_reg (w : Word) (hw : OddLDefined w) :
    ∃ u, (regsAt (stripTrailing .two w)).2 = some u := by
  obtain ⟨u, s, k, hs, rfl⟩ := hw
  refine ⟨u, ?_⟩
  rw [strip_run, JointRot.stripTrailing_snoc, if_neg hs, JointRot.regsAt_append_singleton]
  cases s <;> first | rfl | contradiction

private theorem even_reg (w : Word) (hw : EvenLDefined w) :
    ∃ u, (regsAt (stripTrailing .three w)).1 = some u := by
  obtain ⟨u, s, k, hs, rfl⟩ := hw
  refine ⟨u, ?_⟩
  rw [strip_run, JointRot.stripTrailing_snoc, if_neg hs, JointRot.regsAt_append_singleton]
  cases s <;> first | rfl | contradiction

private theorem first_entries (n i : ℕ) (g : ℕ → Piece) (tail : List Piece) (hi : i < n) :
    (((List.range n).map g) ++ tail)[i]? = some (g i) := by
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

private theorem aff_smul (w : Word) (k : ℤ) (K : AltCoeff) : altAff w (k • K) = k • altAff w K := by
  ext <;> simp [altAff, coeffAffine] <;> ring

private def stem (o : PartialOdometer) (pre : Word) (c s : Site) (K : AltCoeff) (i : ℕ) :=
  stdPiece o (c + altOff pre ((i : ℤ) • K)) (s + altAff pre ((i : ℤ) • K))

private theorem two_stems (o : PartialOdometer) (pre : Word) (c s : Site) (K : AltCoeff)
    (h : LatticeSelfCompatible o (altOff pre K) (altAff pre K)) (i : ℕ) :
    ∃ C : ℤ, ∀ z ∈ (stem o pre c s K i).placed, z ∈ (stem o pre c s K (i+1)).placed →
      pieceVal (stem o pre c s K i) z - pieceVal (stem o pre c s K (i+1)) z = C := by
  simp only [stem, LCorrecRecursion.altOff_smul, aff_smul]
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, ← add_assoc]
  apply adjacent _ _ _ _ _ h

private theorem on_parts (ps : List Piece) (i j : Fin ps.length) (p q : Piece)
    (hi : ps[i.val]? = some p) (hj : ps[j.val]? = some q)
    (h : ∃ C : ℤ, ∀ z ∈ p.placed, z ∈ q.placed → pieceVal p z - pieceVal q z = C) :
    ∃ C : ℤ, ∀ x ∈ goodPart ps i ∩ goodPart ps j, pieceVal (ps.get i) x.val - pieceVal (ps.get j) x.val = C := by
  have ei : ps.get i = p := by simpa only [List.get_eq_getElem, List.getElem?_eq_getElem i.isLt, Option.some.injEq] using hi
  have ej : ps.get j = q := by simpa only [List.get_eq_getElem, List.getElem?_eq_getElem j.isLt, Option.some.injEq] using hj
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨⟨hx1, -⟩, ⟨hx2, -⟩⟩ := hx
  rw [ei, ej]
  exact hC x.val (ei ▸ hx1) (ej ▸ hx2)

/-- The local input to the glue for any two consecutive stems of an odd L. -/
theorem odd_stems (D : JointData) (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length)
    (hw : OddLDefined w) (plus elong : Bool) (i j : Fin (oddPs D f w plus elong).length)
    (hij : i.val + 1 = j.val) (hj : j.val ≤ trailingCount .two w) :
    ∃ C : ℤ, ∀ x ∈ goodPart (oddPs D f w plus elong) i ∩ goodPart (oddPs D f w plus elong) j,
      pieceVal ((oddPs D f w plus elong).get i) x.val - pieceVal ((oddPs D f w plus elong).get j) x.val = C := by
  let pre := stripTrailing .two w
  let K := (oddKCoeff (W1Odd w) plus).1
  obtain ⟨u, hu⟩ := odd_reg w hw
  have hl := lt_of_lt_of_le (regsAt_lt pre u (Or.inr hu)) (JointRot.stripTrailing_length_le .two w)
  have ht := (hg u hl).2.2.1.2.1
  have H : LatticeSelfCompatible (f u).tEven (vQ2 pre) (aQ2 pre) := by
    simpa only [LatticeSelfCompatible, vQ2, aQ2, ← (JointRot.parents_of_regs pre).2 u hu] using WeakStepAssembly.translation_v2 _ _ _ _ ht
  have hc : LatticeSelfCompatible (f u).tEven (altOff pre K) (altAff pre K) := by
    cases ho : W1Odd w <;> cases hp : plus <;> first
      | simpa [K, ho, hp, oddKCoeff, altOff, coeffOff, altAff, coeffAffine, aQ2, offsetA] using H
      | simpa [K, ho, hp, oddKCoeff, altOff, coeffOff, altAff, coeffAffine, aQ2, offsetA] using negStep H
  let g := stem (f u).tEven pre (oddLInitOff w plus) (oddLInitAff w plus) K
  have entry (n : ℕ) (hn : n ≤ trailingCount .two w) : (oddPs D f w plus elong)[n]? = some (g n) := by
    unfold oddPs oddLPieces
    simp only [hu, regOdo, below, if_pos hl, List.append_assoc]
    exact first_entries _ n _ _ (by omega)
  exact on_parts _ i j _ _ (entry i (by omega)) (entry j hj)
    (by simpa only [← hij] using two_stems _ _ _ _ _ hc i.val)

/-- The local input to the glue for any two consecutive stems of an even L. -/
theorem even_stems (D : JointData) (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length)
    (hw : EvenLDefined w) (plus elong : Bool) (i j : Fin (evenPs D f w plus elong).length)
    (hij : i.val + 1 = j.val) (hj : j.val ≤ trailingCount .three w) :
    ∃ C : ℤ, ∀ x ∈ goodPart (evenPs D f w plus elong) i ∩ goodPart (evenPs D f w plus elong) j,
      pieceVal ((evenPs D f w plus elong).get i) x.val - pieceVal ((evenPs D f w plus elong).get j) x.val = C := by
  let pre := stripTrailing .three w
  let s2 : Bool := decide (pre.getLast? = some Digit.two)
  let K := (evenKCoeff (W1Odd w) plus s2).1
  obtain ⟨u, hu⟩ := even_reg w hw
  have hl := lt_of_lt_of_le (regsAt_lt pre u (Or.inl hu)) (JointRot.stripTrailing_length_le .three w)
  have ht := (hg u hl).2.2.1.1
  have H : LatticeSelfCompatible (f u).tOdd (vP1 pre) 0 := by
    simpa [LatticeSelfCompatible, vP1, ← (JointRot.parents_of_regs pre).1 u hu, dotS]
      using WeakStepAssembly.translation_v1 _ _ _ _ ht
  have hc : LatticeSelfCompatible (f u).tOdd (altOff pre K) (altAff pre K) := by
    cases ho : W1Odd w <;> cases hp : plus <;> cases hs : s2 <;> first
      | simpa [K, ho, hp, hs, evenKCoeff, altOff, coeffOff, altAff, coeffAffine] using H
      | simpa [K, ho, hp, hs, evenKCoeff, altOff, coeffOff, altAff, coeffAffine] using negStep H
  let g := stem (f u).tOdd pre (evenLInitOff w plus) (evenLInitAff w plus) K
  have entry (n : ℕ) (hn : n ≤ trailingCount .three w) : (evenPs D f w plus elong)[n]? = some (g n) := by
    unfold evenPs evenLPieces
    simp only [hu, regOdo, below, if_pos hl, List.append_assoc]
    exact first_entries _ n _ _ (by omega)
  exact on_parts _ i j _ _ (entry i (by omega)) (entry j hj)
    (by simpa only [← hij] using two_stems _ _ _ _ _ hc i.val)

end FLatticePaper.Tiles.LStemCompat
