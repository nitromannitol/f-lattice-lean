import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1MReflect
import FLatticePaper.Plane.Induction.W1MRank
import FLatticePaper.Plane.Induction.W1Hagree
import FLatticePaper.Plane.Induction.SheetReflection

/-! # Task 85 (final): hagree at M-white ties, from the A descent and the centre reflection

For an M-white sheet tie `c` (the sheets agree at `c`, and the sheet minimum is white there), with the centre `K₀ = frame.centre` of the sheet
exchange and a quota policy `Q` of the conjugate (the retained relation):

* the A descent (`a_arrow_forced`) gives an input `o` of `c`, retained by the A policy, with `ForcedEdge M c o`;
* the sheet exchange makes the laplacian of `M` centre-invariant, so `ForcedEdge M (K₀ − c) (K₀ − o)` (`forcedEdge_reflect`);
* the A descent at the reflected tie `K₀ − c` gives its forced input `o'`; uniqueness of the M-forced target (`forced_input_unique` with
  `sheetMin_hasSat_of_strong`) gives `o' = K₀ − o`;
* so the C policy retains `o` at `c`, and the A pointer of `c` is `o` (the rejected input of the square is not retained).

Discharged here: the sheet exchange `hX` (`sheetExchange_of_packet`, from the packet of the conjugate), and the rank increments `hinc` of
the F2F3 policy (`exists_F2F3_increments`, from the reduced strong residual). Named: the square data `hsq` for the policy `Q`. -/

namespace FLatticePaper.W1MFinal

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1MSheet FLatticePaper.W1MReflect FLatticePaper.W1MDescent FLatticePaper.W1Hagree

/-- The pointer of a relation at `c` is the retained input `o`, when `o` is retained, the rejected input `p0` is not, and both are inputs. -/
theorem pointerOf_eq_of (Q : Site → Site → Prop) (c o p0 : Site)
    (ho : o = incomingNeg c ∨ o = incomingPos c) (hp0 : p0 = incomingNeg c ∨ p0 = incomingPos c)
    (hQo : Q c o) (hQp0 : ¬ Q c p0) (hne : o ≠ p0) :
    FLatticePaper.W1Pointers.pointerOf Q c = o := by
  unfold FLatticePaper.W1Pointers.pointerOf
  classical
  split_ifs with hn
  · -- the neg input is retained, hence not the rejected input
    have hnp : incomingNeg c ≠ p0 := fun e => hQp0 (e ▸ hn)
    exact input_unique_of_ne (Or.inl rfl) ho hp0 hnp hne
  · rcases ho with ho | ho
    · exact absurd (ho ▸ hQo) hn
    · exact ho.symm

/-- The neighbour reflection of the Laplacian: the laplacian of `M` is invariant under the centre reflection. -/
theorem laplacian_reflect_of (M : Field) (K0 : Site) (hK0 : (K0.1 + K0.2) % 2 = 0)
    (t : Site → ℤ) (κ : ℤ) (ht : ∀ x y, t (x + y) = t x + t y)
    (hMR : ∀ z, M (K0 - z) = M z - t z + κ) (z : Site) :
    laplacian M (K0 - z) = laplacian M z := by
  have hsum : incomingNeg z + incomingPos z = z + z := by
    obtain ⟨z1, z2⟩ := z
    unfold incomingNeg incomingPos EvenSite
    split_ifs <;> simp only [Prod.mk.injEq, Prod.mk_add_mk, and_true, true_and] at * <;> omega
  have htsum : t (incomingNeg z) + t (incomingPos z) = 2 * t z := by
    rw [← ht, hsum, ht]
    ring
  unfold laplacian
  rw [← (neighbours_reflect K0 z hK0).2, ← (neighbours_reflect K0 z hK0).1,
    hMR (incomingPos z), hMR (incomingNeg z), hMR z]
  linarith

/-- The sheet C policy of a relation `Q`: the A policy at the reflected points (the pull-back of `sheetQ`). -/
def sheetQC (Q : Site → Site → Prop) (lv centre : Site) : Site → Site → Prop :=
  fun c i => sheetQ Q lv (centre - c) (centre - i)

/-- **The F2F3 policy and its rank** (task 85; the discharge of `hinc`). For the reduced strong residual of the conjugate and `η = ±1`, there is
a quota policy `Q` whose chain potential does not increase along it and which has the rank increments `(−1, 2η)` on the child's generators
(the zero-pitch combination `(a, c) = (1, 2)` of `F2F3_policy`). -/
theorem exists_F2F3_increments {u : Word} (R : StrongResidualReduced u) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    ∃ Q : Site → Site → Prop, RetainQuota (standardField u) Q ∧
      NonincreasingAlong ((frameAt u).chainPotential (standardField u) η) Q ∧
      RankWithIncrements Q (frameAt u).child.modifiedDeck.kernel (frameAt u).child.modifiedDeck.transverse (-1) (2 * η) := by
  obtain ⟨Q, hq, hΦ, hrk⟩ := R.F2F3_policy η hη
  exact ⟨Q, hq, hΦ, hrk 1 2 (by norm_num) (by norm_num)⟩

/-- **hagree at M-white ties** (task 85). For a quota policy `Q` of the conjugate with the chain potential nonincreasing and the rank increments
`(−1, 2·eps)`, and the square data `hsq` for `Q` at every M-white tie, the C policy retains the pointer of the A policy at every M-white tie.
The sheet exchange is discharged from the packet, `hX := sheetExchange_of_packet`. -/
theorem hagree_M_tie (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (Q : Site → Site → Prop) (hq : RetainQuota (standardField (conjWord word)) Q)
    (hch : NonincreasingAlong ((frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (frameAt word).eps) Q)
    (hinc : RankWithIncrements Q (frameAt (conjWord word)).child.modifiedDeck.kernel
      (frameAt (conjWord word)).child.modifiedDeck.transverse (-1) (2 * (frameAt word).eps))
    (hsq : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 →
      ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
        p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
        ¬ sheetQ Q (frameAt word).sheetShift c p0 ∧
        Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
        sheetQ Q (frameAt word).sheetShift p0 p1 ∧
        sheetQ Q (frameAt word).sheetShift p1 p2 ∧
        sheetQ Q (frameAt word).sheetShift p2 c) :
    ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 →
      sheetQC Q (frameAt word).sheetShift (frameAt word).centre c
        (FLatticePaper.W1Pointers.pointerOf (sheetQ Q (frameAt word).sheetShift) c) := by
  intro c hT hM
  -- the sheet exchange, from the packet of the conjugate
  have hX : (frameAt word).SheetExchange (FqW word) := sheetExchange_of_packet h hSE.packet
  obtain ⟨hA, hC⟩ := hX
  set K0 := (frameAt word).centre with hK0def
  have hK0 : (K0.1 + K0.2) % 2 = 0 := (frameAt word).evenSite_centre
  set κ := (frameAt word).symmetryConstant with hκ
  set t : Site → ℤ := (frameAt word).tGrade with htdef
  have ht : ∀ x y, t (x + y) = t x + t y := by
    intro x y
    simp only [htdef, ChildFrame.tGrade, Prod.fst_add, Prod.snd_add]
    ring
  -- the minimum is reflected with the affine shift
  have hMR : ∀ z, MW word (K0 - z) = MW word z - t z + κ := by
    intro z
    show min ((frameAt word).sheetA (FqW word) (K0 - z)) ((frameAt word).sheetC (FqW word) (K0 - z)) =
      min ((frameAt word).sheetA (FqW word) z) ((frameAt word).sheetC (FqW word) z) - t z + κ
    rw [hA z, hC z]
    simp only [min_def]
    split_ifs <;> omega
  have hlapM : ∀ x, laplacian (MW word) (K0 - x) = laplacian (MW word) x :=
    fun x => laplacian_reflect_of (MW word) K0 hK0 t κ ht hMR x
  -- the A arrow of c is M-forced, and its reflection is M-forced at the reflected tie
  obtain ⟨o, ho, hRo, hFo⟩ := a_arrow_forced word h hSE Q hq hch hinc hsq c hT hM
  have hFrefl := forcedEdge_reflect (MW word) K0 hK0 hlapM hFo
  have hT' : (frameAt word).sheetC (FqW word) (K0 - c) = (frameAt word).sheetA (FqW word) (K0 - c) := by
    rw [hC c, hA c, hT]
  have hM' : laplacian (MW word) (K0 - c) = 0 := by
    rw [hlapM c]
    exact hM
  obtain ⟨o', ho', hRo', hFo'⟩ := a_arrow_forced word h hSE Q hq hch hinc hsq (K0 - c) hT' hM'
  -- uniqueness of the M-forced target
  obtain ⟨sel, hsel, hsq'⟩ := FLatticePaper.W1MRank.sheetMin_hasSat_of_strong h hSE
  have hO : K0 - o = o' := forced_input_unique hsel hsq' hFrefl hFo'
  rw [← hO] at hRo'
  -- the C policy retains o at c
  have hCo : sheetQC Q (frameAt word).sheetShift K0 c o := hRo'
  -- the A pointer of c is o (the rejected input is not retained)
  obtain ⟨p0, p1, p2, a, b, hcc, hp0c, hp1c, hp2c, hcov, hne01, hne12, hne02, hp0in, hrej, hE1, hE2, hE3,
    hR0, hR1, hR2⟩ := hsq c hT hM
  have hop0 : o ≠ p0 := fun e => hrej (e ▸ hRo)
  have hpt : FLatticePaper.W1Pointers.pointerOf (sheetQ Q (frameAt word).sheetShift) c = o :=
    pointerOf_eq_of _ c o p0 ho hp0in hRo hrej hop0
  rw [hpt]
  exact hCo

end FLatticePaper.W1MFinal
