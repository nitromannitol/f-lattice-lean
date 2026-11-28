import FLatticePaper.Tiles.AltSevenBase
import FLatticePaper.Tiles.AltSevenFamily
import FLatticePaper.Tiles.AltSixOverlaps
import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.ConnectedAltL

/-! # Case 3 from the joint family at the base parent words

At `w = v d` with `v = 3^k`, `2^k` or empty, the alternate tile odometer of `v` is its weak one (`TilePart` at a base word), which
`PaperAltBaseCond` fixes: an explicit base alternate tile. With the register data from the family (`AltSevenFamily`) and the
overlaps (`AltSixOverlaps`), the seven pieces built from the family agree (`AltSevenBase`). -/

namespace FLatticePaper.Tiles.AltSevenFamilyB

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathAlt
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (IsBase oddTile evenTile)
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.SiteInduction

private theorem shift_eq (x : ℤ × ℤ) : x - (1, 1) = x + ((-1 : ℤ), (-1 : ℤ)) := by ext <;> simp <;> ring
private theorem shift_eq0 (x : ℤ × ℤ) : x = x + ((0 : ℤ), (0 : ℤ)) := by ext <;> simp
private theorem shift_eq1 (x : ℤ × ℤ) : x + (0, 1) = x + ((0 : ℤ), (1 : ℤ)) := rfl

private theorem base_slice (D : JointData) (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (v : Word) (hb : IsBase v)
    (hlt : v.length < n) : (f v).aOdd = (f v).waOdd ∧ (f v).aEven = (f v).waEven ∧ D.altBase v (f v).waOdd (f v).waEven := by
  have hJ := (hg _ hlt).1
  have hTP := hJ.2.2.1.1 hb
  exact ⟨hTP.2.2.1, hTP.2.2.2, hJ.2.1.2.2.1 hb⟩

/-- The odd alternate tile odometer of `3^k`: the base ladder alternate. -/
theorem baseAOdd_three (D : JointData) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (n : ℕ)
    (hg : GoodBelow D f n) (k : ℕ) (hk : 1 ≤ k) (hlt : (List.replicate k Digit.three).length < n) :
    (∀ x : ℤ × ℤ, x ∈ (f (List.replicate k Digit.three)).aOdd.dom ↔
        x + ((-1 : ℤ), (-1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2)) ∧
      ∀ x ∈ (f (List.replicate k Digit.three)).aOdd.dom, (f (List.replicate k Digit.three)).aOdd.val x =
        paperLadderAltValue (2 * (k : ℤ) + 2) (x + ((-1 : ℤ), (-1 : ℤ))) := by
  obtain ⟨e1, -, hW⟩ := base_slice D f n hg _ (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd)) hlt
  rw [hA] at hW
  obtain ⟨hd, hv, -, -⟩ := hW.2.1 k hk rfl
  rw [e1]
  exact ⟨fun x => by rw [hd, shift_eq], fun x hx => by rw [hv x hx, shift_eq]⟩

/-- The odd alternate tile odometer of `2^k`, `k ≥ 0`: the base near-stair alternate. -/
theorem baseAOdd_two (D : JointData) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (n : ℕ)
    (hg : GoodBelow D f n) (k : ℕ) (hlt : (List.replicate k Digit.two).length < n) :
    (∀ x : ℤ × ℤ, x ∈ (f (List.replicate k Digit.two)).aOdd.dom ↔
        x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3)) ∧
      ∀ x ∈ (f (List.replicate k Digit.two)).aOdd.dom, (f (List.replicate k Digit.two)).aOdd.val x =
        paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨e1, -, hW⟩ := base_slice D f n hg [] (Or.inl rfl) hlt
    rw [hA] at hW
    obtain ⟨hd, hv, -, -⟩ := hW.1 rfl
    simp only [List.replicate_zero, Nat.cast_zero, mul_zero, zero_add]
    rw [e1]
    exact ⟨fun x => by rw [hd], fun x hx => by rw [hv x hx]⟩
  · obtain ⟨e1, -, hW⟩ := base_slice D f n hg _ (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)) hlt
    rw [hA] at hW
    obtain ⟨hd, hv, -, -⟩ := hW.2.2 k hk rfl
    rw [e1]
    exact ⟨fun x => by rw [hd], fun x hx => by rw [hv x hx]⟩

/-- The even alternate tile odometer of `3^k`, `k ≥ 0`: the base stair alternate. -/
theorem baseAEven_three (D : JointData) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (n : ℕ)
    (hg : GoodBelow D f n) (k : ℕ) (hlt : (List.replicate k Digit.three).length < n) :
    (∀ x : ℤ × ℤ, x ∈ (f (List.replicate k Digit.three)).aEven.dom ↔
        x + ((0 : ℤ), (0 : ℤ)) ∈ paperStairAltTile (2 * (k : ℤ) + 3)) ∧
      ∀ x ∈ (f (List.replicate k Digit.three)).aEven.dom, (f (List.replicate k Digit.three)).aEven.val x =
        paperStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (0 : ℤ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨-, e2, hW⟩ := base_slice D f n hg [] (Or.inl rfl) hlt
    rw [hA] at hW
    obtain ⟨-, -, hd, hv⟩ := hW.1 rfl
    simp only [List.replicate_zero, Nat.cast_zero, mul_zero, zero_add]
    rw [e2]
    exact ⟨fun x => by rw [hd, ← shift_eq0], fun x hx => by rw [hv x hx, ← shift_eq0]⟩
  · obtain ⟨-, e2, hW⟩ := base_slice D f n hg _ (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd)) hlt
    rw [hA] at hW
    obtain ⟨-, -, hd, hv⟩ := hW.2.1 k hk rfl
    rw [e2]
    exact ⟨fun x => by rw [hd, ← shift_eq0], fun x hx => by rw [hv x hx, ← shift_eq0]⟩

/-- The even alternate tile odometer of `2^k`: the base near-ladder alternate. -/
theorem baseAEven_two (D : JointData) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (n : ℕ)
    (hg : GoodBelow D f n) (k : ℕ) (hk : 1 ≤ k) (hlt : (List.replicate k Digit.two).length < n) :
    (∀ x : ℤ × ℤ, x ∈ (f (List.replicate k Digit.two)).aEven.dom ↔
        x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2)) ∧
      ∀ x ∈ (f (List.replicate k Digit.two)).aEven.dom, (f (List.replicate k Digit.two)).aEven.val x =
        paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ))) := by
  obtain ⟨-, e2, hW⟩ := base_slice D f n hg _ (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd)) hlt
  rw [hA] at hW
  obtain ⟨-, -, hd, hv⟩ := hW.2.2 k hk rfl
  rw [e2]
  exact ⟨fun x => by rw [hd], fun x hx => by rw [hv x hx]⟩

/-- Case 3 from the family at the base parent word `three^k`, even alternate child, last digit `one`. -/
theorem familyB_ae31 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 1 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.three) ++ [Digit.one]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lEven) ((List.replicate k Digit.three) ++ [Digit.one])) 6 j)
    (hk : ∀ u2, (regsAt ((List.replicate k Digit.three) ++ [Digit.one])).2 = some u2 → ∃ c : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ ((List.replicate k Digit.three) ++ [Digit.one]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ ((List.replicate k Digit.three) ++ [Digit.one])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.three) ++ [Digit.one])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lEven) ((List.replicate k Digit.three) ++ [Digit.one])) κ := by
  have hlt : (List.replicate k Digit.three).length < ((List.replicate k Digit.three) ++ [Digit.one]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.three) ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.one (by simp); simp at this
    · have := h Digit.one (by simp); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.three) ++ [Digit.one]) hwb
  have hr : regsAt ((List.replicate k Digit.three) ++ [Digit.one]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u1 = (List.replicate k Digit.three) := by
    have := ConnectedAltL.regs_pre_fst (List.replicate k Digit.three) Digit.one (by decide)
    rw [hu1] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.three) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.three) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.three) ++ [Digit.one]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.three) ++ [Digit.one]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.one])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.one])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAOdd_three D hA f _ hg k hkk (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.three) ++ [Digit.one]) = 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_three k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).2
  obtain ⟨kk, hkk'⟩ := hk u2 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ae31 D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lEven) k hkk ((List.replicate k Digit.three) ++ [Digit.one]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf; simp)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb1]; exact hdH) (by simp only [hb1]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_even D.S _ _ _ _ _ ((List.replicate k Digit.three) ++ [Digit.one]) u1 u2 (0, 1, 1, 0) (texV2 (parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd + texV1Even (parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).even) ((parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd.num, -(parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altP1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2])
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_even_all ((List.replicate k Digit.three) ++ [Digit.one]) hwb (by simp) u1 u2 hr)⟩

/-- Case 3 from the family at the base parent word `three^k`, even alternate child, last digit `two`. -/
theorem familyB_ae32 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 1 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.three) ++ [Digit.two]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).lEven) ((List.replicate k Digit.three) ++ [Digit.two])) 6 j)
    (hk : ∀ u2, (regsAt ((List.replicate k Digit.three) ++ [Digit.two])).2 = some u2 → ∃ c : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ ((List.replicate k Digit.three) ++ [Digit.two]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ ((List.replicate k Digit.three) ++ [Digit.two])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.three) ++ [Digit.two])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).lEven) ((List.replicate k Digit.three) ++ [Digit.two])) κ := by
  have hlt : (List.replicate k Digit.three).length < ((List.replicate k Digit.three) ++ [Digit.two]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.three) ++ [Digit.two]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.two (by simp); simp at this
    · have := h Digit.three (by simp [List.mem_replicate]; omega); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.three) ++ [Digit.two]) hwb
  have hr : regsAt ((List.replicate k Digit.three) ++ [Digit.two]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u1 = (List.replicate k Digit.three) := by
    have := ConnectedAltL.regs_pre_fst (List.replicate k Digit.three) Digit.two (by decide)
    rw [hu1] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.three) ++ [Digit.two]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.three) ++ [Digit.two]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.three) ++ [Digit.two]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.three) ++ [Digit.two]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.two])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.two])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAOdd_three D hA f _ hg k hkk (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.three) ++ [Digit.two]) ≠ 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_three k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).2
  obtain ⟨kk, hkk'⟩ := hk u2 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ae32 D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).aEven) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.two]) u).lEven) k hkk ((List.replicate k Digit.three) ++ [Digit.two]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb1]; exact hdH) (by simp only [hb1]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_even D.S _ _ _ _ _ ((List.replicate k Digit.three) ++ [Digit.two]) u1 u2 (0, 0, 0, 1) (texV2 (parentsAt ((List.replicate k Digit.three) ++ [Digit.two])).even) ((parentsAt ((List.replicate k Digit.three) ++ [Digit.two])).even.num, -(parentsAt ((List.replicate k Digit.three) ++ [Digit.two])).even.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altP1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2])
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_even_all ((List.replicate k Digit.three) ++ [Digit.two]) hwb (by simp) u1 u2 hr)⟩

/-- Case 3 from the family at the base parent word `two^k`, even alternate child, last digit `one`. -/
theorem familyB_ae21 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 0 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.two) ++ [Digit.one]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lEven) ((List.replicate k Digit.two) ++ [Digit.one])) 6 j)
    (hk : ∀ u2, (regsAt ((List.replicate k Digit.two) ++ [Digit.one])).2 = some u2 → ∃ c : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ ((List.replicate k Digit.two) ++ [Digit.one]) ∈ tEvenSet u2 →
      (f u2).tEven.val (x + shiftQ ((List.replicate k Digit.two) ++ [Digit.one])) - (f u2).tEven.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.two) ++ [Digit.one])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltEvenPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lEven) ((List.replicate k Digit.two) ++ [Digit.one])) κ := by
  have hlt : (List.replicate k Digit.two).length < ((List.replicate k Digit.two) ++ [Digit.one]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.two) ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.one (by simp); simp at this
    · have := h Digit.one (by simp); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.two) ++ [Digit.one]) hwb
  have hr : regsAt ((List.replicate k Digit.two) ++ [Digit.one]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u1 = (List.replicate k Digit.two) := by
    have := ConnectedAltL.regs_pre_fst (List.replicate k Digit.two) Digit.one (by decide)
    rw [hu1] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.two) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.two) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.two) ++ [Digit.one]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.two) ++ [Digit.one]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.one])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.one])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAOdd_two D hA f _ hg k (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.two) ++ [Digit.one]) = 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_two k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).2
  obtain ⟨kk, hkk'⟩ := hk u2 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ae21 D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lEven) k hkk ((List.replicate k Digit.two) ++ [Digit.one]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf; simp)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb2]; exact hhQ) (by simp only [hb2]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb1]; exact hdH) (by simp only [hb1]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_even D.S _ _ _ _ _ ((List.replicate k Digit.two) ++ [Digit.one]) u1 u2 (0, 1, 1, 0) (texV2 (parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd + texV1Even (parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).even) ((parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd.num, -(parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altP1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2])
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_even_all ((List.replicate k Digit.two) ++ [Digit.one]) hwb (by simp) u1 u2 hr)⟩

/-- Case 3 from the family at the base parent word `three^k`, odd alternate child, last digit `one`. -/
theorem familyB_ao31 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 0 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.three) ++ [Digit.one]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lOdd) ((List.replicate k Digit.three) ++ [Digit.one])) 6 j)
    (hk : ∀ u1, (regsAt ((List.replicate k Digit.three) ++ [Digit.one])).1 = some u1 → ∃ c : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP ((List.replicate k Digit.three) ++ [Digit.one]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP ((List.replicate k Digit.three) ++ [Digit.one])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.three) ++ [Digit.one])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lOdd) ((List.replicate k Digit.three) ++ [Digit.one])) κ := by
  have hlt : (List.replicate k Digit.three).length < ((List.replicate k Digit.three) ++ [Digit.one]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.three) ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.one (by simp); simp at this
    · have := h Digit.one (by simp); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.three) ++ [Digit.one]) hwb
  have hr : regsAt ((List.replicate k Digit.three) ++ [Digit.one]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u2 = (List.replicate k Digit.three) := by
    have := ConnectedAltL.regs_pre_snd (List.replicate k Digit.three) Digit.one (by decide)
    rw [hu2] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.three) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.three) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.three) ++ [Digit.one]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.three) ++ [Digit.one]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.one])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.three) ++ [Digit.one])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAEven_three D hA f _ hg k (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.three) ++ [Digit.one]) = 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_three k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).1
  obtain ⟨kk, hkk'⟩ := hk u1 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ao31 D.S (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).aEven) (fun u => (below f ((List.replicate k Digit.three) ++ [Digit.one]) u).lOdd) k hkk ((List.replicate k Digit.three) ++ [Digit.one]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf; simp)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb2]; exact hdH) (by simp only [hb2]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_odd D.S _ _ _ _ _ ((List.replicate k Digit.three) ++ [Digit.one]) u1 u2 (1, 1, -1, 0) (texV1Odd (parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd + texV2 (parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd - texV1Even (parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).even) ((parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd.num, -(parentsAt ((List.replicate k Digit.three) ++ [Digit.one])).odd.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altQ1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring)
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_odd_all ((List.replicate k Digit.three) ++ [Digit.one]) hwb (by simp) u1 u2 hr)⟩

/-- Case 3 from the family at the base parent word `two^k`, odd alternate child, last digit `one`. -/
theorem familyB_ao21 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 1 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.two) ++ [Digit.one]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lOdd) ((List.replicate k Digit.two) ++ [Digit.one])) 6 j)
    (hk : ∀ u1, (regsAt ((List.replicate k Digit.two) ++ [Digit.one])).1 = some u1 → ∃ c : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP ((List.replicate k Digit.two) ++ [Digit.one]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP ((List.replicate k Digit.two) ++ [Digit.one])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.two) ++ [Digit.one])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lOdd) ((List.replicate k Digit.two) ++ [Digit.one])) κ := by
  have hlt : (List.replicate k Digit.two).length < ((List.replicate k Digit.two) ++ [Digit.one]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.two) ++ [Digit.one]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.one (by simp); simp at this
    · have := h Digit.one (by simp); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.two) ++ [Digit.one]) hwb
  have hr : regsAt ((List.replicate k Digit.two) ++ [Digit.one]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u2 = (List.replicate k Digit.two) := by
    have := ConnectedAltL.regs_pre_snd (List.replicate k Digit.two) Digit.one (by decide)
    rw [hu2] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.two) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.two) ++ [Digit.one]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.two) ++ [Digit.one]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.two) ++ [Digit.one]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.one])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.one])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAEven_two D hA f _ hg k hkk (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.two) ++ [Digit.one]) = 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_two k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).1
  obtain ⟨kk, hkk'⟩ := hk u1 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ao21 D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).aEven) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.one]) u).lOdd) k hkk ((List.replicate k Digit.two) ++ [Digit.one]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf; simp)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb2]; exact hdH) (by simp only [hb2]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_odd D.S _ _ _ _ _ ((List.replicate k Digit.two) ++ [Digit.one]) u1 u2 (1, 1, -1, 0) (texV1Odd (parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd + texV2 (parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd - texV1Even (parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).even) ((parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd.num, -(parentsAt ((List.replicate k Digit.two) ++ [Digit.one])).odd.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altQ1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2] <;> ring)
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_odd_all ((List.replicate k Digit.two) ++ [Digit.one]) hwb (by simp) u1 u2 hr)⟩

/-- Case 3 from the family at the base parent word `two^k`, odd alternate child, last digit `three`. -/
theorem familyB_ao23 (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hkk : 1 ≤ k) (hg : GoodBelow D f ((List.replicate k Digit.two) ++ [Digit.three]).length)
    (hpc : ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).lOdd) ((List.replicate k Digit.two) ++ [Digit.three])) 6 j)
    (hk : ∀ u1, (regsAt ((List.replicate k Digit.two) ++ [Digit.three])).1 = some u1 → ∃ c : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP ((List.replicate k Digit.two) ++ [Digit.three]) ∈ tOddSet u1 →
      (f u1).tOdd.val (x + shiftP ((List.replicate k Digit.two) ++ [Digit.three])) - (f u1).tOdd.val x - ClosedPathSum.dot2 (affS ((List.replicate k Digit.two) ++ [Digit.three])) x = c) :
    ∃ κ : ℕ → ℤ, JointGlue.PiecesAgree (tileAltOddPieces D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aEven)
      (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).lOdd) ((List.replicate k Digit.two) ++ [Digit.three])) κ := by
  have hlt : (List.replicate k Digit.two).length < ((List.replicate k Digit.two) ++ [Digit.three]).length := by simp
  have hwb : ¬ IsBase ((List.replicate k Digit.two) ++ [Digit.three]) := by
    rintro (h | h | h)
    · simp at h
    · have := h Digit.two (by simp [List.mem_replicate]; omega); simp at this
    · have := h Digit.three (by simp); simp at this
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := JointRot.regs_some ((List.replicate k Digit.two) ++ [Digit.three]) hwb
  have hr : regsAt ((List.replicate k Digit.two) ++ [Digit.three]) = (some u1, some u2) := Prod.ext hu1 hu2
  have hv : u2 = (List.replicate k Digit.two) := by
    have := ConnectedAltL.regs_pre_snd (List.replicate k Digit.two) Digit.three (by decide)
    rw [hu2] at this; cases this; rfl
  have l1 : u1.length < ((List.replicate k Digit.two) ++ [Digit.three]).length := JointInduction.regsAt_lt _ u1 (Or.inl hu1)
  have l2 : u2.length < ((List.replicate k Digit.two) ++ [Digit.three]).length := JointInduction.regsAt_lt _ u2 (Or.inr hu2)
  have hb1 : below f ((List.replicate k Digit.two) ++ [Digit.three]) u1 = f u1 := JointRot.below_of_lt f _ _ l1
  have hb2 : below f ((List.replicate k Digit.two) ++ [Digit.three]) u2 = f u2 := JointRot.below_of_lt f _ _ l2
  have hp := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.three])).1 u1 (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents ((List.replicate k Digit.two) ++ [Digit.three])).2 u2 (by rw [hr])
  obtain ⟨βP, hdP, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  rw [← hp] at hcP hhP
  rw [← hq] at hcQ hhQ
  rw [hdP] at hhP
  rw [hdQ] at hhQ
  obtain ⟨hdH, hvH⟩ := baseAEven_two D hA f _ hg k hkk (by simp)
  rw [← hv] at hdH hvH
  have hph : phase ((List.replicate k Digit.two) ++ [Digit.three]) ≠ 1 := by
    simp [phase, List.count_append, List.count_replicate]
  have hrel : _ := parentsAt_replicate_two k
  have hcompat := (MixedCompatGeneral.alt_mixed D hS hA f _ u1 u2 hg hwb hr 0).1
  obtain ⟨kk, hkk'⟩ := hk u1 (by rw [hr])
  refine ⟨_, AltSevenBase.seven_base_ao23 D.S (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).tEven)
    (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aOdd) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).aEven) (fun u => (below f ((List.replicate k Digit.two) ++ [Digit.three]) u).lOdd) k hkk ((List.replicate k Digit.two) ++ [Digit.three]) u1 u2 hph (by simp) hr hp hq
    (by simp [parentsAt_append_singleton, hrel, Parents.step, Parents.current, Parents.combine]; ring_nf)
    βP βQ (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) (by simp only [hb1]; exact hcP) (by simp only [hb2]; exact hcQ)
    (by simp only [hb1]; exact hhP) (by simp only [hb1]; exact ⟨kk, hkk'⟩) (by simp only [hb1, hb2]; exact hcompat)
    (by simp only [hb2]; exact hdH) (by simp only [hb2]; exact hvH)
    (fun j hj => AltSevenFamily.hpc_odd D.S _ _ _ _ _ ((List.replicate k Digit.two) ++ [Digit.three]) u1 u2 (0, 1, 1, 0) (texV2 (parentsAt ((List.replicate k Digit.two) ++ [Digit.three])).odd + texV1Even (parentsAt ((List.replicate k Digit.two) ++ [Digit.three])).even) ((parentsAt ((List.replicate k Digit.two) ++ [Digit.three])).odd.num, -(parentsAt ((List.replicate k Digit.two) ++ [Digit.three])).odd.den) hr (by simp)
      (by simp [SurgicalAlt.altTypeOf, JointFamily.W1Odd, hph, SurgicalAlt.altQ1Coeff])
      (by ext <;> simp [altOff, SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2])
      (by ext <;> simp [altAff, SurgicalAlt.coeffAffine])
      (by simp only [hb1]; exact hdP) (by simp only [hb2]; exact hdQ) j hj (hpc j hj))
    (AltSixOverlaps.sixOverlaps_odd_all ((List.replicate k Digit.two) ++ [Digit.three]) hwb (by simp) u1 u2 hr)⟩

end FLatticePaper.Tiles.AltSevenFamilyB
