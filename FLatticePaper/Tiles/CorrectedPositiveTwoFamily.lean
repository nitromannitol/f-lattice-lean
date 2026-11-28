import FLatticePaper.Tiles.MixedRegisterTwoDirect
import FLatticePaper.Tiles.CorrectedRegisterTwoDirect
import FLatticePaper.Tiles.CorrectedDoubleOneFamily
import FLatticePaper.Tiles.CorrectedSwappedDomains

/-! The six-copy odd alternate and the corrected child domains after arbitrary positive-determinant words. -/

namespace FLatticePaper.Tiles.CorrectedPositiveTwoFamily

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily LCorrecProps CorrectedEvenPlacement CorrectedPlacementFrames CorrectedChildColumns
open CorrectedWordCoverage CorrectedAlternatePolygons

private theorem positive_nonbase (w : Word) (d : (parentsAt w).odd.det (parentsAt w).even=1) : ¬IsBase w := by
  rintro (rfl|three|two)
  · exact (by decide : (-1:ℤ)≠1) d
  · have eq : w=List.replicate w.length .three := List.eq_replicate_iff.mpr ⟨rfl,three⟩
    have P := BaseTileProps.parents_three w.length
    rw [←eq] at P; simp [P,Fraction.det] at d
  · have eq : w=List.replicate w.length .two := List.eq_replicate_iff.mpr ⟨rfl,two⟩
    have P := BaseTileProps.parents_two w.length
    rw [←eq] at P; simp [P,Fraction.det] at d

theorem sign_two (w : Word) :
    (parentsAt (w++[.two])).odd.det (parentsAt (w++[.two])).even=(parentsAt w).odd.det (parentsAt w).even := by
  rw [parentsAt_append_singleton,SiteScope.det_step_two]

/-- At every two exit of positive preceding determinant the six standard copies give the actual odd alternate. -/
theorem alternate (w : Word) (sign : (parentsAt w).odd.det (parentsAt w).even=1) : MixedAt (w++[.two]) false := by
  have hw := positive_nonbase w sign
  have ht : ¬IsBase (w++[exit false]) := positive_nonbase _ ((sign_two w).trans sign)
  apply CorrectedMixedSources.mixed_at w false false ht (by intro bad; cases bad)
  intro z
  cases w with
  | nil => exact False.elim (hw (Or.inl rfl))
  | cons x xs =>
    apply (CorrectedMixedPlacement.physical x xs hw false false z).mp
    rw [sign]
    exact MixedRegisterTwoDirect.word x xs hw false z sign

private theorem comparison (v t : Word) (one long : Bool) (pre : stemPrefix v=t++[exit one])
    (sign : (parentsAt t).odd.det (parentsAt t).even=1) (z : Site) :
    let prev := -(parentsAt t).odd.det (parentsAt t).even
    Covers (fun i => (CorrectedPlacedDiagram.diagram (periods v) (length v) one prev long i).mem z) long 8 := by
  have ht := positive_nonbase t sign
  cases t with
  | nil => exact False.elim (ht (Or.inl rfl))
  | cons x xs =>
    apply CorrectedPhysicalCoverage.physical x xs v ht one long pre z
    rw [sign]; cases one
    · exact CorrectedRegisterTwoDirect.word x xs ht long _ (Nat.succ_pos _) z sign
    · exact CorrectedRegisterOneDirect.word x xs ht long _ (Nat.succ_pos _) z sign

/-- Either next exit of the six-copy odd alternate supplies the entire ordinary corrected child. -/
theorem ordinary (v w : Word) (one : Bool) (pre : stemPrefix v=(w++[.two])++[exit one])
    (sign : (parentsAt w).odd.det (parentsAt w).even=1) : evenChild evenLCells v false=oddTile (v++[.three]) := by
  have d := (sign_two w).trans sign
  have H := CorrectedAlternatePolygons.head v (w++[.two]) one pre (alternate w sign)
  exact CorrectedPhysicalCoverage.ordinary v _ one pre (positive_nonbase _ d) H (comparison v _ one false pre d)

private theorem sign_threes (w : Word) (k : ℕ) : (parentsAt (w++List.replicate k .three)).odd.det
    (parentsAt (w++List.replicate k .three)).even=(parentsAt w).odd.det (parentsAt w).even := by
  induction k with
  | zero => simp
  | succ k h => rw [List.replicate_succ',←List.append_assoc,parentsAt_append_singleton,SiteScope.det_step_three,h]

/-- Both native three-ending domains after two successive two exits and any positive run of threes. -/
theorem domains (w : Word) (k : ℕ) (sign : (parentsAt w).odd.det (parentsAt w).even=1) :
    let v := ((w++[.two])++[.two])++List.replicate k .three
    evenChild evenLCells v false=oddTile (v++[.three]) ∧ evenChild evenLCells v true=altEvenT (v++[.three]) := by
  intro v
  let t := w++[Digit.two]
  have d : (parentsAt t).odd.det (parentsAt t).even=1 := (sign_two _).trans sign
  have pre : stemPrefix v=t++[exit false] := by
    change stripTrailing .three ((t++[Digit.two])++List.replicate k .three)=t++[.two]
    induction k with
    | zero => rw [List.replicate_zero,List.append_nil,JointRot.stripTrailing_snoc]; rfl
    | succ k ih => rw [List.replicate_succ',←List.append_assoc,JointRot.stripTrailing_snoc,if_pos rfl,ih]
  have ds : (parentsAt v).odd.det (parentsAt v).even=1 := (sign_threes _ k).trans ((sign_two t).trans d)
  have sw : (parentsAt (swapW v)).odd.det (parentsAt (swapW v)).even=1 := by
    rw [SiteScope.det_parentsAt] at ds ⊢
    exact (congrArg (fun a : ℕ => 2*(a:ℤ)-1) (phase_rotate_word v)).trans ds
  have T := CorrectedAlternateRotation.after_three v true (alternate (swapW v) sw)
  have H := CorrectedAlternatePolygons.head v t false pre (alternate w sign)
  exact ⟨ordinary v w false pre sign,CorrectedPhysicalCoverage.elongated v t false pre (positive_nonbase _ d)
    H T (comparison v t false true pre d)⟩

end FLatticePaper.Tiles.CorrectedPositiveTwoFamily
