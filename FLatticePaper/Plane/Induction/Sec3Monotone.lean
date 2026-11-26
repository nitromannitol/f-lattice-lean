import FLatticePaper.Plane.Induction.Sec3Shift
import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! §3 of the canonical V raw-slip monotonicity note, as a chain of named premises.

For a free V white `w` with prescribed input `u`, the shifted sites `w + X` and `u + X` (note convention) carry
the sheet minimum, so `D₊(w) = F(w) − min(A(w+X), C(w+X))` with `A(w+X) = F_p(w)`. The h0 equality `F(w) = F_p(w)` then gives
`D₊(w) = −min(0, Ψ(w+X))`. The canonical retention of the native edge `zTurn(w+X−lv) → zTurn(u+X−lv)` and `psi_mono` give
`Ψ(w+X) ≤ Ψ(u+X)`, hence `D₊(u) ≤ D₊(w)`. The premises (h0 equalities, shifted stars in E, retention) are stated, not assumed globally. -/

namespace FLatticePaper.Sec3Monotone

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.Sec3Shift FLatticePaper.W1Step

theorem slip_eq_neg_min_sheetPsi {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word)) {w : Site}
    (hw : standardField word w = FqW word w) (hs : w + sec3X word ∈ (frameAt word).closedPolygon) :
    (frameAt word).slip (standardField word) 1 w = -min 0 (sheetPsi word (w + sec3X word)) := by
  unfold ChildFrame.slip
  simp only [one_smul]
  rw [standardField_shortShift_eq_sec3X hW w, standardField_eq_sheetMin_of_strong h hSE hs, hw]
  unfold ChildFrame.sheetMin
  rw [sheetA_sec3X h hSE w]
  unfold sheetPsi
  rw [sheetA_sec3X h hSE w]
  have key : ∀ a c : ℤ, a - min a c = -min 0 (c - a) := by
    intro a c
    omega
  exact key _ _

theorem slip_le_of_retained {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {w u : Site} (hw : standardField word w = FqW word w) (hu : standardField word u = FqW word u)
    (hsw : w + sec3X word ∈ (frameAt word).closedPolygon) (hsu : u + sec3X word ∈ (frameAt word).closedPolygon)
    (hret : P.retained (zTurn (w + sec3X word - (frameAt word).sheetShift))
      (zTurn (u + sec3X word - (frameAt word).sheetShift))) :
    (frameAt word).slip (standardField word) 1 u ≤ (frameAt word).slip (standardField word) 1 w := by
  rw [slip_eq_neg_min_sheetPsi h hW hSE hu hsu, slip_eq_neg_min_sheetPsi h hW hSE hw hsw]
  have hpsi : sheetPsi word (w + sec3X word) ≤ sheetPsi word (u + sec3X word) :=
    W1NonfreeHsq.psi_mono h hSE P hret
  have hmin : min 0 (sheetPsi word (w + sec3X word)) ≤ min 0 (sheetPsi word (u + sec3X word)) :=
    min_le_min le_rfl hpsi
  linarith

end FLatticePaper.Sec3Monotone
