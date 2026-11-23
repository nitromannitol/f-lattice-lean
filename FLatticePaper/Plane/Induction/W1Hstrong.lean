import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.Packet

/-! Task 54 (2): the strengthened odd parent strip `hStrong` (W1_CONSTRUCTOR §1: odd `s_p ∈ [2 − 3D + N, 3D + N − 2]`), derived
from the conjugate's zero strips. The parent field is `Fp = G∘Z + h0` (quarterTurnField), so `Fp(Q) = h0(Q)` iff `G(ZQ) = 0`.
With `z = ZQ` (even for odd `Q`) and the conjugate child `(D−N, D+N)`, `t_c(z) = −s_p(Q) + (D+N)`: the ordinary zero strip of
the conjugate (`t_c ∈ [1 − (D+N), 4D − 2]`) covers `s_p ≤ 2(D+N) − 1`, and the conjugate's extended even zero line
(`even_zero_lower_of_strong`, `t_c ∈ [2 − 2D, 1 − (D+N)]`, the seed `SeedFields(conjWord w).even_zero`) covers the rest. -/

namespace FLatticePaper.W1Hstrong

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1Seeds

theorem hStrong_of_strong {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord w)) (hpar : SeedFields (conjWord w)) :
    ∀ Q : Site, ¬ EvenSite Q →
      2 - 3 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num ≤ (frameAt w).parentSGrade Q →
      (frameAt w).parentSGrade Q ≤ 3 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num - 2 →
      quarterTurnField (standardField (conjWord w)) Q = harmonicGrid Q := by
  intro Q hQ hlo hhi
  have hconj : (frameAt (conjWord w)).child = (frameAt w).parents.odd.rotate := frameAt_conj_child hproper
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hconj
  have hzE : EvenSite (-Q.2, Q.1 - 1) := by
    unfold EvenSite at hQ ⊢
    show (-Q.2 + (Q.1 - 1)) % 2 = 0
    omega
  have htc : (frameAt (conjWord w)).tGrade (-Q.2, Q.1 - 1) =
      -(frameAt w).parentSGrade Q + ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) := by
    unfold ChildFrame.tGrade ChildFrame.parentSGrade
    dsimp only
    rw [hcn, hcd]
    ring
  have hG0 : standardField (conjWord w) (-Q.2, Q.1 - 1) = 0 := by
    have hLc : (frameAt (conjWord w)).child.den + (frameAt (conjWord w)).child.num =
        2 * ((frameAt w).parents.odd.den) := by
      rw [hcn, hcd]
      ring
    have hDN : (frameAt (conjWord w)).child.den = (frameAt w).parents.odd.den + (frameAt w).parents.odd.num := hcd
    have hDN' : (frameAt (conjWord w)).child.num = (frameAt w).parents.odd.den - (frameAt w).parents.odd.num := hcn
    rcases le_or_gt (1 - (frameAt (conjWord w)).child.den)
        ((frameAt (conjWord w)).tGrade (-Q.2, Q.1 - 1)) with h1 | h1
    · rcases le_or_gt ((frameAt (conjWord w)).tGrade (-Q.2, Q.1 - 1))
        ((frameAt (conjWord w)).child.num + 2 * (frameAt (conjWord w)).child.den - 1) with h2 | h2
      · exact hS.packet.strips.1 _ h1 h2
      · have hr := standardField_iRefl hS (-Q.2, Q.1 - 1)
        have hiz : EvenSite (iRefl (-Q.2, Q.1 - 1)) := (evenSite_iRefl _).2 hzE
        have ht2 := tGrade_iRefl (frameAt (conjWord w)) (-Q.2, Q.1 - 1)
        rw [← hr]
        apply even_zero_lower_of_strong hS hpar.even_zero _ hiz
        · rw [ht2]
          rw [htc] at h2 ⊢
          linarith
        · rw [ht2]
          rw [htc] at h2 ⊢
          linarith
    · apply even_zero_lower_of_strong hS hpar.even_zero _ hzE
      · rw [htc] at h1 ⊢
        rw [hLc]
        linarith
      · rw [htc] at h1 ⊢
        rw [hDN] at h1
        linarith
  unfold quarterTurnField
  rw [quarterTurn_site, hG0, zero_add]

end FLatticePaper.W1Hstrong
