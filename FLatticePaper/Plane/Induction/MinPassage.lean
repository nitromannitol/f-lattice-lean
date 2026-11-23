import FLatticePaper.Plane.Induction.PassagePR
import FLatticePaper.Plane.Induction.KMinBridge

/-! # Task 103 (the passage): the white (forced) step of the minimum of `K₊`, `K₋`, with the acyclic price input

At a white point `z` of a fort `S` of `F = standardField word`, which is a minimum of `K_η` over `S`, the forced input `o` of an unseeded
forced white (the unit proof of `ForcedEdge`) is an input of `z`, lies in `S` (both inputs of a white point of a fort are in the fort), and
`K_η o = K_η z`: `P` and the rounded slip do not increase along forced white edges (`price_nonincrease_forced_of_sat_PR` and its `J` versions,
from the satisfiability input `HasSatSelection` and the transfer `(T)`), so the minimum passes to the forced input. The price range enters only
as `PriceRangeOn word` (from `priceRange_of_conjugate`). The black step is `minK_black_input_plus_PR` (`price_nonincrease_black_PR`). -/

namespace FLatticePaper.MinPassage

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.KMinBridge FLatticePaper.PassagePR

/-- The forced input of an unseeded forced point is an input of it (the seed case is empty). -/
theorem forced_input_of_unseeded {F : Field} {c o : Site} (hf : ForcedEdge F (fun _ _ => False) c o) :
    o = FLatticePaper.incomingNeg c ∨ o = FLatticePaper.incomingPos c := by
  cases hf with
  | seed hs => exact hs.elim
  | @unit a b c' o' inside hc hw ho hout hin hforced => exact ho

/-- **The white forced step of `K₊`**: the forced input of a white minimum of `K₊` over a fort lies in the fort and has the same `K₊`. -/
theorem minK_white_forced_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {S : Set Site} (hfort : IsIncomingFort (standardField word) S) {z o : Site} (hzS : z ∈ S)
    (hzE : z ∈ (frameAt word).closedPolygon) (hw : laplacian (standardField word) z = 0)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) z o) (hoE : o ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kPlusW word z ≤ kPlusW word w) :
    o ∈ S ∧ kPlusW word o = kPlusW word z := by
  have hio := forced_input_of_unseeded hf
  have hoS : o ∈ S := by
    rcases hfort z hzS with ⟨hl, _⟩ | ⟨_, hn, hp⟩
    · exfalso
      omega
    · rcases hio with rfl | rfl
      · exact hn
      · exact hp
  have hpr := price_nonincrease_forced_of_sat_PR h hSE hPR hW hT hw hzE hf hoE
  have hjr := jplus_nonincrease_forced_of_sat_PR h hSE hPR hW hT hw hzE hf hoE
  have hmi := hmin o hoS
  refine ⟨hoS, ?_⟩
  unfold kPlusW jPlusW at hmi ⊢
  omega

/-- **The white forced step of `K₋`**: the same for `K₋` and `J₋`. -/
theorem minK_white_forced_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {S : Set Site} (hfort : IsIncomingFort (standardField word) S) {z o : Site} (hzS : z ∈ S)
    (hzE : z ∈ (frameAt word).closedPolygon) (hw : laplacian (standardField word) z = 0)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) z o) (hoE : o ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kMinusW word z ≤ kMinusW word w) :
    o ∈ S ∧ kMinusW word o = kMinusW word z := by
  have hio := forced_input_of_unseeded hf
  have hoS : o ∈ S := by
    rcases hfort z hzS with ⟨hl, _⟩ | ⟨_, hn, hp⟩
    · exfalso
      omega
    · rcases hio with rfl | rfl
      · exact hn
      · exact hp
  have hpr := price_nonincrease_forced_of_sat_PR h hSE hPR hW hT hw hzE hf hoE
  have hjr := jminus_nonincrease_forced_of_sat_PR h hSE hPR hW hT hw hzE hf hoE
  have hmi := hmin o hoS
  refine ⟨hoS, ?_⟩
  unfold kMinusW jMinusW at hmi ⊢
  omega

end FLatticePaper.MinPassage
