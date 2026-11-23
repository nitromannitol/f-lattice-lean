import FLatticePaper.Plane.Induction.SheetMinFromConj
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.ComparisonEmpty
import FLatticePaper.Plane.ThresholdMinimum
import FLatticePaper.Rank

/-! # Task 80: a global burning rank of the sheet minimum M, from the two constrained ranks (lead, task 79 option (i))

`sheetMin_burningRank_of_chain` is the proof of `sheetMin_binary_recurrent_of_chain` with its final step replaced: the burning rank of
`M = thresholdMin A C 0` is `leftThresholdRank` (gap, then the winning sheet's rank), from `isBurningRank_leftThreshold`. A global
`IsBurningRank` is a strict AND-OR rank: black sites have both inputs strictly lower, white sites one. Then `hasSat_of_burning` gives the
satisfying selection of M, with no fort argument. `sheetMin_hasSat_of_strong` supplies the ranks from the conjugate's strong estimates
(as in `sheetMin_recurrent_of_strong`). -/

namespace FLatticePaper.W1MRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- **The square clauses of a strict AND-OR rank over a linear order** (the rank form of `squareClauses_of_strict`). The minimal corner of
a unit square is white (a black minimal corner has an input of smaller rank in the square), and its selected input has smaller rank, so
it leaves the square. -/
theorem squareClauses_of_burning {F : Field} {β : Type*} [LinearOrder β] {R : Site → β} {sel : Site → Site}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i < R c)
    (hsel : ∀ c, laplacian F c = 0 → (sel c = incomingNeg c ∨ sel c = incomingPos c) ∧ R (sel c) < R c)
    (a b : ℤ) : SquareClauseSat F sel a b := by
  intro hall
  obtain ⟨c, hcS, hmin⟩ := (squareCorners a b).exists_min_image R ⟨(a, b), by simp [squareCorners]⟩
  have hk := hall c hcS
  unfold keptInside at hk
  rcases hbin c with hb | hw
  · rw [if_pos hb] at hk
    rcases hk with hn | hp
    · have h1 := hblack c hb (incomingNeg c) (Or.inl rfl)
      have h2 := hmin _ hn
      exact absurd h2 (not_le.mpr h1)
    · have h1 := hblack c hb (incomingPos c) (Or.inr rfl)
      have h2 := hmin _ hp
      exact absurd h2 (not_le.mpr h1)
  · rw [if_neg (by rw [hw]; norm_num)] at hk
    have h1 := (hsel c hw).2
    have h2 := hmin _ hk
    exact absurd h2 (not_le.mpr h1)

/-- **A global strict AND-OR rank gives the satisfying selection** (task 80): from `IsBurningRank`, choose at each white an input of
smaller rank; the square clauses hold by `squareClauses_of_burning`. -/
theorem hasSat_of_burning {F : Field} {β : Type*} [LinearOrder β] (R : Site → β) (h : IsBurningRank F R) :
    HasSatSelection F := by
  have hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0 := by
    intro c
    rcases h c with ⟨hl, -, -⟩ | ⟨hl, -⟩
    · exact Or.inl hl
    · exact Or.inr hl
  have hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i < R c := by
    intro c hc i hi
    rcases h c with ⟨-, hn, hp⟩ | ⟨hl, -⟩
    · rcases hi with rfl | rfl
      · exact hn
      · exact hp
    · exact absurd (hl.symm.trans hc) (by norm_num)
  have hwhite : ∀ c, ∃ i, laplacian F c = 0 → (i = incomingNeg c ∨ i = incomingPos c) ∧ R i < R c := by
    intro c
    rcases h c with ⟨hl, hn, hp⟩ | ⟨hl, hn | hp⟩
    · exact ⟨incomingNeg c, fun h0 => absurd (h0.symm.trans hl) (by norm_num)⟩
    · exact ⟨incomingNeg c, fun _ => ⟨Or.inl rfl, hn⟩⟩
    · exact ⟨incomingPos c, fun _ => ⟨Or.inr rfl, hp⟩⟩
  choose sel hsel using hwhite
  exact ⟨sel, fun c hc => (hsel c hc).1, fun a b =>
    squareClauses_of_burning hbin hblack (fun c hc => hsel c hc) a b⟩

/-- **The global burning rank of the sheet minimum** (task 80): the chain proof of `sheetMin_binary_recurrent_of_chain`, ending with the
combined rank `leftThresholdRank` of `M = thresholdMin A C 0`. -/
theorem sheetMin_burningRank_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    {α : Type*} [LinearOrder α] (rankA rankC : Site → α)
    (hrankA : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankA
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hrankC : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankC
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))) :
    ∃ R : Site → ℤ ×ₗ α, IsBurningRank ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) R := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  have hs : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hid : ∀ z : Site,
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z -
          (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z =
        sheetChainPotential word (standardField (conjWord word)) (z - (frameAt word).sheetShift) - K := by
    intro z
    have := hK z
    unfold sheetChainPotential
    linarith
  have hslip : ∀ c i : Site,
      slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i =
        sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift) -
          sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift) := by
    intro c i
    unfold slipIncrement
    rw [hid i, hid c]
    ring
  have hunitAC : HasUnitSlip ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) := by
    intro c i hE
    rw [hslip c i]
    exact hunit (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift)
      (edge_sub_even i c (frameAt word).sheetShift hs hE)
  have hpermA : (fun c i => slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i ≤ 0) =
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift) ≤
        sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift)) := by
    funext c i
    rw [hslip c i]
    exact propext ⟨fun hh => by linarith, fun hh => by linarith⟩
  have hA : IsConstrainedBurningRank ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
      (fun z => rankA (z - (frameAt word).sheetShift))
      (fun c i => slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i ≤ 0) := by
    rw [hpermA]
    exact ChildFrame.sheetA_rank hrankA
  have e1 : ∀ c : Site, c - ((frameAt word).sheetShift + (frameAt word).sheetOffset) +
      (frameAt word).sheetOffset = c - (frameAt word).sheetShift := fun c => by abel
  have hpermC : (fun c i => 0 ≤ slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i) =
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift) ≤
        sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift)) := by
    funext c i
    rw [hslip c i]
    exact propext ⟨fun hh => by linarith, fun hh => by linarith⟩
  have hC : IsConstrainedBurningRank ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))))
      (fun z => rankC (z - ((frameAt word).sheetShift + (frameAt word).sheetOffset)))
      (fun c i => 0 ≤ slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i) := by
    rw [hpermC]
    have h1 := ChildFrame.sheetC_rank (frame := frameAt word) hrankC
    simp only [e1] at h1
    exact h1
  have hburn := isBurningRank_leftThreshold (level := 0) hunitAC hA hC
  rw [← (frameAt word).sheetMin_eq_thresholdMin] at hburn
  exact ⟨_, hburn⟩

/-- **The satisfying selection of the sheet minimum from the conjugate's strong estimates** (task 80): the constrained ranks of `A` and `C`
(`constrainedRank_of_variant`, as in `sheetMin_recurrent_of_strong`) give a global burning rank of `M`, hence `HasSatSelection M`. -/
theorem sheetMin_hasSat_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    HasSatSelection ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  have hsheet := i3_sheetLocalInputs_of_strong h hSE
  have hG := hSE.packet
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant h hG (i3aGrade_deck h hG)
    (permitA_invariant h hG) hsheet.permitA hsheet.noA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant h hG (tGrade_add_odd_deck word)
    (permitC_invariant h hG) hsheet.permitC hsheet.noC
  obtain ⟨R, hR⟩ := sheetMin_burningRank_of_chain h hG hsheet.unit rankA rankC hrankA hrankC
  exact hasSat_of_burning R hR

end FLatticePaper.W1MRank
