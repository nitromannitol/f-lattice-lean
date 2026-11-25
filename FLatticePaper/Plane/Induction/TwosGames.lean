import FLatticePaper.Plane.Induction.TwosFreeSets
import FLatticePaper.Plane.Induction.TwosEquiv
import FLatticePaper.Plane.Induction.TwosRank
import FLatticePaper.Plane.Induction.TwosQuota
import FLatticePaper.Plane.Induction.TwosSquareShift
import FLatticePaper.Plane.Induction.TwosSlipMinusMono
import FLatticePaper.Plane.Induction.TwosChainMinus
import FLatticePaper.Plane.Induction.TwosDrifts
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.TwosTileRange
import FLatticePaper.Plane.Induction.TwosTileRangeM
import FLatticePaper.Plane.Induction.TwosLaplacianTile
import FLatticePaper.Construction.LadderExtension

/-! The canonical signed games of the twos word `2^(k+1)`: the twos policy `TwosSel` as a `CanonicalSignedPolicy` for each sign,
with the rank of each sign, and `GamesWithRank` (`twos_gamesWithRank`).

The selected inputs are the input edges: a black centre keeps both edges, a free centre keeps the free table at its free alias
(`freeDisp`), a candidate centre keeps the candidate displacement (`candDisp`); the alias translates have even coordinate sum,
so the parity of the centre is that of the alias. The free set is the deck-invariant `FreeClass`. The rank of sign `η` is
`(2d+3) Φ_η + ρ_η`, with the tile facts `hvar`, `hflat` of each sign as hypotheses. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A horizontal displacement of an even centre is an input edge. -/
theorem edge_of_even {c v : Site} (hc : EvenSite c) (h2 : v.2 = 0) (h1 : v.1 = 1 ∨ v.1 = -1) :
    Edge (c + v) c := by
  unfold Edge incomingNeg incomingPos
  rw [if_pos hc, if_pos hc]
  rcases h1 with h1 | h1
  · right
    ext
    · simp [h1]
    · simp [h2]
  · left
    ext
    · simp [h1, sub_eq_add_neg]
    · simp [h2]

/-- A vertical displacement of an odd centre is an input edge. -/
theorem edge_of_odd {c v : Site} (hc : ¬ EvenSite c) (h1 : v.1 = 0) (h2 : v.2 = 1 ∨ v.2 = -1) :
    Edge (c + v) c := by
  unfold Edge incomingNeg incomingPos
  rw [if_neg hc, if_neg hc]
  rcases h2 with h2 | h2
  · right
    ext
    · simp [h1]
    · simp [h2]
  · left
    ext
    · simp [h1]
    · simp [h2, sub_eq_add_neg]

/-- The free displacement at a free site is an input edge of every centre with the parity of the site. -/
theorem freeDisp_edge (a η : ℤ) (hη : η = 1 ∨ η = -1) {c : Site} {x y : ℤ} (hF : FreeSite a x y)
    (hp : EvenSite c ↔ EvenSite (x, y)) :
    Edge (c + freeDisp a η x y) c := by
  have hη' : ∀ v : ℤ, (v = η ∨ v = -η) → (v = 1 ∨ v = -1) := fun v hv => by
    rcases hη with rfl | rfl <;> rcases hv with rfl | rfl <;> simp
  unfold freeDisp
  by_cases hH : FreeHSite a x y
  · rw [if_pos hH]
    by_cases h10 : x = 1 ∧ y = 0
    · rw [if_pos h10]
      have hc : ¬ EvenSite c := by
        rw [hp]
        obtain ⟨rfl, rfl⟩ := h10
        unfold EvenSite
        norm_num
      exact edge_of_odd hc rfl (by rcases hη with rfl | rfl <;> simp)
    · rw [if_neg h10]
      by_cases he : EvenSite (x, y)
      · rw [if_pos he]
        exact edge_of_even (hp.mpr he) rfl (Or.inl rfl)
      · rw [if_neg he]
        exact edge_of_odd (fun h => he (hp.mp h)) rfl (Or.inl rfl)
  · rw [if_neg hH]
    by_cases h00 : x = 0 ∧ y = 0
    · rw [if_pos h00]
      have hev : EvenSite (x, y) := by
        obtain ⟨rfl, rfl⟩ := h00
        unfold EvenSite
        norm_num
      exact edge_of_even (hp.mpr hev) rfl (Or.inl rfl)
    · rw [if_neg h00]
      by_cases he : EvenSite (x, y)
      · rw [if_pos he]
        exact edge_of_even (hp.mpr he) rfl (hη' η (Or.inl rfl))
      · rw [if_neg he]
        exact edge_of_odd (fun h => he (hp.mp h)) rfl (by rcases hη with rfl | rfl <;> simp)

/-- The candidate displacement at a candidate guard is an input edge of every centre with the parity of the guard site. -/
theorem candDisp_edge (a : ℤ) (ha : a % 2 = 0) {c : Site} {x y : ℤ} (hp : EvenSite c ↔ EvenSite (x, y))
    (hg : CandGuard a x y) : Edge (c + candDisp a x y) c := by
  have hval1 : (candDisp a x y).1 = if CandE a x y then 1 else if CandW a x y then -1 else 0 := rfl
  have hval2 : (candDisp a x y).2 = if CandLow a x y ∨ CandHigh a x y then
      (if y < (if CandLow a x y then a - 1 else 2 * a - 1) then -1 else 1) else 0 := rfl
  by_cases he : EvenSite (x, y)
  · have hc : EvenSite c := hp.mpr he
    have hnb : ¬ (CandLow a x y ∨ CandHigh a x y) := by
      unfold CandLow CandHigh
      unfold EvenSite at he
      dsimp only at he
      omega
    have hEW : CandE a x y ∨ CandW a x y := by
      unfold CandGuard at hg
      rcases hg with h | h | h | h
      · exact absurd (Or.inl h) hnb
      · exact absurd (Or.inr h) hnb
      · exact Or.inl h
      · exact Or.inr h
    have hv2 : (candDisp a x y).2 = 0 := by
      rw [hval2, if_neg hnb]
    have hv1 : (candDisp a x y).1 = 1 ∨ (candDisp a x y).1 = -1 := by
      rw [hval1]
      rcases hEW with h | h
      · rw [if_pos h]
        left
        rfl
      · have hnE : ¬ CandE a x y := by
          unfold CandE CandW at *
          omega
        rw [if_neg hnE, if_pos h]
        right
        rfl
    exact edge_of_even hc hv2 hv1
  · have hc : ¬ EvenSite c := fun h => he (hp.mp h)
    have hnE : ¬ CandE a x y := by
      unfold CandE
      unfold EvenSite at he
      dsimp only at he
      omega
    have hnW : ¬ CandW a x y := by
      unfold CandW
      unfold EvenSite at he
      dsimp only at he
      omega
    have hbands : CandLow a x y ∨ CandHigh a x y := by
      unfold CandGuard at hg
      rcases hg with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnE
      · exact absurd h hnW
    have hv1 : (candDisp a x y).1 = 0 := by
      rw [hval1, if_neg hnE, if_neg hnW]
    have hv2 : (candDisp a x y).2 = 1 ∨ (candDisp a x y).2 = -1 := by
      rw [hval2, if_pos hbands]
      split_ifs <;> simp
    exact edge_of_odd hc hv1 hv2

/-- The alias translates have the parity of their centre: the lattice vectors have even coordinate sums. -/
theorem aliasOf_evenSite {k : ℕ} {c u : Site} (h : AliasOf (2 * (k : ℤ) + 4) c u) :
    EvenSite u ↔ EvenSite c := by
  obtain ⟨i, l, hu⟩ := h
  have e : u.1 + u.2 = (c.1 + c.2) + 2 * (-((2 * (k : ℤ) + 4)) * i - (2 * (k : ℤ) + 3) * l) := by
    rw [hu]
    ring
  generalize hX : -((2 * (k : ℤ) + 4)) * i - (2 * (k : ℤ) + 3) * l = X at e
  unfold EvenSite
  omega

/-- A selected input of the twos policy is an input edge of its centre (both signs). -/
theorem twosSel_edge {k : ℕ} {η : ℤ} {F : Field} {c i : Site} (hη : η = 1 ∨ η = -1)
    (hT : TwosSel (2 * (k : ℤ) + 4) η F c i) : Edge i c := by
  rcases hT with ⟨-, he⟩ | ⟨-, ⟨u, hu, hF, hi⟩ | ⟨-, u, hu, hn, hg, hi⟩⟩
  · exact he
  · have hp : EvenSite c ↔ EvenSite (u.1, u.2) := (aliasOf_evenSite hu).symm
    rw [hi]
    exact freeDisp_edge (2 * (k : ℤ) + 4) η hη hF hp
  · have hp : EvenSite c ↔ EvenSite (u.1, u.2) := (aliasOf_evenSite hu).symm
    rw [hi]
    exact candDisp_edge (2 * (k : ℤ) + 4) (by omega) hp hg

/-- A translate of the centre by a deck vector `ki U + ti V` keeps the alias relation. -/
theorem aliasOf_add_lattice {k : ℕ} {c u s : Site}
    (hs : ∃ ki ti : ℤ, s = (ki * (2 * (k : ℤ) + 5) + ti * (-2), ki * (2 * (k : ℤ) + 3) + ti * (4 * (k : ℤ) + 8))) :
    AliasOf (2 * (k : ℤ) + 4) (c + s) u ↔ AliasOf (2 * (k : ℤ) + 4) c u := by
  obtain ⟨ki, ti, rfl⟩ := hs
  unfold AliasOf
  constructor
  · rintro ⟨i, l, hu⟩
    refine ⟨i - ki, l - ti, ?_⟩
    rw [hu]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring
  · rintro ⟨i, l, hu⟩
    refine ⟨i + ki, l + ti, ?_⟩
    rw [hu]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      ring

/-- The deck span of the twos frame consists of the lattice vectors `ki U + ti V`. -/
theorem twos_span_form (k : ℕ) {step : Site}
    (hstep : step ∈ (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.span) :
    ∃ ki ti : ℤ, step = (ki * (2 * (k : ℤ) + 5) + ti * (-2), ki * (2 * (k : ℤ) + 3) + ti * (4 * (k : ℤ) + 8)) := by
  obtain ⟨ki, ti, hs⟩ := hstep
  refine ⟨ki, ti, ?_⟩
  rw [hs]
  unfold PeriodDeck.combine
  rw [twos_kernel_explicit, twos_transverse_explicit]

/-- The free set `FreeClass` is invariant under the deck span. -/
theorem freeClass_add_span (k : ℕ) {c step : Site}
    (hstep : step ∈ (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.span) :
    FreeClass (2 * (k : ℤ) + 4) (c + step) ↔ FreeClass (2 * (k : ℤ) + 4) c := by
  obtain ⟨ki, ti, hs⟩ := twos_span_form k hstep
  unfold FreeClass
  constructor
  · rintro ⟨u, hu, hF⟩
    exact ⟨u, (aliasOf_add_lattice ⟨ki, ti, hs⟩).mp hu, hF⟩
  · rintro ⟨u, hu, hF⟩
    exact ⟨u, (aliasOf_add_lattice ⟨ki, ti, hs⟩).mpr hu, hF⟩

/-- At a white centre the selected input of the twos policy exists (the quota). -/
theorem twosSel_spec {S : Field} {k : ℕ} (η : ℤ)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c : Site} (hw : laplacian (standardField (List.replicate (k + 1) Digit.two)) c = 0) :
    TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c
      (twosSelFun k η (standardField (List.replicate (k + 1) Digit.two)) c) :=
  Classical.epsilon_spec (twos_white_quota k hagree hperiod η c hw).1

/-- At a white centre the selected input is the only selected input of the twos policy (the quota). -/
theorem twosSel_unique {S : Field} {k : ℕ} (η : ℤ)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site} (hw : laplacian (standardField (List.replicate (k + 1) Digit.two)) c = 0)
    (hi : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) :
    i = twosSelFun k η (standardField (List.replicate (k + 1) Digit.two)) c :=
  (twos_white_quota k hagree hperiod η c hw).2 i _ hi (twosSel_spec η hagree hperiod hw)

/-- The retained inputs of the twos policy form a quota (both inputs at a black, one at a white). -/
theorem twosSel_quota {S : Field} {k : ℕ} (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4))) :
    RetainQuota (standardField (List.replicate (k + 1) Digit.two))
      (TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two))) := by
  refine ⟨fun c hl => ⟨Or.inl ⟨hl, Or.inl rfl⟩, Or.inl ⟨hl, Or.inr rfl⟩⟩, fun c hw => ?_⟩
  have hi := twosSel_spec η hagree hperiod hw
  rcases twosSel_edge hη hi with h | h
  · exact Or.inl (h ▸ hi)
  · exact Or.inr (h ▸ hi)

/-- The slip permits of the twos policy: the sign `η` slip does not increase along the selected inputs. -/
theorem twos_permitted {S : Field} {k : ℕ} (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (h : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) :
    slipPermits (standardField (List.replicate (k + 1) Digit.two))
      (fun z => standardField (List.replicate (k + 1) Digit.two) (z + η • (frameAt (List.replicate (k + 1) Digit.two)).shortShift))
      c i := by
  rcases hη with rfl | rfl
  · have hs := twosSlip_nonincreasing k hagree hperiod h
    have hs' : (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 i ≤
        (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) 1 c := by
      rw [slip_one_eq, slip_one_eq]
      exact hs
    unfold slipPermits slipIncrement
    unfold ChildFrame.slip at hs'
    linarith
  · have hs := twosSlipM_nonincreasing k hagree hperiod h
    unfold slipPermits slipIncrement
    unfold ChildFrame.slip at hs
    linarith

/-- The price does not increase along the selected inputs of the twos policy (both signs). -/
theorem twos_price_signed {S : Field} {k : ℕ} (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (h : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) :
    (frameAt (List.replicate (k + 1) Digit.two)).cutGrade (standardField (List.replicate (k + 1) Digit.two)) 1 0 1 i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).cutGrade (standardField (List.replicate (k + 1) Digit.two)) 1 0 1 c := by
  rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
  exact twosP_nonincreasing k hagree hperiod hη h

/-- The rounded slip does not increase along the selected inputs of the twos policy (both signs). -/
theorem twos_roundedSlip_signed {S : Field} {k : ℕ} (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (h : TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i) :
    (frameAt (List.replicate (k + 1) Digit.two)).cutGrade (standardField (List.replicate (k + 1) Digit.two)) 0 1 η i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).cutGrade (standardField (List.replicate (k + 1) Digit.two)) 0 1 η c := by
  unfold ChildFrame.cutGrade
  simp only [zero_mul, zero_add, one_mul]
  rcases hη with rfl | rfl
  · exact twos_roundedSlip_nonincreasing k hagree hperiod h
  · exact twos_roundedSlipM_nonincreasing k hagree hperiod h

/-- The chain potential of sign `-1` drops by one along the kernel (`Ψ(a + U) = Ψ(a) - 1`). -/
theorem chainM_kernel (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) z - 1 := by
  rw [twos_kernel_explicit, chainM_eq, chainM_eq]
  have e1 : (z + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3)).1 - 1 = (z.1 - 1) + (2 * (k : ℤ) + 5) := by
    simp only [Prod.fst_add]
    ring
  have e2 : (z + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3)).2 - 1 = (z.2 - 1) + (2 * (k : ℤ) + 3) := by
    simp only [Prod.snd_add]
    ring
  rw [e1, e2, psi_U_shift]

/-- The chain potential of sign `-1` drops by two along the transverse (`Ψ(a + V) = Ψ(a) - 2`). -/
theorem chainM_transverse (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1)
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) z - 2 := by
  rw [twos_transverse_explicit, chainM_eq, chainM_eq]
  have e1 : (z + (-2, 4 * (k : ℤ) + 8)).1 - 1 = (z.1 - 1) + (0 * (2 * (k : ℤ) + 5) + 1 * (-2)) := by
    simp only [Prod.fst_add]
    ring
  have e2 : (z + (-2, 4 * (k : ℤ) + 8)).2 - 1 = (z.2 - 1) + (0 * (2 * (k : ℤ) + 3) + 1 * (4 * (k : ℤ) + 8)) := by
    simp only [Prod.snd_add]
    ring
  rw [e1, e2, twosPsi_lattice]
  ring

/-- The rank of sign `-1`: `(2d+3) Φ₋₁ + ρ₋₁`, with `Φ₋₁` the chain potential of sign `-1`. -/
noncomputable def twosRankM (k : ℕ) (z : Site) : ℤ :=
  (2 * (2 * (k : ℤ) + 5) + 3) *
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) z +
    rhoTwos (2 * (k : ℤ) + 4) (-1) z

/-- The rank of sign `η` of the twos policy: `twosRank` at `η = 1` and `twosRankM` at `η = -1`. -/
noncomputable def twosRankOf (k : ℕ) (η : ℤ) (z : Site) : ℤ :=
  if η = 1 then twosRank k z else twosRankM k z

/-- The sign `η` rank drops by `M = 2d+3` along the kernel and changes by `2 η M` along the transverse. -/
theorem twosRankOf_kernel (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    twosRankOf k η (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      twosRankOf k η z - (2 * (2 * (k : ℤ) + 5) + 3) := by
  rcases hη with rfl | rfl
  · unfold twosRankOf
    simp only [if_true]
    exact twosRank_kernel k z
  · unfold twosRankOf twosRankM
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    rw [chainM_kernel]
    have hr : rhoTwos (2 * (k : ℤ) + 4) (-1)
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) = rhoTwos (2 * (k : ℤ) + 4) (-1) z := by
      rw [twos_kernel_explicit]
      exact rhoTwos_kernel k (-1) z
    rw [hr]
    ring

theorem twosRankOf_transverse (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (z : Site) :
    twosRankOf k η (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      twosRankOf k η z + 2 * η * (2 * (2 * (k : ℤ) + 5) + 3) := by
  rcases hη with rfl | rfl
  · unfold twosRankOf
    simp only [if_true]
    rw [twosRank_transverse]
    ring
  · unfold twosRankOf twosRankM
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    rw [chainM_transverse]
    have hr : rhoTwos (2 * (k : ℤ) + 4) (-1)
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) = rhoTwos (2 * (k : ℤ) + 4) (-1) z := by
      rw [twos_transverse_explicit]
      exact rhoTwos_transverse k (-1) z
    rw [hr]
    ring

/-- The strict decrease of the sign `-1` rank along the selected inputs (the tile facts `hvar`, `hflat` of sign `-1`). -/
theorem twosRankM_strict (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (hvar : ∀ z w : Site, rhoTwos (2 * (k : ℤ) + 4) (-1) z - rhoTwos (2 * (k : ℤ) + 4) (-1) w < 2 * (2 * (k : ℤ) + 5) + 3)
    (hflat : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) c)
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i) :
    twosRankM k i < twosRankM k c := by
  have hC := twosChainM_nonincreasing k hagree hperiod hT
  rcases lt_or_eq_of_le hC with hlt | heq
  · have hM0 : (0 : ℤ) ≤ 2 * (2 * (k : ℤ) + 5) + 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (show (frameAt (List.replicate (k + 1) Digit.two)).chainPotential
        (standardField (List.replicate (k + 1) Digit.two)) (-1) i + 1 ≤
          (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c
        by omega) hM0
    have h2 := hvar i c
    unfold twosRankM
    nlinarith
  · have h3 := hflat c i hT heq
    unfold twosRankM
    rw [heq]
    linarith

/-- The rank of sign `η` is strict along the selected inputs of the twos policy (both signs). -/
theorem twosRankOf_strict (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (hvarP : ∀ z w : Site, rhoTwos (2 * (k : ℤ) + 4) 1 z - rhoTwos (2 * (k : ℤ) + 4) 1 w < 2 * (2 * (k : ℤ) + 5) + 3)
    (hflatP : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 c)
    (hvarM : ∀ z w : Site, rhoTwos (2 * (k : ℤ) + 4) (-1) z - rhoTwos (2 * (k : ℤ) + 4) (-1) w < 2 * (2 * (k : ℤ) + 5) + 3)
    (hflatM : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) c) :
    ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i →
      twosRankOf k η i < twosRankOf k η c := by
  intro c i hT
  rcases hη with rfl | rfl
  · unfold twosRankOf
    rw [if_pos rfl, if_pos rfl]
    exact twosRank_strict k hagree hperiod hvarP hflatP hT
  · unfold twosRankOf
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    exact twosRankM_strict k hagree hperiod hvarM hflatM hT

/-- The canonical signed policy of the twos word for the sign `η`, with the strict rank `R` of the sign. -/
noncomputable def twosSignedPolicy {S : Field} (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (R : Site → ℤ)
    (hR : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) c i → R i < R c) :
    CanonicalSignedPolicy (frameAt (List.replicate (k + 1) Digit.two))
      (standardField (List.replicate (k + 1) Digit.two)) η where
  policy := TwosSel (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two))
  free := FreeClass (2 * (k : ℤ) + 4)
  freeInvariant := fun step hstep site => freeClass_add_span k hstep
  quota := twosSel_quota η hη hagree hperiod
  permitted := fun c i h => twos_permitted η hη hagree hperiod h
  nonincreasingP := fun c i h => twos_price_signed η hη hagree hperiod h
  nonincreasingJ := fun c i h => twos_roundedSlip_signed η hη hagree hperiod h
  rank := R
  strictRank := fun c i h _ _ => hR c i h
  freePrescribed := fun c _ hw => ⟨twosSelFun k η (standardField (List.replicate (k + 1) Digit.two)) c,
    twosSel_edge hη (twosSel_spec η hagree hperiod hw), fun j =>
      ⟨fun h => twosSel_unique η hagree hperiod hw h, fun h => by
        rw [h]
        exact twosSel_spec η hagree hperiod hw⟩⟩
  sel := twosSelFun k η (standardField (List.replicate (k + 1) Digit.two))
  sel_input := fun c hw => twosSel_edge hη (twosSel_spec η hagree hperiod hw)
  white_policy := fun c hw i => ⟨fun h => twosSel_unique η hagree hperiod hw h, fun h => by
    rw [h]
    exact twosSel_spec η hagree hperiod hw⟩
  squares := fun a b => twos_squareClauseSat hη hagree hperiod a b
  prescribed := twos_prescribedAt k η hagree hperiod
  policyEdge := fun c i h => twosSel_edge hη h
  westAtException := fun h => absurd h (by rw [twos_frame_eps (k + 1)]; norm_num)

/-- **The canonical signed games of the twos word `2^(k+1)`**, from the two tile facts of each sign (`hvar`, `hflat`). -/
noncomputable def twosCanonicalGames {S : Field} (k : ℕ)
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4))
      S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (hvarP : ∀ z w : Site, rhoTwos (2 * (k : ℤ) + 4) 1 z - rhoTwos (2 * (k : ℤ) + 4) 1 w < 2 * (2 * (k : ℤ) + 5) + 3)
    (hflatP : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 c)
    (hvarM : ∀ z w : Site, rhoTwos (2 * (k : ℤ) + 4) (-1) z - rhoTwos (2 * (k : ℤ) + 4) (-1) w < 2 * (2 * (k : ℤ) + 5) + 3)
    (hflatM : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) c) :
    CanonicalSignedGames (frameAt (List.replicate (k + 1) Digit.two))
      (standardField (List.replicate (k + 1) Digit.two)) where
  game := fun η hη => twosSignedPolicy k η hη hagree hperiod (twosRankOf k η)
    (twosRankOf_strict k η hη hagree hperiod hvarP hflatP hvarM hflatM)
  deckEquiv := fun η _ i j x u => by
    have hper := twos_standardField_periods k hagree hperiod
    have hcomb : (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j =
        (i * (2 * (k : ℤ) + 4 + 1) - 2 * j, i * (2 * (k : ℤ) + 4 - 1) + 2 * (2 * (k : ℤ) + 4) * j) := by
      have hc : ((1 : ℤ) + (2 * (k : ℤ) + 4)) % 2 = 1 := by omega
      rw [ChildFrame.combine_coords, child_replicate_two_succ]
      unfold Fraction.rotate
      dsimp only
      rw [if_pos hc]
      ext <;> simp <;> ring
    have hL : ∀ c, laplacian (standardField (List.replicate (k + 1) Digit.two))
        (c + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j) =
        laplacian (standardField (List.replicate (k + 1) Digit.two)) c := fun c =>
      laplacian_add_combine hper c i j
    exact (FLatticePaper.TwosEquiv.twosSel_shift (2 * (k : ℤ) + 4) η i j
      (standardField (List.replicate (k + 1) Digit.two))
      ((frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j) hcomb hL x u).symm
  chainNonincreasing := fun η hη c i h => by
    rcases hη with rfl | rfl
    · exact twosChain_nonincreasing k hagree hperiod h
    · exact twosChainM_nonincreasing k hagree hperiod h

/-- **The twos word `2^(k+1)` has games with rank** (`GamesWithRank`). The auxiliary field `S` with the agreement and periods
of the raw ladder mask is an extension (`ladderOdd_exists_extension`); the standard field is its rotation, so the agreement is
stated for `S`, not for the standard field. The sign `+1` tile fact `hvar` is `tr_hvar`; the other facts are hypotheses. -/
theorem twos_gamesWithRank (k : ℕ)
    (hflatP : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 c)
    (hflatM : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      rhoTwos (2 * (k : ℤ) + 4) (-1) i < rhoTwos (2 * (k : ℤ) + 4) (-1) c) :
    GamesWithRank (List.replicate (k + 1) Digit.two) := by
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension (ladderOdd_valid_twos k)
  refine ⟨twosCanonicalGames k hagree hperiod (fun z w => tr_hvar k z w) hflatP (fun z w => tr_hvarM k z w) hflatM, fun η hη => ⟨twosRankOf k η,
    -(2 * (2 * (k : ℤ) + 5) + 3), 2 * η * (2 * (2 * (k : ℤ) + 5) + 3), fun z => ?_, fun z => ?_, fun x i hxi => ?_⟩⟩
  · rw [twosRankOf_kernel k η hη z, sub_eq_add_neg]
  · exact twosRankOf_transverse k η hη z
  · exact twosRankOf_strict k η hη hagree hperiod (fun z w => tr_hvar k z w) hflatP (fun z w => tr_hvarM k z w) hflatM x i hxi

end FLatticePaper.TwosEPolicy
