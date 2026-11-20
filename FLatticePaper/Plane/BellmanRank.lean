import FLatticePaper.Farey.PeriodDeck
import FLatticePaper.Plane.AlternateSlip
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

namespace FLatticePaper

open Farey

/-- The input quotas of a fort, with no finiteness assumption on its sites. -/
def IsIncomingFort (field : Field) (sites : Set Site) : Prop :=
  ∀ site ∈ sites,
    (laplacian field site = -1 ∧ (incomingNeg site ∈ sites ∨ incomingPos site ∈ sites)) ∨
    (laplacian field site = 0 ∧ incomingNeg site ∈ sites ∧ incomingPos site ∈ sites)

/-- At a site below the threshold the play can stop. Otherwise one physical
input is chosen at charge zero, and both must be covered at charge one. -/
def EscapesWithin (field grade : Field) (level : ℤ) : ℕ → Site → Prop
  | 0, site => grade site < level
  | n + 1, site => grade site < level ∨
      (laplacian field site = -1 ∧ EscapesWithin field grade level n (incomingNeg site) ∧
        EscapesWithin field grade level n (incomingPos site)) ∨
      (laplacian field site = 0 ∧ (EscapesWithin field grade level n (incomingNeg site) ∨
        EscapesWithin field grade level n (incomingPos site)))

theorem escapesWithin_succ {field grade : Field} {level : ℤ} (n : ℕ) (site : Site)
    (h : EscapesWithin field grade level n site) : EscapesWithin field grade level (n + 1) site := by
  induction n generalizing site with
  | zero => exact Or.inl h
  | succ n ih =>
    rcases h with h | ⟨hl, hn, hp⟩ | ⟨hl, hn | hp⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hl, ih _ hn, ih _ hp⟩)
    · exact Or.inr (Or.inr ⟨hl, Or.inl (ih _ hn)⟩)
    · exact Or.inr (Or.inr ⟨hl, Or.inr (ih _ hp)⟩)

theorem escapesWithin_mono {field grade : Field} {level : ℤ} {site : Site} {n m : ℕ}
    (hnm : n ≤ m) (h : EscapesWithin field grade level n site) : EscapesWithin field grade level m site := by
  have hmono : Monotone fun k => EscapesWithin field grade level k site :=
    monotone_nat_of_le_succ (fun k => escapesWithin_succ k site)
  exact hmono hnm h

/-- If a half-space contains no nonempty fort, pruning its actual incoming
stars gives a finite exit strategy at each site. -/
theorem exists_escapeDepth_of_no_incomingFort {field grade : Field} {level : ℤ}
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hno : ∀ sites : Set Site, sites.Nonempty → IsIncomingFort field sites →
      (∀ site ∈ sites, level ≤ grade site) → False) (site : Site) :
    ∃ n, EscapesWithin field grade level n site := by
  classical
  by_contra! hsite
  let remaining : Set Site := {site | ∀ n, ¬ EscapesWithin field grade level n site}
  have hesc {point : Site} (hout : point ∉ remaining) : ∃ n, EscapesWithin field grade level n point := by
    simpa only [remaining, Set.mem_setOf_eq, not_forall, not_not] using hout
  apply hno remaining ⟨site, hsite⟩ ?_ (fun point hp => le_of_not_gt (hp 0))
  intro point hp
  rcases hbinary point with hl | hl
  · left
    refine ⟨hl, ?_⟩
    by_contra! hout
    obtain ⟨n, hn⟩ := hesc hout.1
    obtain ⟨m, hm⟩ := hesc hout.2
    exact hp (max n m + 1) (Or.inr (Or.inl ⟨hl,
      escapesWithin_mono (le_max_left ..) hn, escapesWithin_mono (le_max_right ..) hm⟩))
  · right
    refine ⟨hl, ?_, ?_⟩
    · intro n hn
      exact hp (n + 1) (Or.inr (Or.inr ⟨hl, Or.inl hn⟩))
    · intro n hn
      exact hp (n + 1) (Or.inr (Or.inr ⟨hl, Or.inr hn⟩))

theorem escapesWithin_add_iff {field grade : Field} {step : Site} {increment : ℤ}
    (heven : EvenSite step) (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ site, grade (site + step) = grade site + increment)
    (level : ℤ) (n : ℕ) (site : Site) :
    EscapesWithin field grade (level + increment) n (site + step) ↔ EscapesWithin field grade level n site := by
  induction n generalizing site with
  | zero => simp only [EscapesWithin, hgrade, add_lt_add_iff_right]
  | succ n ih =>
    simp only [EscapesWithin, hcharge, hgrade, add_lt_add_iff_right,
      incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven, ih]

/-- A cover by finitely many period representatives makes the local exit
depths uniform. The threshold at each site is its own grade. -/
theorem exists_uniform_escapeDepth {field grade : Field} {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hdepth : ∀ site, ∃ n, EscapesWithin field grade (grade site) n site) :
    ∃ horizon : ℕ, 0 < horizon ∧ ∀ site, EscapesWithin field grade (grade site) horizon site := by
  classical
  choose depth hdepth using hdepth
  let horizon := sites.sup depth + 1
  refine ⟨horizon, by simp [horizon], fun site => ?_⟩
  obtain ⟨representative, hmem, hstep⟩ := hcover site
  let step := site - representative
  have hreconstruct : representative + step = site := by dsimp [step]; rw [add_comm, sub_add_cancel]
  obtain ⟨increment, hinc⟩ := hgrade step hstep
  have hle : depth representative ≤ horizon :=
    (Finset.le_sup (f := depth) hmem).trans (by omega)
  have hescape := escapesWithin_mono hle (hdepth representative)
  have h := (escapesWithin_add_iff (heven step hstep) (hcharge step hstep) hinc
    (grade representative) horizon representative).mpr hescape
  rw [← hinc, hreconstruct] at h
  exact h

/-- Both incoming grade jumps have a common nonnegative upper bound. -/
theorem exists_incomingGradeJumpBound {grade : Field} {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment) :
    ∃ bound : ℤ, 0 ≤ bound ∧ ∀ site,
      grade (incomingNeg site) ≤ grade site + bound ∧ grade (incomingPos site) ≤ grade site + bound := by
  let jump (site : Site) := max (grade (incomingNeg site) - grade site) (grade (incomingPos site) - grade site)
  refine ⟨(↑(sites.sup (fun site => (jump site).toNat)) : ℤ), by positivity, fun site => ?_⟩
  obtain ⟨representative, hmem, hstep⟩ := hcover site
  let step := site - representative
  have hreconstruct : representative + step = site := by dsimp [step]; rw [add_comm, sub_add_cancel]
  obtain ⟨increment, hinc⟩ := hgrade step hstep
  have hsup := Finset.le_sup (f := fun site => (jump site).toNat) hmem
  have hneg := le_max_left (grade (incomingNeg representative) - grade representative)
    (grade (incomingPos representative) - grade representative)
  have hpos := le_max_right (grade (incomingNeg representative) - grade representative)
    (grade (incomingPos representative) - grade representative)
  change _ ≤ jump representative at hneg hpos
  rw [← hreconstruct, incomingNeg_add_of_even _ _ (heven step hstep),
    incomingPos_add_of_even _ _ (heven step hstep), hinc, hinc, hinc]
  constructor <;> omega

/-- At charge one continuation pays the worse of the two input values. At
charge zero the strategy can choose either actual input. -/
def bellmanInputs (field value : Field) (site : Site) : ℤ :=
  if laplacian field site = -1 then max (value (incomingNeg site)) (value (incomingPos site))
  else min (value (incomingNeg site)) (value (incomingPos site))

/-- The obstacle is the payoff for stopping. Each continuation earns one. -/
def bellmanValue (field obstacle : Field) : ℕ → Field
  | 0 => obstacle
  | n + 1 => fun site => max (obstacle site) (1 + bellmanInputs field (bellmanValue field obstacle n) site)

theorem obstacle_le_bellmanValue (field obstacle : Field) (n : ℕ) (site : Site) :
    obstacle site ≤ bellmanValue field obstacle n site := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left ..

theorem bellmanValue_mono (field obstacle : Field) (site : Site) :
    Monotone fun n => bellmanValue field obstacle n site := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing site with
  | zero => exact obstacle_le_bellmanValue field obstacle 1 site
  | succ n ih =>
    refine max_le_max le_rfl (add_le_add_right ?_ 1)
    unfold bellmanInputs
    split
    · exact max_le_max (ih _) (ih _)
    · exact min_le_min (ih _) (ih _)

theorem bellmanValue_add {field obstacle : Field} {step : Site} {increment : ℤ}
    (heven : EvenSite step) (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hobstacle : ∀ site, obstacle (site + step) = obstacle site + increment)
    (n : ℕ) (site : Site) :
    bellmanValue field obstacle n (site + step) = bellmanValue field obstacle n site + increment := by
  induction n generalizing site with
  | zero => exact hobstacle site
  | succ n ih =>
    simp only [bellmanValue, bellmanInputs, hcharge, hobstacle, incomingNeg_add_of_even _ _ heven,
      incomingPos_add_of_even _ _ heven, ih]
    split <;> simp only [max_add_add_right, min_add_add_right, ← add_assoc]

/-- Uniform grade exits bound the payoff even when the game stops partway
through an exit segment. Here `used` counts moves in the current segment. -/
theorem bellmanValue_le_of_uniform_escape {field grade : Field} {horizon : ℕ} {bound : ℤ}
    (hjump : ∀ site, grade (incomingNeg site) ≤ grade site + bound ∧
      grade (incomingPos site) ≤ grade site + bound)
    (hbound : 0 ≤ bound)
    (hescape : ∀ site, EscapesWithin field grade (grade site) horizon site)
    (n : ℕ) (site : Site) :
    bellmanValue field (fun point => (horizon : ℤ) * grade point) n site ≤
      (horizon : ℤ) * grade site + ((horizon : ℤ) + (horizon : ℤ) ^ 2 * bound) := by
  let scale : ℤ := horizon
  let obstacle : Field := fun point => scale * grade point
  let budget := scale + scale ^ 2 * bound
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hstop (point : Site) (level : ℤ) (used : ℕ)
      (htime : used ≤ horizon) (hupper : grade point ≤ level + (used : ℤ) * bound) :
      obstacle point ≤ scale * level + budget - (used : ℤ) := by
    have hused : (used : ℤ) ≤ scale := by simpa [scale] using (Int.ofNat_le.mpr htime)
    have hj := mul_le_mul_of_nonneg_right hused hbound
    have hgrade : grade point ≤ level + scale * bound := by omega
    have hm := mul_le_mul_of_nonneg_left hgrade hscale
    dsimp only [obstacle, budget]
    nlinarith only [hused, hm]
  have hlocal (n : ℕ) (point : Site) (level : ℤ) (used left : ℕ)
      (htime : used + left ≤ horizon) (hlower : level ≤ grade point)
      (hupper : grade point ≤ level + (used : ℤ) * bound)
      (hexit : EscapesWithin field grade level left point) :
      bellmanValue field obstacle n point ≤ scale * level + budget - (used : ℤ) := by
    induction n generalizing point level used left with
    | zero => exact hstop point level used (by omega) hupper
    | succ n ih =>
      cases left with
      | zero => exact (not_lt_of_ge hlower hexit).elim
      | succ left =>
        have hnext (input : Site) (hup : grade input ≤ grade point + bound)
            (hin : EscapesWithin field grade level left input) :
            bellmanValue field obstacle n input ≤ scale * level + budget - ((used + 1 : ℕ) : ℤ) := by
          by_cases hdrop : grade input < level
          · have hglobal := ih input (grade input) 0 horizon (by omega) le_rfl (by simp) (hescape input)
            have hgap := mul_le_mul_of_nonneg_left (show grade input ≤ level - 1 by omega) hscale
            have hused : ((used + 1 : ℕ) : ℤ) ≤ scale := by
              simpa [scale] using (Int.ofNat_le.mpr (show used + 1 ≤ horizon by omega))
            rw [mul_sub, mul_one] at hgap
            omega
          · refine ih input level (used + 1) left (by omega) (le_of_not_gt hdrop) ?_ hin
            push_cast
            rw [add_mul, one_mul]
            omega
        refine max_le (hstop point level used (by omega) hupper) ?_
        rcases hexit with hbelow | ⟨hblack, hn, hp⟩ | ⟨hwhite, hn | hp⟩
        · exact (not_lt_of_ge hlower hbelow).elim
        · have hvalue := max_le (hnext _ (hjump point).1 hn) (hnext _ (hjump point).2 hp)
          simp only [bellmanInputs, if_pos hblack]
          omega
        · have hvalue := (min_le_left (bellmanValue field obstacle n (incomingNeg point))
            (bellmanValue field obstacle n (incomingPos point))).trans (hnext _ (hjump point).1 hn)
          simp only [bellmanInputs, show laplacian field point ≠ -1 by omega, if_false]
          omega
        · have hvalue := (min_le_right (bellmanValue field obstacle n (incomingNeg point))
            (bellmanValue field obstacle n (incomingPos point))).trans (hnext _ (hjump point).2 hp)
          simp only [bellmanInputs, show laplacian field point ≠ -1 by omega, if_false]
          omega
  simpa only [obstacle, budget, scale, Nat.cast_zero, sub_zero] using
    hlocal n site (grade site) 0 horizon (by omega) le_rfl (by simp) (hescape site)

/-- A uniformly bounded monotone integer correction on a finite deck
stabilizes simultaneously at every site. -/
private theorem exists_bellmanValue_fixed {field obstacle : Field} {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hshift : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, obstacle (site + step) = obstacle site + increment)
    (budget : ℤ) (hupper : ∀ n site, bellmanValue field obstacle n site ≤ obstacle site + budget) :
    ∃ n, bellmanValue field obstacle (n + 1) = bellmanValue field obstacle n := by
  classical
  have hmaximum (site : Site) : ∃ n, ∀ m, bellmanValue field obstacle m site ≤ bellmanValue field obstacle n site := by
    let values := (Finset.Icc (obstacle site) (obstacle site + budget)).filter
      (fun value => ∃ n, bellmanValue field obstacle n site = value)
    have hmem (m : ℕ) : bellmanValue field obstacle m site ∈ values :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨obstacle_le_bellmanValue field obstacle m site, hupper m site⟩, m, rfl⟩
    obtain ⟨largest, hmemLargest, hmax⟩ := values.exists_max_image id ⟨_, hmem 0⟩
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp hmemLargest).2
    exact ⟨n, fun m => hn ▸ hmax _ (hmem m)⟩
  choose depth hdepth using hmaximum
  let n := sites.sup depth
  refine ⟨n, funext fun site => ?_⟩
  obtain ⟨representative, hmem, hstep⟩ := hcover site
  let step := site - representative
  have hreconstruct : representative + step = site := by dsimp [step]; rw [add_comm, sub_add_cancel]
  obtain ⟨increment, hinc⟩ := hshift step hstep
  have hle : depth representative ≤ n := Finset.le_sup hmem
  have heq : bellmanValue field obstacle (n + 1) representative = bellmanValue field obstacle n representative :=
    le_antisymm ((hdepth representative _).trans (bellmanValue_mono field obstacle representative hle))
      (bellmanValue_mono field obstacle representative (by omega))
  rw [← hreconstruct, bellmanValue_add (heven step hstep) (hcharge step hstep) hinc,
    bellmanValue_add (heven step hstep) (hcharge step hstep) hinc, heq]

/-- With no nonempty fort in any grade half-space, the physical binary field
has a strict rank. Its deck character is a positive integer multiple of the
grade character, with a bounded periodic correction. -/
theorem exists_burningRank_of_no_incomingFort {field grade : Field} {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hno : ∀ (level : ℤ) (fort : Set Site), fort.Nonempty → IsIncomingFort field fort →
      (∀ site ∈ fort, level ≤ grade site) → False) :
    ∃ (scale : ℤ) (remainder : Field) (budget : ℤ), 0 < scale ∧
      (∀ site, 0 ≤ remainder site ∧ remainder site ≤ budget) ∧
      (∀ step ∈ deck.span, ∀ site, remainder (site + step) = remainder site) ∧
      IsBurningRank field (fun site => scale * grade site + remainder site) := by
  obtain ⟨horizon, hpos, hescape⟩ := exists_uniform_escapeDepth hcover heven hcharge hgrade
    (fun site => exists_escapeDepth_of_no_incomingFort hbinary (hno (grade site)) site)
  obtain ⟨bound, hbound, hjump⟩ := exists_incomingGradeJumpBound hcover heven hgrade
  let scale : ℤ := horizon
  let obstacle : Field := fun site => scale * grade site
  let budget := scale + scale ^ 2 * bound
  have hupper (n : ℕ) (site : Site) : bellmanValue field obstacle n site ≤ obstacle site + budget :=
    bellmanValue_le_of_uniform_escape hjump hbound hescape n site
  have hshift (step : Site) (hmem : step ∈ deck.span) :
      ∃ increment : ℤ, ∀ site, obstacle (site + step) = obstacle site + increment := by
    obtain ⟨increment, hinc⟩ := hgrade step hmem
    exact ⟨scale * increment, fun site => by simp only [obstacle, hinc, mul_add]⟩
  obtain ⟨n, hn⟩ := exists_bellmanValue_fixed hcover heven hcharge hshift budget hupper
  let rank := bellmanValue field obstacle n
  let remainder : Field := fun site => rank site - obstacle site
  refine ⟨scale, remainder, budget, by simpa [scale] using (Int.ofNat_lt.mpr hpos), ?_, ?_, ?_⟩
  · intro site
    have hlo := obstacle_le_bellmanValue field obstacle n site
    have hhi := hupper n site
    dsimp only [remainder, rank]
    omega
  · intro step hmem site
    obtain ⟨increment, hinc⟩ := hshift step hmem
    simp only [remainder, rank, bellmanValue_add (heven step hmem) (hcharge step hmem) hinc, hinc]
    omega
  · have hrank : (fun site => scale * grade site + remainder site) = rank := by
      funext site
      dsimp only [remainder, obstacle]
      omega
    rw [hrank]
    intro site
    have hvalue : 1 + bellmanInputs field rank site ≤ rank site := by
      change 1 + bellmanInputs field rank site ≤ bellmanValue field obstacle n site
      rw [← hn]
      exact le_max_right ..
    rcases hbinary site with hb | hw
    · left
      simp only [bellmanInputs, if_pos hb] at hvalue
      exact ⟨hb, by have := le_max_left (rank (incomingNeg site)) (rank (incomingPos site)); omega,
        by have := le_max_right (rank (incomingNeg site)) (rank (incomingPos site)); omega⟩
    · right
      simp only [bellmanInputs, show laplacian field site ≠ -1 by omega, if_false] at hvalue
      refine ⟨hw, ?_⟩
      by_cases hle : rank (incomingNeg site) ≤ rank (incomingPos site)
      · rw [min_eq_left hle] at hvalue
        exact Or.inl (by omega)
      · rw [min_eq_right (le_of_not_ge hle)] at hvalue
        exact Or.inr (by omega)

end FLatticePaper
