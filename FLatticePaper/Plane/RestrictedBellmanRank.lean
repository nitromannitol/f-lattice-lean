import FLatticePaper.Plane.BellmanRank
import FLatticePaper.Plane.Induction.RankFromForts
import FLatticePaper.Plane.Induction.StarFromSheets

/-! The restricted Bellman rank (task 20): the construction of `BellmanRank` with the inputs restricted to the
permitted ones. A restricted fort blocks a site through a non-permitted or blocked input (`IsRestrictedFort`). With
the absence of restricted forts in every grade half-space, the restricted value iteration gives a constrained burning
rank for the permits. The original theorems are untouched. -/

namespace FLatticePaper

open Farey

/-- A restricted exit: as `EscapesWithin`, but a site of charge `-1` escapes only through both inputs when both are
permitted, and a site of charge `0` through one permitted input. -/
def RestrictedEscapesWithin (field grade : Field) (permits : Site → Site → Prop) (level : ℤ) :
    ℕ → Site → Prop
  | 0, site => grade site < level
  | n + 1, site => grade site < level ∨
      (laplacian field site = -1 ∧ permits site (incomingNeg site) ∧ permits site (incomingPos site) ∧
        RestrictedEscapesWithin field grade permits level n (incomingNeg site) ∧
        RestrictedEscapesWithin field grade permits level n (incomingPos site)) ∨
      (laplacian field site = 0 ∧
        ((permits site (incomingNeg site) ∧ RestrictedEscapesWithin field grade permits level n (incomingNeg site)) ∨
          (permits site (incomingPos site) ∧ RestrictedEscapesWithin field grade permits level n (incomingPos site))))

theorem restrictedEscapesWithin_succ {field grade : Field} {permits : Site → Site → Prop} {level : ℤ} (n : ℕ)
    (site : Site) (h : RestrictedEscapesWithin field grade permits level n site) :
    RestrictedEscapesWithin field grade permits level (n + 1) site := by
  induction n generalizing site with
  | zero => exact Or.inl h
  | succ n ih =>
    rcases h with h | ⟨hl, hpn, hpp, hn, hp⟩ | ⟨hl, ⟨hpn, hn⟩ | ⟨hpp, hp⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hl, hpn, hpp, ih _ hn, ih _ hp⟩)
    · exact Or.inr (Or.inr ⟨hl, Or.inl ⟨hpn, ih _ hn⟩⟩)
    · exact Or.inr (Or.inr ⟨hl, Or.inr ⟨hpp, ih _ hp⟩⟩)

theorem restrictedEscapesWithin_mono {field grade : Field} {permits : Site → Site → Prop} {level : ℤ}
    {site : Site} {n m : ℕ} (hnm : n ≤ m) (h : RestrictedEscapesWithin field grade permits level n site) :
    RestrictedEscapesWithin field grade permits level m site := by
  have hmono : Monotone fun k => RestrictedEscapesWithin field grade permits level k site :=
    monotone_nat_of_le_succ (fun k => restrictedEscapesWithin_succ k site)
  exact hmono hnm h

/-- Without a nonempty restricted fort in any grade half-space, every site has a finite restricted exit. -/
theorem exists_restrictedEscapeDepth {field grade : Field} {permits : Site → Site → Prop} {level : ℤ}
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hno : ∀ sites : Set Site, sites.Nonempty → IsRestrictedFort field permits sites →
      (∀ site ∈ sites, level ≤ grade site) → False) (site : Site) :
    ∃ n, RestrictedEscapesWithin field grade permits level n site := by
  classical
  by_contra! hsite
  let remaining : Set Site := {site | ∀ n, ¬ RestrictedEscapesWithin field grade permits level n site}
  have hesc {point : Site} (hout : point ∉ remaining) :
      ∃ n, RestrictedEscapesWithin field grade permits level n point := by
    simpa only [remaining, Set.mem_setOf_eq, not_forall, not_not] using hout
  apply hno remaining ⟨site, hsite⟩ ?_ (fun point hp => le_of_not_gt (hp 0))
  intro point hp
  rcases hbinary point with hl | hl
  · left
    refine ⟨hl, ?_⟩
    by_contra! hout
    obtain ⟨⟨hnR, hpn⟩, ⟨hpR, hpp⟩⟩ := hout
    obtain ⟨n, hn⟩ := hesc hnR
    obtain ⟨m, hm⟩ := hesc hpR
    exact hp (max n m + 1) (Or.inr (Or.inl ⟨hl, hpn, hpp,
      restrictedEscapesWithin_mono (le_max_left n m) hn, restrictedEscapesWithin_mono (le_max_right n m) hm⟩))
  · right
    refine ⟨hl, ?_, ?_⟩
    · by_contra! hout
      obtain ⟨hnR, hpn⟩ := hout
      obtain ⟨n, hn⟩ := hesc hnR
      exact hp (n + 1) (Or.inr (Or.inr ⟨hl, Or.inl ⟨hpn, hn⟩⟩))
    · by_contra! hout
      obtain ⟨hpR, hpp⟩ := hout
      obtain ⟨n, hn⟩ := hesc hpR
      exact hp (n + 1) (Or.inr (Or.inr ⟨hl, Or.inr ⟨hpp, hn⟩⟩))

theorem restrictedEscapesWithin_add_iff {field grade : Field} {permits : Site → Site → Prop} {step : Site}
    {increment : ℤ} (heven : EvenSite step) (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ site, grade (site + step) = grade site + increment)
    (hperm : ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (level : ℤ) (n : ℕ) (site : Site) :
    RestrictedEscapesWithin field grade permits (level + increment) n (site + step) ↔
      RestrictedEscapesWithin field grade permits level n site := by
  induction n generalizing site with
  | zero => simp only [RestrictedEscapesWithin, hgrade, add_lt_add_iff_right]
  | succ n ih =>
    simp only [RestrictedEscapesWithin, hcharge, hgrade, add_lt_add_iff_right,
      incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven, hperm, ih]

/-- A cover by finitely many representatives makes the restricted exit depths uniform. -/
theorem exists_uniformRestrictedEscapeDepth {field grade : Field} {permits : Site → Site → Prop}
    {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hdepth : ∀ site, ∃ n, RestrictedEscapesWithin field grade permits (grade site) n site) :
    ∃ horizon : ℕ, 0 < horizon ∧ ∀ site, RestrictedEscapesWithin field grade permits (grade site) horizon site := by
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
  have hescape := restrictedEscapesWithin_mono hle (hdepth representative)
  have h := (restrictedEscapesWithin_add_iff (heven step hstep) (hcharge step hstep) hinc
    (hperm step hstep) (grade representative) horizon representative).mpr hescape
  rw [← hinc, hreconstruct] at h
  exact h


open Classical in
/-- The restricted continuation value: at charge `-1` the larger of the two inputs; at charge `0` the smaller of the
permitted inputs (with `PermitLocal`, at least one input is permitted). -/
noncomputable def restrictedInputs (field : Field) (permits : Site → Site → Prop) (value : Field) (site : Site) : ℤ :=
  if laplacian field site = -1 then max (value (incomingNeg site)) (value (incomingPos site))
  else if permits site (incomingNeg site) ∧ permits site (incomingPos site) then
    min (value (incomingNeg site)) (value (incomingPos site))
  else if permits site (incomingNeg site) then value (incomingNeg site)
  else value (incomingPos site)

theorem restrictedInputs_mono {field : Field} {permits : Site → Site → Prop} {value value' : Field}
    (h : ∀ site, value site ≤ value' site) (site : Site) :
    restrictedInputs field permits value site ≤ restrictedInputs field permits value' site := by
  have hn := h (incomingNeg site)
  have hp := h (incomingPos site)
  unfold restrictedInputs
  split_ifs
  · exact max_le_max hn hp
  · exact min_le_min hn hp
  · exact hn
  · exact hp

theorem restrictedInputs_le_neg {field : Field} {permits : Site → Site → Prop} {value : Field} {site : Site}
    (hl : laplacian field site ≠ -1) (hp : permits site (incomingNeg site)) :
    restrictedInputs field permits value site ≤ value (incomingNeg site) := by
  unfold restrictedInputs
  rw [if_neg hl]
  split_ifs with h1
  · exact min_le_left _ _
  · exact le_rfl

theorem restrictedInputs_le_pos {field : Field} {permits : Site → Site → Prop} {value : Field} {site : Site}
    (hl : laplacian field site ≠ -1) (hp : permits site (incomingPos site)) :
    restrictedInputs field permits value site ≤ value (incomingPos site) := by
  unfold restrictedInputs
  rw [if_neg hl]
  split_ifs with h1 h2
  · exact min_le_right _ _
  · exact absurd hp (fun hpp => h1 ⟨h2, hpp⟩)
  · exact le_rfl

/-- At a site of charge `0` with a permitted input, the continuation value is the value of a permitted input. -/
theorem restrictedInputs_eq_permitted {field : Field} {permits : Site → Site → Prop} {value : Field} {site : Site}
    (hl : laplacian field site ≠ -1) (hperm : permits site (incomingNeg site) ∨ permits site (incomingPos site)) :
    (permits site (incomingNeg site) ∧ restrictedInputs field permits value site = value (incomingNeg site)) ∨
      (permits site (incomingPos site) ∧ restrictedInputs field permits value site = value (incomingPos site)) := by
  unfold restrictedInputs
  rw [if_neg hl]
  split_ifs with h1 h2
  · rcases le_total (value (incomingNeg site)) (value (incomingPos site)) with h | h
    · exact Or.inl ⟨h1.1, min_eq_left h⟩
    · exact Or.inr ⟨h1.2, min_eq_right h⟩
  · exact Or.inl ⟨h2, rfl⟩
  · exact Or.inr ⟨hperm.resolve_left h2, rfl⟩

theorem restrictedInputs_of_charge_neg_one {field : Field} {permits : Site → Site → Prop} {value : Field}
    {site : Site} (hl : laplacian field site = -1) :
    restrictedInputs field permits value site = max (value (incomingNeg site)) (value (incomingPos site)) := by
  unfold restrictedInputs
  rw [if_pos hl]

theorem restrictedInputs_add {field : Field} {permits : Site → Site → Prop} {value : Field} {step : Site}
    {increment : ℤ} (heven : EvenSite step)
    (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hperm : ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hvalue : ∀ site, value (site + step) = value site + increment) (site : Site) :
    restrictedInputs field permits value (site + step) = restrictedInputs field permits value site + increment := by
  have hn : permits (site + step) (incomingNeg (site + step)) ↔ permits site (incomingNeg site) := by
    rw [incomingNeg_add_of_even site step heven]
    exact hperm site _
  have hp : permits (site + step) (incomingPos (site + step)) ↔ permits site (incomingPos site) := by
    rw [incomingPos_add_of_even site step heven]
    exact hperm site _
  unfold restrictedInputs
  by_cases hl : laplacian field site = -1
  · rw [if_pos (by rw [hcharge]; exact hl), if_pos hl, incomingNeg_add_of_even site step heven,
      incomingPos_add_of_even site step heven, hvalue, hvalue]
    exact max_add_add_right _ _ _
  · rw [if_neg (by rw [hcharge]; exact hl), if_neg hl]
    by_cases h1 : permits site (incomingNeg site) ∧ permits site (incomingPos site)
    · rw [if_pos (And.intro (hn.mpr h1.1) (hp.mpr h1.2)), if_pos h1, incomingNeg_add_of_even site step heven,
        incomingPos_add_of_even site step heven, hvalue, hvalue]
      exact min_add_add_right _ _ _
    · rw [if_neg (fun h => h1 ⟨hn.mp h.1, hp.mp h.2⟩), if_neg h1]
      by_cases h2 : permits site (incomingNeg site)
      · rw [if_pos (hn.mpr h2), if_pos h2, incomingNeg_add_of_even site step heven, hvalue]
      · rw [if_neg (fun h => h2 (hn.mp h)), if_neg h2, incomingPos_add_of_even site step heven, hvalue]



/-- The restricted value iteration from the obstacle: each continuation earns one. -/
noncomputable def restrictedBellmanValue (field : Field) (permits : Site → Site → Prop) (obstacle : Field) :
    ℕ → Field
  | 0 => obstacle
  | n + 1 => fun site =>
      max (obstacle site) (1 + restrictedInputs field permits (restrictedBellmanValue field permits obstacle n) site)

theorem restrictedValue_le_succ (field : Field) (permits : Site → Site → Prop) (obstacle : Field) (n : ℕ)
    (site : Site) :
    restrictedBellmanValue field permits obstacle n site ≤
      restrictedBellmanValue field permits obstacle (n + 1) site := by
  induction n generalizing site with
  | zero => exact le_max_left _ _
  | succ n ih =>
    show max (obstacle site) (1 + restrictedInputs field permits (restrictedBellmanValue field permits obstacle n) site) ≤
      max (obstacle site) (1 + restrictedInputs field permits (restrictedBellmanValue field permits obstacle (n + 1)) site)
    exact max_le_max le_rfl (add_le_add_right (restrictedInputs_mono ih site) 1)

theorem obstacle_le_restrictedValue (field : Field) (permits : Site → Site → Prop) (obstacle : Field) (n : ℕ)
    (site : Site) : obstacle site ≤ restrictedBellmanValue field permits obstacle n site := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left ..

theorem restrictedValue_mono (field : Field) (permits : Site → Site → Prop) (obstacle : Field) (site : Site) :
    Monotone fun n => restrictedBellmanValue field permits obstacle n site :=
  monotone_nat_of_le_succ fun n => restrictedValue_le_succ field permits obstacle n site

theorem restrictedValue_add {field : Field} {permits : Site → Site → Prop} {obstacle : Field} {step : Site}
    {increment : ℤ} (heven : EvenSite step)
    (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hperm : ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hobstacle : ∀ site, obstacle (site + step) = obstacle site + increment) (n : ℕ) (site : Site) :
    restrictedBellmanValue field permits obstacle n (site + step) =
      restrictedBellmanValue field permits obstacle n site + increment := by
  induction n generalizing site with
  | zero => exact hobstacle site
  | succ n ih =>
    show max (obstacle (site + step)) (1 + restrictedInputs field permits
        (restrictedBellmanValue field permits obstacle n) (site + step)) =
      max (obstacle site) (1 + restrictedInputs field permits (restrictedBellmanValue field permits obstacle n) site)
        + increment
    rw [hobstacle site, restrictedInputs_add heven hcharge hperm ih site]
    have e : 1 + (restrictedInputs field permits (restrictedBellmanValue field permits obstacle n) site + increment) =
        1 + restrictedInputs field permits (restrictedBellmanValue field permits obstacle n) site + increment := by
      ring
    rw [e]
    exact max_add_add_right _ _ _

/-- Uniform restricted exits bound the restricted payoff, even when the game stops partway through an exit segment. -/
theorem restrictedValue_le_of_uniform_escape {field grade : Field} {permits : Site → Site → Prop} {horizon : ℕ}
    {bound : ℤ}
    (hjump : ∀ site, grade (incomingNeg site) ≤ grade site + bound ∧
      grade (incomingPos site) ≤ grade site + bound)
    (hbound : 0 ≤ bound)
    (hescape : ∀ site, RestrictedEscapesWithin field grade permits (grade site) horizon site)
    (n : ℕ) (site : Site) :
    restrictedBellmanValue field permits (fun point => (horizon : ℤ) * grade point) n site ≤
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
      (hexit : RestrictedEscapesWithin field grade permits level left point) :
      restrictedBellmanValue field permits obstacle n point ≤ scale * level + budget - (used : ℤ) := by
    induction n generalizing point level used left with
    | zero => exact hstop point level used (by omega) hupper
    | succ n ih =>
      match left, hexit, htime with
      | 0, hexit, _ => exact (not_lt_of_ge hlower hexit).elim
      | left + 1, hexit, htime =>
        have hnext (input : Site) (hup : grade input ≤ grade point + bound)
            (hin : RestrictedEscapesWithin field grade permits level left input) :
            restrictedBellmanValue field permits obstacle n input ≤
              scale * level + budget - ((used + 1 : ℕ) : ℤ) := by
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
        rcases hexit with hbelow | ⟨hblack, hpn, hpp, hn, hp⟩ | ⟨hwhite, ⟨hpn, hn⟩ | ⟨hpp, hp⟩⟩
        · exact (not_lt_of_ge hlower hbelow).elim
        · have hvalue := max_le (hnext _ (hjump point).1 hn) (hnext _ (hjump point).2 hp)
          rw [restrictedInputs_of_charge_neg_one hblack]
          omega
        · have hvalue := (restrictedInputs_le_neg (by rw [hwhite]; norm_num) hpn).trans
            (hnext _ (hjump point).1 hn)
          omega
        · have hvalue := (restrictedInputs_le_pos (by rw [hwhite]; norm_num) hpp).trans
            (hnext _ (hjump point).2 hp)
          omega
  simpa only [obstacle, budget, scale, Nat.cast_zero, sub_zero] using
    hlocal n site (grade site) 0 horizon (by omega) le_rfl (by simp) (hescape site)



/-- The restricted value iteration stabilises simultaneously on a finite deck. -/
theorem exists_restrictedValue_fixed {field : Field} {obstacle : Field} {permits : Site → Site → Prop}
    {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hshift : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, obstacle (site + step) = obstacle site + increment)
    (budget : ℤ) (hupper : ∀ n site, restrictedBellmanValue field permits obstacle n site ≤ obstacle site + budget) :
    ∃ n, restrictedBellmanValue field permits obstacle (n + 1) = restrictedBellmanValue field permits obstacle n := by
  classical
  have hmaximum (site : Site) : ∃ n, ∀ m,
      restrictedBellmanValue field permits obstacle m site ≤ restrictedBellmanValue field permits obstacle n site := by
    let values := (Finset.Icc (obstacle site) (obstacle site + budget)).filter
      (fun value => ∃ n, restrictedBellmanValue field permits obstacle n site = value)
    have hmem (m : ℕ) : restrictedBellmanValue field permits obstacle m site ∈ values :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨obstacle_le_restrictedValue field permits obstacle m site,
        hupper m site⟩, m, rfl⟩
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
  have heq : restrictedBellmanValue field permits obstacle (n + 1) representative =
      restrictedBellmanValue field permits obstacle n representative :=
    le_antisymm ((hdepth representative _).trans (restrictedValue_mono field permits obstacle representative hle))
      (restrictedValue_mono field permits obstacle representative (by omega))
  rw [← hreconstruct, restrictedValue_add (heven step hstep) (hcharge step hstep) (hperm step hstep) hinc,
    restrictedValue_add (heven step hstep) (hcharge step hstep) (hperm step hstep) hinc, heq]

/-- With no restricted fort in any grade half-space, and the local permits of `PermitLocal`, the restricted Bellman
rank is a constrained burning rank for the permits. -/
theorem exists_constrainedBurningRank_of_restrictedNoFort {field grade : Field}
    {permits : Site → Site → Prop} {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hlocal : PermitLocal field permits)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hno : RestrictedNoFort field grade permits) :
    ∃ (scale : ℤ) (remainder : Field) (budget : ℤ), 0 < scale ∧
      (∀ site, 0 ≤ remainder site ∧ remainder site ≤ budget) ∧
      (∀ step ∈ deck.span, ∀ site, remainder (site + step) = remainder site) ∧
      IsConstrainedBurningRank field (fun site => scale * grade site + remainder site) permits := by
  obtain ⟨horizon, hpos, hescape⟩ := exists_uniformRestrictedEscapeDepth hcover heven hcharge hgrade hperm
    (fun site => exists_restrictedEscapeDepth hbinary (hno (grade site)) site)
  obtain ⟨bound, hbound, hjump⟩ := exists_incomingGradeJumpBound hcover heven hgrade
  let scale : ℤ := horizon
  let obstacle : Field := fun site => scale * grade site
  let budget := scale + scale ^ 2 * bound
  have hupper (n : ℕ) (site : Site) :
      restrictedBellmanValue field permits obstacle n site ≤ obstacle site + budget :=
    restrictedValue_le_of_uniform_escape hjump hbound hescape n site
  have hshift (step : Site) (hmem : step ∈ deck.span) :
      ∃ increment : ℤ, ∀ site, obstacle (site + step) = obstacle site + increment := by
    obtain ⟨increment, hinc⟩ := hgrade step hmem
    exact ⟨scale * increment, fun site => by simp only [obstacle, hinc, mul_add]⟩
  obtain ⟨n, hn⟩ := exists_restrictedValue_fixed hcover heven hcharge hperm hshift budget hupper
  let rank := restrictedBellmanValue field permits obstacle n
  let remainder : Field := fun site => rank site - obstacle site
  refine ⟨scale, remainder, budget, by simpa [scale] using (Int.ofNat_lt.mpr hpos), ?_, ?_, ?_⟩
  · intro site
    have hlo := obstacle_le_restrictedValue field permits obstacle n site
    have hhi := hupper n site
    dsimp only [remainder, rank]
    omega
  · intro step hmem site
    obtain ⟨increment, hinc⟩ := hshift step hmem
    simp only [remainder, rank, restrictedValue_add (heven step hmem) (hcharge step hmem) (hperm step hmem) hinc,
      hinc]
    omega
  · have hrank : (fun site => scale * grade site + remainder site) = rank := by
      funext site
      dsimp only [remainder, obstacle]
      omega
    rw [hrank]
    intro site
    have hvalue : 1 + restrictedInputs field permits rank site ≤ rank site := by
      change 1 + restrictedInputs field permits rank site ≤
        restrictedBellmanValue field permits obstacle n site
      rw [← hn]
      exact le_max_right _ _
    dsimp only
    rcases hbinary site with hb | hw
    · rw [restrictedInputs_of_charge_neg_one hb] at hvalue
      have hn' := le_max_left (rank (incomingNeg site)) (rank (incomingPos site))
      have hp' := le_max_right (rank (incomingNeg site)) (rank (incomingPos site))
      exact Or.inl ⟨hb, ⟨(hlocal.1 site hb).1, by omega⟩, ⟨(hlocal.1 site hb).2, by omega⟩⟩
    · have hl : laplacian field site ≠ -1 := by rw [hw]; norm_num
      rcases restrictedInputs_eq_permitted hl (hlocal.2 site hw) with ⟨hpn, heq⟩ | ⟨hpp, heq⟩
      · rw [heq] at hvalue
        exact Or.inr ⟨hw, Or.inl ⟨hpn, by omega⟩⟩
      · rw [heq] at hvalue
        exact Or.inr ⟨hw, Or.inr ⟨hpp, by omega⟩⟩



section SewnStandard

open Induction

/-- The shift of the difference `D = F − F(· + σ)` along an integer combination of the deck vectors `K` and `V`. -/
theorem starDiff_add_deck {F : Field} {K V σ : Site} {cU cV : ℤ} {g : Site → ℤ}
    (hK : ∀ z, F (z + K) = F z + cU) (hV : ∀ z, F (z + V) = F z - g z + cV)
    (hgσ : ∀ z, g (z + σ) = g z + g σ) (hgσ2 : g σ = 2) (i j : ℤ) (z : Site) :
    starDiff F σ (z + (i • K + j • V)) = starDiff F σ z + 2 * j := by
  rw [show z + (i • K + j • V) = (z + i • K) + j • V by abel,
    starDiff_add_zsmul_transverse hV hgσ j (z + i • K), starDiff_add_zsmul_kernel hK i z, hgσ2]
  ring

/-- The slip permits are invariant under the deck: the difference `D` shifts by the same amount at both sites. -/
theorem slipPermits_add_deck {F : Field} {K V σ : Site} {cU cV : ℤ} {g : Site → ℤ}
    (hK : ∀ z, F (z + K) = F z + cU) (hV : ∀ z, F (z + V) = F z - g z + cV)
    (hgσ : ∀ z, g (z + σ) = g z + g σ) (hgσ2 : g σ = 2) (i j : ℤ) (site input : Site) :
    slipPermits F (fun z => F (z + σ)) (site + (i • K + j • V)) (input + (i • K + j • V)) ↔
      slipPermits F (fun z => F (z + σ)) site input := by
  unfold slipPermits
  rw [slip_eq_starDiff, slip_eq_starDiff, starDiff_add_deck hK hV hgσ hgσ2 i j input,
    starDiff_add_deck hK hV hgσ hgσ2 i j site]
  constructor <;> intro h <;> linarith

/-- S3 for a child frame: with the generator periods, the binary Laplacian, the local permits and the absence of
restricted forts in the `t`-grade half-spaces, the sewn field has a constrained burning rank for the slip permits. -/
theorem S3_of_restrictedNoFort (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hlocal : PermitLocal F (slipPermits F (fun z => F (z + frame.shortShift))))
    (hno : RestrictedNoFort F frame.tGrade (slipPermits F (fun z => F (z + frame.shortShift)))) :
    ∃ rank : Site → ℤ, IsConstrainedBurningRank F rank (slipPermits F (fun z => F (z + frame.shortShift))) := by
  have hKspan : frame.child.modifiedDeck.kernel ∈ frame.child.modifiedDeck.span :=
    ⟨1, 0, by simp [PeriodDeck.combine]⟩
  have hVspan : frame.child.modifiedDeck.transverse ∈ frame.child.modifiedDeck.span :=
    ⟨0, 1, by simp [PeriodDeck.combine]⟩
  have hKe : EvenSite frame.child.modifiedDeck.kernel :=
    ((frame.child.mem_modifiedDeck_iff _).mp hKspan).2
  have hVe : EvenSite frame.child.modifiedDeck.transverse :=
    ((frame.child.mem_modifiedDeck_iff _).mp hVspan).2
  have hpos : 0 < frame.child.modifiedDeck.det :=
    Fraction.det_modifiedDeck_pos (frame.valid.current_interior .even).inUnitInterval
  have hcover : frame.child.modifiedDeck.Covers frame.child.modifiedDeck.residueSquare :=
    (PeriodDeck.covers_iff_square_codes_subset _ hpos _).mpr subset_rfl
  have heven : ∀ step ∈ frame.child.modifiedDeck.span, EvenSite step := by
    rintro step ⟨i, j, rfl⟩
    rw [combine_eq_smul]
    exact evenSite_smul_add _ _ hKe hVe i j
  have hcharge : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site,
      laplacian F (site + step) = laplacian F site := by
    rintro step ⟨i, j, rfl⟩ site
    exact laplacian_add_combine hper site i j
  have hgrade : ∀ step ∈ frame.child.modifiedDeck.span, ∃ increment : ℤ,
      ∀ site, frame.tGrade (site + step) = frame.tGrade site + increment := by
    rintro step ⟨i, j, rfl⟩
    exact ⟨-(j * frame.child.periodDenominator), fun site => by rw [frame.tGrade_add_combine]; ring⟩
  have hgσ : ∀ z, frame.child.transverseGrade (z + frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade frame.shortShift := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hgσ2 : frame.child.transverseGrade frame.shortShift = 2 := by
    rw [frame.transverseGrade_child, frame.tGrade_shortShift]
    norm_num
  have hperm : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site input,
      slipPermits F (fun z => F (z + frame.shortShift)) (site + step) (input + step) ↔
        slipPermits F (fun z => F (z + frame.shortShift)) site input := by
    rintro step ⟨i, j, rfl⟩ site input
    rw [combine_eq_smul]
    exact slipPermits_add_deck hper.1 hper.2 hgσ hgσ2 i j site input
  obtain ⟨scale, remainder, budget, -, -, -, hrank⟩ :=
    exists_constrainedBurningRank_of_restrictedNoFort hcover heven hcharge hgrade hperm hlocal hbin hno
  exact ⟨_, hrank⟩

/-- S3 for the sewn standard field of a word, from its packet and the absence of restricted forts. -/
theorem S3_of_packet_restrictedNoFort (word : Word) (hpk : (frameAt word).Packet (standardField word))
    (hlocal : PermitLocal (standardField word)
      (slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift))))
    (hno : RestrictedNoFort (standardField word) (frameAt word).tGrade
      (slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)))) :
    ∃ rank : Site → ℤ, IsConstrainedBurningRank (standardField word) rank
      (slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift))) :=
  S3_of_restrictedNoFort (frameAt word) hpk.periods hpk.binary hlocal hno

end SewnStandard

end FLatticePaper
