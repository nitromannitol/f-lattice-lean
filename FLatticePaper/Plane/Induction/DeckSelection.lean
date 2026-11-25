import FLatticePaper.Plane.Induction.VWindow
import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.SignedPolicy
import FLatticePaper.Plane.PeriodCocycle

/-! Task w3, hgames step 2: the policy given a deck-periodic rank is deck equivariant.

For a field `F` with generator periods `(U, V) = (kernel, transverse)` and a rank `R` with deck characters, the selection at a white
centre is the lower of its two inputs (ties to the negative input), and the policy keeps both inputs at black centres and the
selection at white centres. Translation by a span element `s = iU + jV` (even, and with `F(·+s) − F` affine) preserves the policy:
the Laplacian is invariant, the inputs translate, and the comparison of the two inputs is preserved since both shift by the same
character. This gives the deck equivariance `hdeck`/`hdeckOpp` of `chain_nonincreasing_of_W1` as a proved property. -/

namespace FLatticePaper.DeckSelection

open Farey FLatticePaper FLatticePaper.Induction

variable (frame : ChildFrame)

theorem combine_eq (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse := by
  ext <;> simp [PeriodDeck.combine]

/-- An affine function on the sites. -/
def AffineS (g : Site → ℤ) : Prop := ∃ α β γ : ℤ, ∀ x : Site, g x = α * x.1 + β * x.2 + γ

theorem affineS_add {g h : Site → ℤ} (hg : AffineS g) (hh : AffineS h) : AffineS (fun x => g x + h x) := by
  obtain ⟨α, β, γ, hg⟩ := hg
  obtain ⟨α', β', γ', hh⟩ := hh
  exact ⟨α + α', β + β', γ + γ', fun x => by dsimp only; rw [hg x, hh x]; ring⟩

theorem affineS_shift {g : Site → ℤ} (hg : AffineS g) (s : Site) : AffineS (fun x => g (x + s)) := by
  obtain ⟨α, β, γ, hg⟩ := hg
  exact ⟨α, β, γ + α * s.1 + β * s.2, fun x => by dsimp only; rw [hg (x + s)]; simp only [Prod.fst_add, Prod.snd_add]; ring⟩

theorem affineS_const (c : ℤ) : AffineS (fun _ => c) := ⟨0, 0, c, fun x => by simp⟩

theorem affineS_neg {g : Site → ℤ} (hg : AffineS g) : AffineS (fun x => -g x) := by
  obtain ⟨α, β, γ, hg⟩ := hg
  exact ⟨-α, -β, -γ, fun x => by dsimp only; rw [hg x]; ring⟩

theorem affineS_tg : AffineS (fun x => frame.child.transverseGrade x) :=
  ⟨-frame.child.num, frame.child.den, 0, fun x => by unfold Fraction.transverseGrade; ring⟩

/-- The two inputs of a centre (the lower and upper neighbour in the physical graph). -/
theorem incomingNeg_add_incomingPos (z : Site) : incomingNeg z + incomingPos z = z + z := by
  unfold incomingNeg incomingPos
  split_ifs
  all_goals
    ext
    all_goals (try simp)

/-- Translation by an even site preserves the parity of a centre. -/
theorem evenSite_add_of_even {s : Site} (hs : EvenSite s) (z : Site) : EvenSite (z + s) ↔ EvenSite z := by
  unfold EvenSite at hs ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem incomingNeg_add_even {s : Site} (hs : EvenSite s) (z : Site) :
    incomingNeg (z + s) = incomingNeg z + s := by
  unfold incomingNeg
  by_cases h : EvenSite z
  · have h' : EvenSite (z + s) := (evenSite_add_of_even hs z).mpr h
    rw [if_pos h, if_pos h']
    ext
    all_goals (try simp)
    all_goals (try ring)
  · have h' : ¬ EvenSite (z + s) := fun e => h ((evenSite_add_of_even hs z).mp e)
    rw [if_neg h, if_neg h']
    ext
    all_goals (try simp)
    all_goals (try ring)

theorem incomingPos_add_even {s : Site} (hs : EvenSite s) (z : Site) :
    incomingPos (z + s) = incomingPos z + s := by
  unfold incomingPos
  by_cases h : EvenSite z
  · have h' : EvenSite (z + s) := (evenSite_add_of_even hs z).mpr h
    rw [if_pos h, if_pos h']
    ext
    all_goals (try simp)
    all_goals (try ring)
  · have h' : ¬ EvenSite (z + s) := fun e => h ((evenSite_add_of_even hs z).mp e)
    rw [if_neg h, if_neg h']
    ext
    all_goals (try simp)
    all_goals (try ring)

/-- Translation by a span element preserves the parity of a site. -/
theorem evenSite_add_span (i j : ℤ) (z : Site) :
    EvenSite (z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) ↔ EvenSite z := by
  have e : z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) =
      (z + j • frame.child.modifiedDeck.transverse) + i • frame.child.modifiedDeck.kernel := by abel
  rw [e, frame.evenSite_add_smul_kernel, EndpointDeck.transverse_eq_Vdeck, VWindow.evenSite_add_Vdeck]

theorem evenSite_span (i j : ℤ) :
    EvenSite (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) := by
  have h := evenSite_add_span frame i j 0
  rw [zero_add] at h
  exact h.mpr (by unfold EvenSite; norm_num)

section periods

variable {F : Field} {cU cV : ℤ}

theorem F_kernel_add (hF : HasGeneratorPeriods frame.child F cU cV) (i : ℤ) :
    ∀ x : Site, F (x + i • frame.child.modifiedDeck.kernel) = F x + i * cU := by
  induction i using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have e : x + ((k : ℤ) + 1) • frame.child.modifiedDeck.kernel =
        (x + (k : ℤ) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.kernel := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, hF.1, ih x]
    ring
  | pred k ih =>
    intro x
    have h1 := hF.1 (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    have e2 : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.kernel =
        x + (-(k : ℤ)) • frame.child.modifiedDeck.kernel := by
      rw [sub_smul, one_smul]
      abel
    rw [e2, ih x] at h1
    linear_combination (-1 : ℤ) * h1

theorem F_transverse_affine (hF : HasGeneratorPeriods frame.child F cU cV) (j : ℤ) :
    AffineS (fun x => F (x + j • frame.child.modifiedDeck.transverse) - F x) := by
  induction j using Int.induction_on with
  | zero => exact ⟨0, 0, 0, fun x => by simp⟩
  | succ k ih =>
    have e : ∀ x : Site, F (x + ((k : ℤ) + 1) • frame.child.modifiedDeck.transverse) - F x =
        (F (x + (k : ℤ) • frame.child.modifiedDeck.transverse) - F x) +
          (-(frame.child.transverseGrade (x + (k : ℤ) • frame.child.modifiedDeck.transverse)) + cV) := by
      intro x
      have e' : x + ((k : ℤ) + 1) • frame.child.modifiedDeck.transverse =
          (x + (k : ℤ) • frame.child.modifiedDeck.transverse) + frame.child.modifiedDeck.transverse := by
        rw [add_smul, one_smul, add_assoc]
      rw [e', hF.2 _]
      ring
    have hfun : (fun x => F (x + ((k : ℤ) + 1) • frame.child.modifiedDeck.transverse) - F x) =
        fun x => (F (x + (k : ℤ) • frame.child.modifiedDeck.transverse) - F x) +
          (-(frame.child.transverseGrade (x + (k : ℤ) • frame.child.modifiedDeck.transverse)) + cV) :=
      funext e
    rw [hfun]
    exact affineS_add ih (affineS_add (affineS_neg (affineS_shift (affineS_tg frame) _)) (affineS_const cV))
  | pred k ih =>
    have e : ∀ x : Site, F (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse) - F x =
        (F (x + (-(k : ℤ)) • frame.child.modifiedDeck.transverse) - F x) +
          (frame.child.transverseGrade (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse) + -cV) := by
      intro x
      have e' : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse + frame.child.modifiedDeck.transverse =
          x + (-(k : ℤ)) • frame.child.modifiedDeck.transverse := by
        rw [sub_smul, one_smul]
        abel
      have h := hF.2 (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse)
      rw [e'] at h
      linarith
    have hfun : (fun x => F (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse) - F x) =
        fun x => (F (x + (-(k : ℤ)) • frame.child.modifiedDeck.transverse) - F x) +
          (frame.child.transverseGrade (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse) + -cV) :=
      funext e
    rw [hfun]
    exact affineS_add ih (affineS_add (affineS_shift (affineS_tg frame) _) (affineS_const (-cV)))

/-- `F(·+s) − F` is affine for a span element `s = iU + jV`. -/
theorem F_span_affine (hF : HasGeneratorPeriods frame.child F cU cV) (i j : ℤ) :
    AffineS (fun x => F (x + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) - F x) := by
  have e : ∀ x : Site, F (x + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) - F x =
      (F ((x + i • frame.child.modifiedDeck.kernel) + j • frame.child.modifiedDeck.transverse) -
          F (x + i • frame.child.modifiedDeck.kernel)) + (i : ℤ) * cU := by
    intro x
    rw [← add_assoc, F_kernel_add frame hF i x]
    ring
  rw [funext e]
  exact affineS_add (affineS_shift (F_transverse_affine frame hF j) (i • frame.child.modifiedDeck.kernel))
    (affineS_const ((i : ℤ) * cU))

/-- **The Laplacian is invariant under the span.** -/
theorem laplacian_add_span (hF : HasGeneratorPeriods frame.child F cU cV) (i j : ℤ) (z : Site) :
    laplacian F (z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) =
      laplacian F z := by
  have hs := evenSite_span frame i j
  obtain ⟨α, β, γ, hg⟩ := F_span_affine frame hF i j
  have hsum := incomingNeg_add_incomingPos z
  have hx : (incomingNeg z).1 + (incomingPos z).1 = 2 * z.1 := by
    have := congrArg Prod.fst hsum
    simp at this
    linarith
  have hy : (incomingNeg z).2 + (incomingPos z).2 = 2 * z.2 := by
    have := congrArg Prod.snd hsum
    simp at this
    linarith
  have h1 := hg (incomingNeg z)
  have h2 := hg (incomingPos z)
  have h3 := hg z
  unfold laplacian
  rw [incomingNeg_add_even hs z, incomingPos_add_even hs z]
  linear_combination h1 + h2 - 2 * h3 + α * hx + β * hy

end periods

/-- A rank with the deck characters `(cU, cV)` shifts by the character of every span element. -/
theorem char_kernel {G : Site → ℤ} {cU : ℤ} (hG : ∀ z, G (z + frame.child.modifiedDeck.kernel) = G z + cU) (i : ℤ) :
    ∀ x : Site, G (x + i • frame.child.modifiedDeck.kernel) = G x + i * cU := by
  induction i using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have e : x + ((k : ℤ) + 1) • frame.child.modifiedDeck.kernel =
        (x + (k : ℤ) • frame.child.modifiedDeck.kernel) + frame.child.modifiedDeck.kernel := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, hG, ih x]
    ring
  | pred k ih =>
    intro x
    have h1 := hG (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel)
    have e2 : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.kernel + frame.child.modifiedDeck.kernel =
        x + (-(k : ℤ)) • frame.child.modifiedDeck.kernel := by
      rw [sub_smul, one_smul]
      abel
    rw [e2, ih x] at h1
    linear_combination (-1 : ℤ) * h1

theorem char_transverse {G : Site → ℤ} {cV : ℤ} (hG : ∀ z, G (z + frame.child.modifiedDeck.transverse) = G z + cV)
    (j : ℤ) : ∀ x : Site, G (x + j • frame.child.modifiedDeck.transverse) = G x + j * cV := by
  induction j using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have e : x + ((k : ℤ) + 1) • frame.child.modifiedDeck.transverse =
        (x + (k : ℤ) • frame.child.modifiedDeck.transverse) + frame.child.modifiedDeck.transverse := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, hG, ih x]
    ring
  | pred k ih =>
    intro x
    have h1 := hG (x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse)
    have e2 : x + (-(k : ℤ) - 1) • frame.child.modifiedDeck.transverse + frame.child.modifiedDeck.transverse =
        x + (-(k : ℤ)) • frame.child.modifiedDeck.transverse := by
      rw [sub_smul, one_smul]
      abel
    rw [e2, ih x] at h1
    linear_combination (-1 : ℤ) * h1

/-- The selection at a white centre: the input of smaller rank, with ties to the negative input. -/
def selectR (R : Site → ℤ) (c : Site) : Site :=
  if R (incomingPos c) < R (incomingNeg c) then incomingPos c else incomingNeg c

/-- The policy of a rank: black centres keep both inputs, white centres keep the selection. -/
def rankPolicy (F : Field) (R : Site → ℤ) : Site → Site → Prop :=
  fun c i => (laplacian F c = -1 ∧ Edge i c) ∨ (laplacian F c = 0 ∧ i = selectR R c)

theorem selectR_add_span {R : Site → ℤ} {cRU cRV : ℤ}
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cRU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cRV) (i j : ℤ) (z : Site) :
    selectR R (z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) =
      selectR R z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) := by
  have hs := evenSite_span frame i j
  have hP := incomingPos_add_even hs z
  have hN := incomingNeg_add_even hs z
  have hPR : R (incomingPos z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) =
      R (incomingPos z) + (i * cRU + j * cRV) := by
    rw [← add_assoc, char_transverse frame hRV j, char_kernel frame hRU i]
    ring
  have hNR : R (incomingNeg z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) =
      R (incomingNeg z) + (i * cRU + j * cRV) := by
    rw [← add_assoc, char_transverse frame hRV j, char_kernel frame hRU i]
    ring
  unfold selectR
  rw [hP, hN, hPR, hNR]
  by_cases h : R (incomingPos z) < R (incomingNeg z)
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]

/-- The rank policy is invariant under translation by a span element. -/
theorem rankPolicy_add_span {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    {R : Site → ℤ} {cRU cRV : ℤ}
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cRU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cRV) (i j : ℤ) (z u : Site) :
    rankPolicy F R (z + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse))
        (u + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse)) ↔
      rankPolicy F R z u := by
  have hs := evenSite_span frame i j
  unfold rankPolicy Edge
  rw [laplacian_add_span frame hF i j z, incomingNeg_add_even hs z, incomingPos_add_even hs z,
    selectR_add_span frame hRU hRV i j z]
  simp only [add_left_inj]

/-- The deck form used by the chain theorem: translation by `−(iU + jV)`. -/
theorem rankPolicy_deck {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    {R : Site → ℤ} {cRU cRV : ℤ}
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cRU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cRV) (i j : ℤ) (z u : Site)
    (h : rankPolicy F R z u) :
    rankPolicy F R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j) := by
  have e : ∀ x : Site, x - frame.child.modifiedDeck.combine i j =
      x + ((-i) • frame.child.modifiedDeck.kernel + (-j) • frame.child.modifiedDeck.transverse) := by
    intro x
    rw [combine_eq]
    ext <;> simp <;> ring
  rw [e z, e u]
  exact (rankPolicy_add_span frame hF hRU hRV (-i) (-j) z u).mpr h

theorem selectR_input (R : Site → ℤ) (c : Site) : selectR R c = incomingNeg c ∨ selectR R c = incomingPos c := by
  unfold selectR
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The quota of the rank policy. -/
theorem rankPolicy_quota (F : Field) (R : Site → ℤ) : RetainQuota F (rankPolicy F R) := by
  constructor
  · intro c hc
    constructor
    · left
      exact ⟨hc, Or.inl rfl⟩
    · left
      exact ⟨hc, Or.inr rfl⟩
  · intro c hc
    rcases selectR_input R c with h | h
    · left
      exact Or.inr ⟨hc, h.symm⟩
    · right
      exact Or.inr ⟨hc, h.symm⟩

theorem rankPolicy_white (F : Field) (R : Site → ℤ) {c : Site} (hc : laplacian F c = 0) (i : Site) :
    rankPolicy F R c i ↔ i = selectR R c := by
  unfold rankPolicy
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · rw [hc] at h1
      norm_num at h1
    · exact h2
  · intro h
    exact Or.inr ⟨hc, h⟩

theorem rankPolicy_edge (F : Field) (R : Site → ℤ) {c i : Site} (h : rankPolicy F R c i) : Edge i c := by
  unfold rankPolicy at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · subst h
    rcases selectR_input R c with h' | h'
    · rw [h']
      exact Or.inl rfl
    · rw [h']
      exact Or.inr rfl

end FLatticePaper.DeckSelection
