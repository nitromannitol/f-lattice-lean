import FLatticePaper.Tiles.JointFamily

/-! # The one induction of Sections 7 and 8 (`lemma:weak_standard_odometer_properties`, `lemma:tile-odometer-existence`)

Surgical edition 274ad18: the weak odometers, the weak alternate odometers, the tile odometers, the alternate tile odometers and
the L-corrected odometers of a word are built from the tile odometers (and the alternate tile and L-corrected odometers) of
strictly shorter words, and the properties (c) of the weak odometers, (b) of the weak alternate odometers and (a)-(c) of the tile
odometers are proved along the way.
The induction runs over the length of the word: the rotation identity (c) relates the children of `w` and of `swapW w`, which have
the same length, so all the words of one length form one step.

* `exists_family_by_length`: a family exists once a predicate that reads only the words of length at most `|w|` can be satisfied
  at every length, given the shorter words.
* `regsAt_lt`: the register words of `w` (the parents of its children) are shorter than `w`.
* `joint_family_exists`: the induction. Its per-step inputs are named (`WeakStepInput`, `WeakAltStepInput`, `TileStepInput`,
  `LStepInput`, `RotStepInput`); each produces the odometers of one kind at `w`, with their part of the joint predicate and of the
  properties, from the joint family on the shorter words. They are the existence steps of the text and are not proved here. -/

namespace FLatticePaper.Tiles.JointInduction

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.Standard (IsBase swapW)

/-! ### A family by induction on the length of the word -/

section Generic

variable {α : Type} [Inhabited α] (Good : (Word → α) → Word → Prop)

/-- The families good on the words shorter than `n`, built length by length. -/
noncomputable def famSeq
    (hloc : ∀ (f g : Word → α) (w : Word), (∀ u : Word, u.length ≤ w.length → f u = g u) → Good f w → Good g w)
    (hstep : ∀ (n : ℕ) (f : Word → α), (∀ u : Word, u.length < n → Good f u) →
      ∃ g : Word → α, (∀ u : Word, u.length < n → g u = f u) ∧ ∀ u : Word, u.length = n → Good g u) :
    (n : ℕ) → {f : Word → α // ∀ u : Word, u.length < n → Good f u}
  | 0 => ⟨default, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 =>
    ⟨Classical.choose (hstep n (famSeq hloc hstep n).1 (famSeq hloc hstep n).2), fun u hu => by
      have hs := Classical.choose_spec (hstep n (famSeq hloc hstep n).1 (famSeq hloc hstep n).2)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
      · exact hloc _ _ u (fun v hv => (hs.1 v (lt_of_le_of_lt hv hlt)).symm) ((famSeq hloc hstep n).2 u hlt)
      · exact hs.2 u heq⟩

theorem famSeq_succ
    (hloc : ∀ (f g : Word → α) (w : Word), (∀ u : Word, u.length ≤ w.length → f u = g u) → Good f w → Good g w)
    (hstep : ∀ (n : ℕ) (f : Word → α), (∀ u : Word, u.length < n → Good f u) →
      ∃ g : Word → α, (∀ u : Word, u.length < n → g u = f u) ∧ ∀ u : Word, u.length = n → Good g u)
    (n : ℕ) (u : Word) (hu : u.length < n) :
    (famSeq Good hloc hstep (n + 1)).1 u = (famSeq Good hloc hstep n).1 u :=
  (Classical.choose_spec (hstep n (famSeq Good hloc hstep n).1 (famSeq Good hloc hstep n).2)).1 u hu

theorem famSeq_stable
    (hloc : ∀ (f g : Word → α) (w : Word), (∀ u : Word, u.length ≤ w.length → f u = g u) → Good f w → Good g w)
    (hstep : ∀ (n : ℕ) (f : Word → α), (∀ u : Word, u.length < n → Good f u) →
      ∃ g : Word → α, (∀ u : Word, u.length < n → g u = f u) ∧ ∀ u : Word, u.length = n → Good g u)
    (u : Word) (k : ℕ) :
    (famSeq Good hloc hstep (u.length + 1 + k)).1 u = (famSeq Good hloc hstep (u.length + 1)).1 u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, famSeq_succ Good hloc hstep _ u (by omega), ih]

/-- A family good at every word exists, when goodness at `w` reads only the words of length at most `|w|` and can be reached
at each length from the shorter words. -/
theorem exists_family_by_length
    (hloc : ∀ (f g : Word → α) (w : Word), (∀ u : Word, u.length ≤ w.length → f u = g u) → Good f w → Good g w)
    (hstep : ∀ (n : ℕ) (f : Word → α), (∀ u : Word, u.length < n → Good f u) →
      ∃ g : Word → α, (∀ u : Word, u.length < n → g u = f u) ∧ ∀ u : Word, u.length = n → Good g u) :
    ∃ f : Word → α, ∀ w : Word, Good f w := by
  refine ⟨fun w => (famSeq Good hloc hstep (w.length + 1)).1 w, fun w => ?_⟩
  refine hloc _ _ w (fun u hu => ?_) ((famSeq Good hloc hstep (w.length + 1)).2 w (Nat.lt_succ_self _))
  obtain ⟨k, hk⟩ : ∃ k, w.length + 1 = u.length + 1 + k := ⟨w.length - u.length, by omega⟩
  show (famSeq Good hloc hstep (w.length + 1)).1 u = (famSeq Good hloc hstep (u.length + 1)).1 u
  rw [hk, famSeq_stable Good hloc hstep u k]

end Generic

/-! ### The parents of a word are shorter words -/

/-- Reading letters keeps the register words shorter than the prefix read so far. -/
theorem regRun_lt (pre rest : Word) (r : Option Word × Option Word)
    (hr : ∀ v : Word, (r.1 = some v ∨ r.2 = some v) → v.length < pre.length) :
    ∀ v : Word, ((regRun pre rest r).1 = some v ∨ (regRun pre rest r).2 = some v) →
      v.length < (pre ++ rest).length := by
  induction rest generalizing pre r with
  | nil => simpa [regRun] using hr
  | cons d rest ih =>
    have hs : ∀ v : Word, ((regStep pre r d).1 = some v ∨ (regStep pre r d).2 = some v) →
        v.length < (pre ++ [d]).length := by
      intro v hv
      simp only [List.length_append, List.length_singleton]
      cases d <;> simp only [regStep] at hv <;> rcases hv with hv | hv <;>
        first
        | (simp only [Option.some.injEq] at hv; subst hv; omega)
        | (have := hr v (Or.inl hv); omega)
        | (have := hr v (Or.inr hv); omega)
    intro v hv
    have := ih (pre ++ [d]) (regStep pre r d) hs v (by simpa [regRun] using hv)
    simpa [List.append_assoc] using this

/-- The register words of `w` (the words whose children are the parents of the children of `w`) are shorter than `w`. -/
theorem regsAt_lt (w u : Word) (hu : (regsAt w).1 = some u ∨ (regsAt w).2 = some u) : u.length < w.length := by
  simpa using regRun_lt [] w (none, none) (fun v hv => by simp at hv) u hu

/-! ### Locality -/

theorem below_congr (f g : Word → JSlice) (w : Word) (h : ∀ u : Word, u.length < w.length → f u = g u) :
    below f w = below g w := by
  funext u
  unfold below
  split_ifs with hu
  · exact h u hu
  · rfl

/-- The joint predicate and the properties at `w` read only the words of length at most `|w|`. -/
theorem good_congr (D : JointData) (f g : Word → JSlice) (w : Word)
    (h : ∀ u : Word, u.length ≤ w.length → f u = g u) (hf : IsJointSlice D f w ∧ JointProps f w) :
    IsJointSlice D g w ∧ JointProps g w := by
  have hb := below_congr f g w (fun u hu => h u hu.le)
  have hw := h w le_rfl
  have hr := h (swapW w) (by simp [swapW])
  unfold IsJointSlice JointProps at *
  rw [← hb, ← hw, ← hr]
  exact hf

/-! ### The per-step inputs and the induction -/

/-- The joint family is good on the words shorter than `n`. -/
def GoodBelow (D : JointData) (f : Word → JSlice) (n : ℕ) : Prop :=
  ∀ u : Word, u.length < n → IsJointSlice D f u ∧ JointProps f u

/-- The weak standard step (`lemma:weak_standard_odometer_properties`, Steps 1 and 2 with (c), over the tile parents): from the
family on the words shorter than `w`, weak odometers at `w` with their part and (c). -/
def WeakStepInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    ∃ wo we : PartialOdometer, WeakPart D (below f w) w wo we ∧ WeakPropsU w wo we

/-- The weak alternate step (`lemma:weak_alternate_odometer_properties`, over the tile parents and the alternate tile parents),
with (b) at the alternate children that are not corrected. -/
def WeakAltStepInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    ∃ wao wae : PartialOdometer, WeakAltPart D (below f w) w wao wae ∧ WeakAltPropsU w wao wae

/-- The tile step (`lemma:tile-odometer-existence`, existence with (a) and (b), Cases 1-4 and the rotated children): from the
family on the shorter words and the weak odometers at `w`, tile odometers at `w` with their part, (a) and (b), and (b) of
`lemma:weak_alternate_odometer_properties` for the alternate tile odometers (the weak alternate odometers at the children that are
not corrected). -/
def TileStepInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae : PartialOdometer), GoodBelow D f w.length →
    WeakPart D (below f w) w wo we → WeakPropsU w wo we → WeakAltPart D (below f w) w wao wae →
    WeakAltPropsU w wao wae →
    ∃ tod tev aod aev : PartialOdometer,
      TilePart D (below f w) w wo we wao wae tod tev aod aev ∧ TileProps w tod tev aod aev ∧
        AltLatticeSelfCompat w aod aev

/-- The L step (`lemma:l_correct_existence`): from the family on the shorter words and the tile odometers at `w`, the L-corrected
odometers of the children of `w`. -/
def LStepInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer), GoodBelow D f w.length →
    WeakPart D (below f w) w wo we → WeakAltPart D (below f w) w wao wae →
    TilePart D (below f w) w wo we wao wae tod tev aod aev → TileProps w tod tev aod aev →
    ∃ lo le : Bool → Bool → PartialOdometer, LPart D (below f w) w tod tev lo le

/-- The rotation step ((c) of `lemma:tile-odometer-existence`, "Rotations" in its proof): once every word of length `n` has its
joint predicate, (c) of the weak odometers and (a), (b) of the tile odometers, the rotation identities hold at length `n`, for the
tile odometers and for the L-corrected odometers. -/
def RotStepInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (n : ℕ), GoodBelow D f n →
    (∀ w : Word, w.length = n →
      IsJointSlice D f w ∧ WeakPropsU w (f w).wOdd (f w).wEven ∧ TileProps w (f w).tOdd (f w).tEven (f w).aOdd (f w).aEven) →
    ∀ w : Word, w.length = n → RotProps w (f w) (f (swapW w)) ∧ LRotProps w (f w) (f (swapW w))

/-- The one induction of Sections 7-8: given the five per-step inputs, there is a joint family, with the weak, weak alternate,
tile, alternate tile and L-corrected odometers of every word built over the tile odometers of the shorter words, and with (a) and
(c) of `lemma:weak_standard_odometer_properties` and (a)-(c) of `lemma:tile-odometer-existence` at every word ((b) of the weak
lemma follows from (a) by `corner_3_family` and the corner identities), and (b) of
`lemma:weak_alternate_odometer_properties` for the alternate tile odometers. -/
theorem joint_family_exists (D : JointData) (hW : WeakStepInput D) (hWA : WeakAltStepInput D) (hT : TileStepInput D)
    (hL : LStepInput D) (hR : RotStepInput D) : ∃ f : Word → JSlice, IsJointFamily D f := by
  refine exists_family_by_length (fun f w => IsJointSlice D f w ∧ JointProps f w)
    (fun f g w h hf => good_congr D f g w h hf) (fun n f hf => ?_)
  have hfu : ∀ u : Word, u.length = n → GoodBelow D f u.length := fun u hu => hu ▸ hf
  choose wo we hWp hWq using fun u (hu : u.length = n) => hW f u (hfu u hu)
  choose wao wae hAp hAq using fun u (hu : u.length = n) => hWA f u (hfu u hu)
  choose tod tev aod aev hTp hTq hTa using fun u (hu : u.length = n) =>
    hT f u (wo u hu) (we u hu) (wao u hu) (wae u hu) (hfu u hu) (hWp u hu) (hWq u hu) (hAp u hu) (hAq u hu)
  choose lo le hLp using fun u (hu : u.length = n) =>
    hL f u (wo u hu) (we u hu) (wao u hu) (wae u hu) (tod u hu) (tev u hu) (aod u hu) (aev u hu) (hfu u hu) (hWp u hu)
      (hAp u hu) (hTp u hu) (hTq u hu)
  let g : Word → JSlice := fun u =>
    if hu : u.length = n then
      ⟨wo u hu, we u hu, wao u hu, wae u hu, tod u hu, tev u hu, aod u hu, aev u hu, lo u hu, le u hu⟩
    else f u
  have hgf : ∀ u : Word, u.length < n → g u = f u := fun u hu => by
    simp only [g, dif_neg (Nat.ne_of_lt hu)]
  have hgu : ∀ u : Word, ∀ hu : u.length = n,
      g u = ⟨wo u hu, we u hu, wao u hu, wae u hu, tod u hu, tev u hu, aod u hu, aev u hu, lo u hu, le u hu⟩ :=
    fun u hu => by simp only [g, dif_pos hu]
  have hbelow : ∀ u : Word, u.length = n → below g u = below f u := fun u hu =>
    below_congr g f u (fun v hv => hgf v (hu ▸ hv))
  have hgood : GoodBelow D g n := fun u hu =>
    good_congr D f g u (fun v hv => (hgf v (lt_of_le_of_lt hv hu)).symm) (hf u hu)
  have hslice : ∀ u : Word, u.length = n →
      IsJointSlice D g u ∧ WeakPropsU u (g u).wOdd (g u).wEven ∧
        TileProps u (g u).tOdd (g u).tEven (g u).aOdd (g u).aEven := by
    intro u hu
    unfold IsJointSlice
    rw [hbelow u hu, hgu u hu]
    exact ⟨⟨hWp u hu, hAp u hu, hTp u hu, hLp u hu⟩, hWq u hu, hTq u hu⟩
  refine ⟨g, hgf, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hslice u hu
  have h4 : AltLatticeSelfCompat u (g u).aOdd (g u).aEven := by
    rw [hgu u hu]
    exact hTa u hu
  exact ⟨h1, h2, h3, (hR g n hgood hslice u hu).1, (hR g n hgood hslice u hu).2, h4⟩

end FLatticePaper.Tiles.JointInduction
