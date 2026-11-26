import FLatticePaper.Plane.Induction.FreeWebClaims
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.AndOrRank
import FLatticePaper.Plane.Induction.ChildFrame
import FLatticePaper.Plane.AlternateSlip

/-! # The Protected Web Lemma (Q39, §4), with the unit square containing a unique free corner

The hypotheses are the packet strips of the field, the deck invariance of its Laplacian, and the two extended strips (the even zero
strip on `[2 - L, 2L - 2]` and the odd `h_0` band on `[2 - 3d + n, 3d + n - 2]`). The web lemma: a unit square with a free corner `y`
and no other free corner has a white corner `u ≠ y` whose free input lies outside the square. -/

namespace FLatticePaper.ProtectedWeb

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure FLatticePaper.FreeWebClaims
  FLatticePaper.AndOrRank FLatticePaper.SquareClauses

/-- The hypotheses on the field `F` of a child frame, from the packet and the two extended strips. -/
structure WebHyp (frame : ChildFrame) (F : Field) : Prop where
  strips : frame.HasStrips F
  inv : ∀ (z v : Site), v ∈ frame.child.modifiedDeck.span → laplacian F (z + v) = laplacian F z
  evenExt : ∀ z : Site, EvenSite z → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade z →
    frame.tGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = 0
  oddExt : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
    frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z

theorem white_of_freeClosure {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) {w : Site}
    (h : freeClosure frame w) : laplacian F w = 0 := by
  obtain ⟨s, hs, h2⟩ := h
  have h3 : laplacian F (w + s) = 0 := by
    rcases h2 with h2 | h2
    · exact laplacian_eq_zero_of_freeH frame hW.strips h2
    · exact frame.laplacian_eq_zero_of_freeV hW.strips h2
  rw [hW.inv w s hs] at h3
  exact h3

theorem mem_sq (a b : ℤ) (c : Site) :
    c ∈ squareCorners a b ↔ (c.1 = a ∨ c.1 = a + 1) ∧ (c.2 = b ∨ c.2 = b + 1) := by
  unfold squareCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
  · rintro ⟨h1, h2⟩
    omega

theorem shift_mem (a b : ℤ) (c s : Site) :
    c ∈ squareCorners a b ↔ c + s ∈ squareCorners (a + s.1) (b + s.2) := by
  rw [mem_sq, mem_sq]
  simp only [Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor <;> omega

theorem ne_fst {y c : Site} (h : c.1 ≠ y.1) : c ≠ y := fun e => h (congrArg Prod.fst e)
theorem ne_snd {y c : Site} (h : c.2 ≠ y.2) : c ≠ y := fun e => h (congrArg Prod.snd e)

theorem incomingNeg_of_odd (x : Site) (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg; rw [if_neg h]

theorem incomingPos_of_odd (x : Site) (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos; rw [if_neg h]

theorem incomingNeg_of_even (x : Site) (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg; rw [if_pos h]

theorem incomingPos_of_even (x : Site) (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos; rw [if_pos h]

theorem lap_odd_zero {F : Field} (u : Site) (hu : ¬ EvenSite u) (h0 : F u = 0)
    (h1 : F (u.1, u.2 - 1) = 0) (h2 : F (u.1, u.2 + 1) = 0) : laplacian F u = 0 := by
  unfold laplacian
  rw [incomingNeg_of_odd u hu, incomingPos_of_odd u hu, h0, h1, h2]
  ring

theorem lap_even_zero {F : Field} (u : Site) (hu : EvenSite u) (h0 : F u = 0)
    (h1 : F (u.1 - 1, u.2) = 0) (h2 : F (u.1 + 1, u.2) = 0) : laplacian F u = 0 := by
  unfold laplacian
  rw [incomingNeg_of_even u hu, incomingPos_of_even u hu, h0, h1, h2]
  ring

theorem lap_odd_harm {F : Field} (u : Site) (hu : ¬ EvenSite u) (h0 : F u = harmonicGrid u)
    (h1 : F (u.1, u.2 - 1) = harmonicGrid (u.1, u.2 - 1)) (h2 : F (u.1, u.2 + 1) = harmonicGrid (u.1, u.2 + 1)) :
    laplacian F u = 0 := by
  have hh := harmonicGrid_harmonic u
  unfold laplacian at hh ⊢
  rw [incomingNeg_of_odd u hu, incomingPos_of_odd u hu] at hh ⊢
  rw [h0, h1, h2]
  linarith

theorem lap_even_harm {F : Field} (u : Site) (hu : EvenSite u) (h0 : F u = harmonicGrid u)
    (h1 : F (u.1 - 1, u.2) = harmonicGrid (u.1 - 1, u.2)) (h2 : F (u.1 + 1, u.2) = harmonicGrid (u.1 + 1, u.2)) :
    laplacian F u = 0 := by
  have hh := harmonicGrid_harmonic u
  unfold laplacian at hh ⊢
  rw [incomingNeg_of_even u hu, incomingPos_of_even u hu] at hh ⊢
  rw [h0, h1, h2]
  linarith

/-- **The protected web lemma for a free corner in the fundamental position.** -/
theorem web_core {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) {a b : ℤ} {y : Site}
    (hy : y ∈ squareCorners a b) (hyF : y ∈ frame.freeH ∨ y ∈ frame.freeV)
    (hothers : ∀ c ∈ squareCorners a b, c ≠ y → ¬ freeClosure frame c) :
    ∃ u ∈ squareCorners a b, u ≠ y ∧ laplacian F u = 0 ∧
      ∃ w : Site, (w = incomingNeg u ∨ w = incomingPos u) ∧ w ∉ squareCorners a b ∧ freeClosure frame w := by
  obtain ⟨y1, y2⟩ := y
  rw [mem_sq] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hne : ∀ c : Site, (c.1 = a ∨ c.1 = a + 1) → (c.2 = b ∨ c.2 = b + 1) → c ≠ (y1, y2) →
      ¬ freeClosure frame c := fun c h1 h2 h3 => hothers c ((mem_sq a b c).2 ⟨h1, h2⟩) h3
  have hnotQ : ∀ c : Site, ¬ ((c.1 = a ∨ c.1 = a + 1) ∧ (c.2 = b ∨ c.2 = b + 1)) → c ∉ squareCorners a b :=
    fun c h hc => h ((mem_sq a b c).1 hc)
  rcases hyF with hH | hV
  · by_cases hpar : EvenSite (y1, y2)
    · -- an even free H site: the four squares
      have hpar' : (y1 + y2) % 2 = 0 := hpar
      obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
      have hF := H2F frame hH hpar
      have hB := H2B frame hH hpar
      have hte := freeH_even_t frame hH hpar
      have hbox := freeH_bounds frame hH
      have hsL := freeH_s frame hH
      obtain ⟨ht2, htL⟩ := hte
      have hodd := frame.child_odd
      rcases hy1 with ha | ha <;> rcases hy2 with hb | hb
      · -- NE: a = y1, b = y2; both disjuncts of H2F are in the square
        exfalso
        rcases hF with ⟨-, h⟩ | ⟨-, h⟩
        · exact hne (y1 + 1, y2) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
        · exact hne (y1 + 1, y2 + 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
      · -- SE: a = y1, b = y2 - 1; the point (y1 + 1, y2) is in the square, so the second disjunct holds
        have hnot : ¬ freeClosure frame (y1 + 1, y2) :=
          hne (y1 + 1, y2) (by dsimp only; omega) (by dsimp only; omega) (ne_fst (by dsimp only; omega))
        rcases hF with ⟨-, h⟩ | ⟨hgt, h⟩
        · exact absurd h hnot
        · have hu : ¬ EvenSite (y1 + 1, y2) := by
            unfold EvenSite; simp only; omega
          have ht_u : frame.tGrade (y1 + 1, y2) = frame.tGrade (y1, y2) + frame.child.num := by
            unfold ChildFrame.tGrade; ring
          have ht_d : frame.tGrade (y1 + 1, y2 - 1) = frame.tGrade (y1, y2) + (frame.child.num + frame.child.den) := by
            unfold ChildFrame.tGrade; ring
          have ht_p : frame.tGrade (y1 + 1, y2 + 1) = frame.tGrade (y1, y2) + frame.child.num - frame.child.den := by
            unfold ChildFrame.tGrade; ring
          have hev1 : EvenSite (y1 + 1, y2 - 1) := by
            unfold EvenSite; simp only; omega
          have h0 : F (y1 + 1, y2) = 0 := hW.strips.1 _ (by omega) (by omega)
          have h1 : F (y1 + 1, y2 - 1) = 0 := hW.evenExt _ hev1 (by omega) (by omega)
          have h2 : F (y1 + 1, y2 + 1) = 0 := hW.strips.1 _ (by omega) (by omega)
          refine ⟨(y1 + 1, y2), (mem_sq a b _).2 ⟨by dsimp only; omega, by dsimp only; omega⟩,
            ne_fst (by dsimp only; omega), lap_odd_zero _ hu h0 h1 h2, (y1 + 1, y2 + 1),
            Or.inr (incomingPos_of_odd _ hu).symm, ?_, h⟩
          exact hnotQ _ (fun hm => by obtain ⟨h3, h4⟩ := hm; dsimp only at h3 h4; omega)
      · -- NW: a = y1 - 1, b = y2; the point (y1 - 1, y2) is in the square, so the second disjunct holds
        have hnot : ¬ freeClosure frame (y1 - 1, y2) :=
          hne (y1 - 1, y2) (by dsimp only; omega) (by dsimp only; omega) (ne_fst (by dsimp only; omega))
        rcases hB with ⟨-, h⟩ | ⟨hlt, h⟩
        · exact absurd h hnot
        · have hu : ¬ EvenSite (y1 - 1, y2) := by
            unfold EvenSite; simp only; omega
          have ht_m : frame.tGrade (y1 - 1, y2) = frame.tGrade (y1, y2) - frame.child.num := by
            unfold ChildFrame.tGrade; ring
          have ht_ud : frame.tGrade (y1 - 1, y2 - 1) = frame.tGrade (y1, y2) + frame.child.den - frame.child.num := by
            unfold ChildFrame.tGrade; ring
          have ht_uu : frame.tGrade (y1 - 1, y2 + 1) = frame.tGrade (y1, y2) - (frame.child.num + frame.child.den) := by
            unfold ChildFrame.tGrade; ring
          have hev2 : EvenSite (y1 - 1, y2 + 1) := by
            unfold EvenSite; simp only; omega
          have h0 : F (y1 - 1, y2) = 0 := hW.strips.1 _ (by omega) (by omega)
          have h1 : F (y1 - 1, y2 - 1) = 0 := hW.strips.1 _ (by omega) (by omega)
          have h2 : F (y1 - 1, y2 + 1) = 0 := hW.evenExt _ hev2 (by omega) (by omega)
          refine ⟨(y1 - 1, y2), (mem_sq a b _).2 ⟨by dsimp only; omega, by dsimp only; omega⟩,
            ne_fst (by dsimp only; omega), lap_odd_zero _ hu h0 h1 h2, (y1 - 1, y2 - 1),
            Or.inl (incomingNeg_of_odd _ hu).symm, ?_, h⟩
          exact hnotQ _ (fun hm => by obtain ⟨h3, h4⟩ := hm; dsimp only at h3 h4; omega)
      · -- SW: a = y1 - 1, b = y2 - 1; both disjuncts of H2B are in the square
        exfalso
        rcases hB with ⟨-, h⟩ | ⟨-, h⟩
        · exact hne (y1 - 1, y2) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
        · exact hne (y1 - 1, y2 - 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
    · -- an odd free H site: both horizontal neighbours are free, and one of them is in the square
      rcases hy1 with ha | ha
      · exact absurd (H1R frame hH hpar)
          (hne (y1 + 1, y2) (by dsimp only; omega) (by dsimp only; omega) (ne_fst (by dsimp only; omega)))
      · exact absurd (H1L frame hH hpar)
          (hne (y1 - 1, y2) (by dsimp only; omega) (by dsimp only; omega) (ne_fst (by dsimp only; omega)))
  · by_cases hpar : EvenSite (y1, y2)
    · -- an even free V site: the up and down neighbours are free, one of them is in the square
      rcases hy2 with hb | hb
      · exact absurd (V1U frame hV hpar)
          (hne (y1, y2 + 1) (by dsimp only; omega) (by dsimp only; omega) (ne_snd (by dsimp only; omega)))
      · exact absurd (V1D frame hV hpar)
          (hne (y1, y2 - 1) (by dsimp only; omega) (by dsimp only; omega) (ne_snd (by dsimp only; omega)))
    · -- an odd free V site: the four squares
      obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
      have hpar' : ¬ (y1 + y2) % 2 = 0 := hpar
      have hodd' : ¬ EvenSite (y1 + 1, y2 + 1) := by
        unfold EvenSite; simp only; omega
      rcases hy1 with ha | ha <;> rcases hy2 with hb | hb
      · -- NE: a = y1, b = y2; the point (y1, y2 + 1) is in the square
        have hF := V2F frame hV hpar
        have hnot : ¬ freeClosure frame (y1, y2 + 1) :=
          hne (y1, y2 + 1) (by dsimp only; omega) (by dsimp only; omega) (ne_snd (by dsimp only; omega))
        rcases hF with ⟨-, h⟩ | ⟨hs4, h⟩
        · exact absurd h hnot
        · obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hV hpar
          have hu : EvenSite (y1, y2 + 1) := by
            unfold EvenSite; simp only; omega
          have hsu : frame.sGrade (y1, y2 + 1) = frame.sGrade (y1, y2) + (frame.child.den - frame.child.num) := by
            unfold ChildFrame.sGrade; ring
          have hsw : frame.sGrade (y1 - 1, y2 + 1) = frame.sGrade (y1, y2) - 2 * frame.child.num := by
            unfold ChildFrame.sGrade; ring
          have hse : frame.sGrade (y1 + 1, y2 + 1) = frame.sGrade (y1, y2) + 2 * frame.child.den := by
            unfold ChildFrame.sGrade; ring
          have h0 : F (y1, y2 + 1) = harmonicGrid (y1, y2 + 1) := hW.strips.2 _ (by omega) (by omega)
          have h1 : F (y1 - 1, y2 + 1) = harmonicGrid (y1 - 1, y2 + 1) := hW.strips.2 _ (by omega) (by omega)
          have h2 : F (y1 + 1, y2 + 1) = harmonicGrid (y1 + 1, y2 + 1) := hW.oddExt _ hodd' (by omega) (by omega)
          refine ⟨(y1, y2 + 1), (mem_sq a b _).2 ⟨by dsimp only; omega, by dsimp only; omega⟩,
            ne_snd (by dsimp only; omega), lap_even_harm _ hu h0 h1 h2, (y1 - 1, y2 + 1),
            Or.inl (incomingNeg_of_even _ hu).symm, ?_, h⟩
          exact hnotQ _ (fun hm => by obtain ⟨h3, h4⟩ := hm; dsimp only at h3 h4; omega)
      · -- SE: a = y1, b = y2 - 1; both backward neighbours are in the square
        exfalso
        rcases V2B frame hV hpar with ⟨-, h⟩ | ⟨-, h⟩
        · exact hne (y1, y2 - 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_snd (by dsimp only; omega)) h
        · exact hne (y1 + 1, y2 - 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
      · -- NW: a = y1 - 1, b = y2; both forward neighbours are in the square
        exfalso
        rcases V2F frame hV hpar with ⟨-, h⟩ | ⟨-, h⟩
        · exact hne (y1, y2 + 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_snd (by dsimp only; omega)) h
        · exact hne (y1 - 1, y2 + 1) (by dsimp only; omega) (by dsimp only; omega)
            (ne_fst (by dsimp only; omega)) h
      · -- SW: a = y1 - 1, b = y2 - 1; the point (y1, y2 - 1) is in the square, so the second disjunct holds
        have hnot : ¬ freeClosure frame (y1, y2 - 1) :=
          hne (y1, y2 - 1) (by dsimp only; omega) (by dsimp only; omega) (ne_snd (by dsimp only; omega))
        rcases V2B frame hV hpar with ⟨-, h⟩ | ⟨hs5, h⟩
        · exact absurd h hnot
        · obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hV hpar
          have hu : EvenSite (y1, y2 - 1) := by
            unfold EvenSite; simp only; omega
          have hsu : frame.sGrade (y1, y2 - 1) = frame.sGrade (y1, y2) - (frame.child.den - frame.child.num) := by
            unfold ChildFrame.sGrade; ring
          have hsw : frame.sGrade (y1 - 1, y2 - 1) = frame.sGrade (y1, y2) - 2 * frame.child.den := by
            unfold ChildFrame.sGrade; ring
          have hse : frame.sGrade (y1 + 1, y2 - 1) = frame.sGrade (y1, y2) + 2 * frame.child.num := by
            unfold ChildFrame.sGrade; ring
          have hodd2 : ¬ EvenSite (y1 - 1, y2 - 1) := by
            unfold EvenSite; simp only; omega
          have h0 : F (y1, y2 - 1) = harmonicGrid (y1, y2 - 1) := hW.strips.2 _ (by omega) (by omega)
          have h1 : F (y1 - 1, y2 - 1) = harmonicGrid (y1 - 1, y2 - 1) := hW.oddExt _ hodd2 (by omega) (by omega)
          have h2 : F (y1 + 1, y2 - 1) = harmonicGrid (y1 + 1, y2 - 1) := hW.strips.2 _ (by omega) (by omega)
          refine ⟨(y1, y2 - 1), (mem_sq a b _).2 ⟨by dsimp only; omega, by dsimp only; omega⟩,
            ne_snd (by dsimp only; omega), lap_even_harm _ hu h0 h1 h2, (y1 + 1, y2 - 1),
            Or.inr (incomingPos_of_even _ hu).symm, ?_, h⟩
          exact hnotQ _ (fun hm => by obtain ⟨h3, h4⟩ := hm; dsimp only at h3 h4; omega)

theorem combine_eq (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  ext <;> simp [PeriodDeck.combine, ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]

/-- Every deck vector is even (the coordinate sum `(i + j) ... ` is even since `n + d` is). -/
theorem span_even (frame : ChildFrame) {s : Site} (hs : s ∈ frame.child.modifiedDeck.span) : EvenSite s := by
  obtain ⟨i, j, rfl⟩ := hs
  rw [combine_eq]
  obtain ⟨k, hk⟩ : ∃ k, frame.child.num + frame.child.den = 2 * k :=
    ⟨(frame.child.num + frame.child.den) / 2, by
      have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
      omega⟩
  unfold EvenSite
  have e : i * frame.child.den + j * (frame.child.num - frame.child.den) +
      (i * frame.child.num + j * (frame.child.num + frame.child.den)) =
      2 * (i * k + j * frame.child.num) := by linear_combination i * hk
  simp only
  rw [e]
  simp

theorem incomingNeg_ne_self (x : Site) : incomingNeg x ≠ x := by
  intro h
  unfold incomingNeg at h
  split_ifs at h
  · have := congrArg Prod.fst h
    dsimp only at this
    omega
  · have := congrArg Prod.snd h
    dsimp only at this
    omega

theorem incomingPos_ne_self (x : Site) : incomingPos x ≠ x := by
  intro h
  unfold incomingPos at h
  split_ifs at h
  · have := congrArg Prod.fst h
    dsimp only at this
    omega
  · have := congrArg Prod.snd h
    dsimp only at this
    omega

/-- **The web lemma for a general free corner.** Translating by the deck span moves the free corner into `freeH ∪ freeV`. -/
theorem web_general {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) {a b : ℤ} {y : Site}
    (hy : y ∈ squareCorners a b) (hfy : freeClosure frame y)
    (hothers : ∀ c ∈ squareCorners a b, c ≠ y → ¬ freeClosure frame c) :
    ∃ u ∈ squareCorners a b, u ≠ y ∧ laplacian F u = 0 ∧
      ∃ w : Site, (w = incomingNeg u ∨ w = incomingPos u) ∧ w ∉ squareCorners a b ∧ freeClosure frame w := by
  obtain ⟨s0, hs0, hyF⟩ := hfy
  have hsE : EvenSite s0 := span_even frame hs0
  have hy' : y + s0 ∈ squareCorners (a + s0.1) (b + s0.2) := (shift_mem a b y s0).1 hy
  have hothers' : ∀ c ∈ squareCorners (a + s0.1) (b + s0.2), c ≠ y + s0 → ¬ freeClosure frame c := by
    intro c hc hne hfc
    have hcQ : c - s0 ∈ squareCorners a b := (shift_mem a b (c - s0) s0).2 (by rwa [sub_add_cancel])
    have hcne : c - s0 ≠ y := fun e => hne (by rw [← e]; abel)
    have hfc' : freeClosure frame (c - s0) :=
      (freeClosure_add_span frame hs0 (c - s0)).mp (by rwa [sub_add_cancel])
    exact hothers (c - s0) hcQ hcne hfc'
  obtain ⟨u', hu'Q, hu'ne, hlap', w', hw'eq, hw'Q, hw'fc⟩ := web_core hW hy' hyF hothers'
  have hN := incomingNeg_add_of_even (u' - s0) s0 hsE
  have hP := incomingPos_add_of_even (u' - s0) s0 hsE
  rw [sub_add_cancel] at hN hP
  refine ⟨u' - s0, (shift_mem a b (u' - s0) s0).2 (by rwa [sub_add_cancel]), ?_, ?_, w' - s0, ?_, ?_, ?_⟩
  · intro h
    apply hu'ne
    rw [← sub_add_cancel u' s0, h]
  · have hinv := hW.inv (u' - s0) s0 hs0
    rw [sub_add_cancel] at hinv
    rw [← hinv]
    exact hlap'
  · rcases hw'eq with h | h
    · left
      rw [h, hN]; abel
    · right
      rw [h, hP]; abel
  · intro hm
    apply hw'Q
    have := (shift_mem a b (w' - s0) s0).1 hm
    rwa [sub_add_cancel] at this
  · exact (freeClosure_add_span frame hs0 (w' - s0)).mp (by rwa [sub_add_cancel])

theorem two_eq {N P o' r o : Site} (hNP : N ≠ P) (ho' : o' = N ∨ o' = P) (hr : r = N ∨ r = P)
    (ho : o = N ∨ o = P) (h1 : o' ≠ r) (h2 : r ≠ o) : o' = o := by
  rcases ho' with rfl | rfl <;> rcases hr with rfl | rfl <;> rcases ho with rfl | rfl <;> simp_all

/-- **The induction on the forcing derivation.** Every forced white is nonfree, and its only free input is its forced value. -/
theorem forced_conj {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) (c i : Site)
    (h : ForcedEdge F (fun _ _ => False) c i) :
    ¬ freeClosure frame c ∧ ∀ o : Site, (o = incomingNeg c ∨ o = incomingPos c) → freeClosure frame o → o = i := by
  induction h with
  | seed hs => exact (hs : False).elim
  | @unit a b cc o inside hc hw ho hout hin hforced ih =>
    -- every other corner of the square is nonfree
    have hA : ∀ c' ∈ squareCorners a b, c' ≠ cc → ¬ freeClosure frame c' := by
      intro c' hc' hne hfc
      rcases hin c' hc' hne with hb | ⟨hw', -, -⟩
      · have h0 := white_of_freeClosure hW hfc
        rw [hb] at h0
        norm_num at h0
      · exact (ih c' hc' hne hw').1 hfc
    have hnfc : ¬ freeClosure frame cc := by
      intro hfc
      obtain ⟨u, huQ, hune, hlapu, w, hw_eq, hwQ, hwfc⟩ :=
        web_general hW hc hfc (fun c' hc' hne => hA c' hc' hne)
      rcases hin u huQ hune with hb | ⟨hw_u, hinQ, -⟩
      · rw [hlapu] at hb
        norm_num at hb
      · have hPu := ih u huQ hune hw_u
        have hwi := hPu.2 w hw_eq hwfc
        rw [hwi] at hwQ
        exact hwQ hinQ
    refine ⟨hnfc, ?_⟩
    intro o' ho' hfo'
    obtain ⟨r, hrQ, hr⟩ := square_corner_input a b hc
    have hrne : r ≠ cc := by
      rcases hr with rfl | rfl
      · exact incomingNeg_ne_self cc
      · exact incomingPos_ne_self cc
    have hrfc : ¬ freeClosure frame r := hA r hrQ hrne
    have hro : r ≠ o := fun e => hout (e ▸ hrQ)
    have hop : o' ≠ r := fun e => hrfc (e ▸ hfo')
    exact two_eq (incomingNeg_ne_incomingPos cc) ho' hr ho hop hro

/-- **`hFreeIn` in the W1 form**: a forced white whose input is free forces that input. -/
theorem freeInput_eq {frame : ChildFrame} {F : Field} (hW : WebHyp frame F) {c i o : Site}
    (h : ForcedEdge F (fun _ _ => False) c i) (ho : o = incomingNeg c ∨ o = incomingPos c)
    (hfo : o ∈ frame.freeH ∨ o ∈ frame.freeV) : o = i := by
  have hfc : freeClosure frame o := by
    rcases hfo with hH | hV
    · exact fc_of_freeH frame hH
    · exact fc_of_freeV frame hV
  exact (forced_conj hW c i h).2 o ho hfc

end FLatticePaper.ProtectedWeb
