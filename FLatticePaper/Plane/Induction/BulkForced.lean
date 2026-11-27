import FLatticePaper.Plane.Induction.ProtectedWeb
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.BaseGeometry

/-! # Strict representatives of deck classes (Q39 §5, the representative lift of the passage)

For a child frame with `0 < n < d` (child `n/d`), the strict interior `E° = StrictInterior` contains at most one point of each
deck class `z + span`: a strict site and a closed-polygon site that differ by a span vector coincide. The proof is arithmetic:
the grade differences of a span vector are `(t, s) ↦ (−jT, iT)` with `T = d² + 2dn − n²`, and the strict and closed windows
have `t`- and `s`-widths below `T`. -/

namespace FLatticePaper.BulkForced

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure FLatticePaper.SquareClauses
  FLatticePaper.AndOrRank

theorem modDeck_kernel (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  have hm : frame.child.periodMultiplicity = 1 := by
    have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    unfold Fraction.periodMultiplicity
    rw [if_pos hpar]
  simp only [Fraction.modifiedDeck, hm, one_mul]

theorem modDeck_transverse (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

theorem combine_modified (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  unfold PeriodDeck.combine
  rw [modDeck_kernel, modDeck_transverse]

/-- Parity is unchanged by an even shift. -/
theorem evenSite_add_even (p c : Site) (hc : EvenSite c) : EvenSite (p + c) ↔ EvenSite p := by
  unfold EvenSite at *
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- A nonzero multiple of a positive `T` cannot lie strictly between `−T` and `T`. -/
theorem zero_of_mul_bounds (j T : ℤ) (hT : 0 < T) (h1 : -T < j * T) (h2 : j * T < T) : j = 0 := by
  have hj1 : j < 1 := by
    by_contra h
    have h' : 1 ≤ j := not_lt.mp h
    nlinarith
  have hj2 : -1 < j := by
    by_contra h
    have h' : j ≤ -1 := not_lt.mp h
    nlinarith
  omega

/-- **Uniqueness of strict representatives.** A closed-polygon site and a strict interior site that differ by a span vector
are equal. -/
theorem strict_span_zero (frame : ChildFrame) {p q : Site} (hp : p ∈ frame.closedPolygon)
    (hq : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den q)
    (hw : q - p ∈ frame.child.modifiedDeck.span) : q = p := by
  obtain ⟨i, j, hij⟩ := hw
  have hqp : q = p + frame.child.modifiedDeck.combine i j := by
    rw [← hij]
    abel
  have hsp : EvenSite (frame.child.modifiedDeck.combine i j) :=
    ProtectedWeb.span_even frame ⟨i, j, rfl⟩
  have hqe : EvenSite q ↔ EvenSite p := by
    rw [hqp]
    exact evenSite_add_even p _ hsp
  rw [FLatticePaper.W1.closedPolygon_eq_closedRect] at hp
  have hp' : FLatticePaper.W1.closedRect frame.child.num frame.child.den p := hp
  rw [combine_modified] at hqp
  have hq1 : q.1 = p.1 + (i * frame.child.den + j * (frame.child.num - frame.child.den)) := by
    have := congrArg Prod.fst hqp
    simpa using this
  have hq2 : q.2 = p.2 + (i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
    have := congrArg Prod.snd hqp
    simpa using this
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hT : 0 < frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    nlinarith
  have htq : frame.child.num * q.1 - frame.child.den * q.2 =
      (frame.child.num * p.1 - frame.child.den * p.2) -
        j * (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) := by
    rw [hq1, hq2]
    ring
  have hsq : (frame.child.den + frame.child.num) * q.1 + (frame.child.den - frame.child.num) * q.2 =
      ((frame.child.den + frame.child.num) * p.1 + (frame.child.den - frame.child.num) * p.2) +
        i * (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) := by
    rw [hq1, hq2]
    ring
  unfold FLatticePaper.W1.StrictInterior at hq
  by_cases hpe : EvenSite p
  · have hqe' : EvenSite q := hqe.mpr hpe
    unfold FLatticePaper.W1.closedRect at hp'
    simp only [FLatticePaper.W1.w1a, FLatticePaper.W1.w1b, FLatticePaper.W1.w1c, FLatticePaper.W1.w1h,
      FLatticePaper.W1.w1t, FLatticePaper.W1.w1s, FLatticePaper.W1.w1T, if_pos hpe, if_pos hqe'] at hp' hq
    have hi : i = 0 := by
      apply zero_of_mul_bounds i _ hT
      · linarith [hq.2.2.1, hp'.2.2.2, hsq]
      · linarith [hq.2.2.2, hp'.2.2.1, hsq]
    have hj : j = 0 := by
      apply zero_of_mul_bounds j _ hT
      · linarith [hq.2.1, hp'.1, htq]
      · linarith [hq.1, hp'.2.1, htq]
    subst hi
    subst hj
    rw [hqp]
    simp
  · have hqe' : ¬ EvenSite q := fun h => hpe (hqe.mp h)
    unfold FLatticePaper.W1.closedRect at hp'
    simp only [FLatticePaper.W1.w1a, FLatticePaper.W1.w1b, FLatticePaper.W1.w1c, FLatticePaper.W1.w1h,
      FLatticePaper.W1.w1t, FLatticePaper.W1.w1s, FLatticePaper.W1.w1T, if_neg hpe, if_neg hqe'] at hp' hq
    have hi : i = 0 := by
      apply zero_of_mul_bounds i _ hT
      · linarith [hq.2.2.1, hp'.2.2.2, hsq]
      · linarith [hq.2.2.2, hp'.2.2.1, hsq]
    have hj : j = 0 := by
      apply zero_of_mul_bounds j _ hT
      · linarith [hq.2.1, hp'.1, htq]
      · linarith [hq.1, hp'.2.1, htq]
    subst hi
    subst hj
    rw [hqp]
    simp


/-! ## Representative shifts and bulk selections (Q39 §5) -/

theorem span_sub_mem (frame : ChildFrame) {a b : Site} (ha : a ∈ frame.child.modifiedDeck.span)
    (hb : b ∈ frame.child.modifiedDeck.span) : a - b ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := ha
  obtain ⟨k, l, rfl⟩ := hb
  exact ⟨i - k, j - l, by ext <;> simp [PeriodDeck.combine] <;> ring⟩

theorem nonfree_iff_not_freeClosure (frame : ChildFrame) (c : Site) :
    Nonfree frame c ↔ ¬ freeClosure frame c := by
  constructor
  · intro h hfc
    obtain ⟨s, hs, hm⟩ := hfc
    rcases hm with hm | hm
    · exact h s hs (Set.mem_union_left _ hm)
    · exact h s hs (Set.mem_union_right _ hm)
  · intro h v hv hmem
    exact h ⟨v, hv, (Set.mem_union _ _ _).mp hmem⟩

theorem incomingNeg_add (x c : Site) (hc : EvenSite c) : incomingNeg (x + c) = incomingNeg x + c := by
  unfold incomingNeg
  by_cases hx : EvenSite x
  · have hxc : EvenSite (x + c) := (evenSite_add_even x c hc).mpr hx
    rw [if_pos hx, if_pos hxc]
    ext <;> simp [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · have hxc : ¬ EvenSite (x + c) := fun h => hx ((evenSite_add_even x c hc).mp h)
    rw [if_neg hx, if_neg hxc]
    ext <;> simp [Prod.fst_add, Prod.snd_add]
    all_goals ring

theorem incomingPos_add (x c : Site) (hc : EvenSite c) : incomingPos (x + c) = incomingPos x + c := by
  unfold incomingPos
  by_cases hx : EvenSite x
  · have hxc : EvenSite (x + c) := (evenSite_add_even x c hc).mpr hx
    rw [if_pos hx, if_pos hxc]
    ext <;> simp [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · have hxc : ¬ EvenSite (x + c) := fun h => hx ((evenSite_add_even x c hc).mp h)
    rw [if_neg hx, if_neg hxc]
    ext <;> simp [Prod.fst_add, Prod.snd_add]
    all_goals ring

theorem incomingNeg_ne_incomingPos (x : Site) : incomingNeg x ≠ incomingPos x := by
  unfold incomingNeg incomingPos
  split_ifs <;> simp [Prod.ext_iff] <;> omega

open Classical in
/-- The strict representative shift of a site: a span vector bringing it into `E°` (unique when it exists). -/
noncomputable def repShift (frame : ChildFrame) (c : Site) : Site :=
  if h : ∃ v ∈ frame.child.modifiedDeck.span,
      FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (c + v) then Classical.choose h else 0

theorem repShift_spec (frame : ChildFrame) {c : Site} (hc : Nonfree frame c) :
    repShift frame c ∈ frame.child.modifiedDeck.span ∧
      FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (c + repShift frame c) := by
  have h := nonfree_bridge frame c hc
  unfold repShift
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem repShift_eq (frame : ChildFrame) {c v : Site} (hv : v ∈ frame.child.modifiedDeck.span)
    (hsi : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (c + v)) :
    repShift frame c = v := by
  have h : ∃ w ∈ frame.child.modifiedDeck.span,
      FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (c + w) := ⟨v, hv, hsi⟩
  unfold repShift
  rw [dif_pos h]
  obtain ⟨hw, hsw⟩ := Classical.choose_spec h
  have hp : c + v ∈ frame.closedPolygon := (TransferW1.strictInterior_star frame hsi).1
  have hd : (c + Classical.choose h) - (c + v) ∈ frame.child.modifiedDeck.span := by
    have e : (c + Classical.choose h) - (c + v) = Classical.choose h - v := by abel
    rw [e]
    exact span_sub_mem frame hw hv
  exact add_left_cancel (strict_span_zero frame hp hsw hd)

theorem repShift_of_input (frame : ChildFrame) {x y : Site} (hx : Nonfree frame x) (hy : Nonfree frame y)
    (hadj : y = incomingNeg x ∨ y = incomingPos x) : repShift frame x = repShift frame y := by
  obtain ⟨hvx, hsx⟩ := repShift_spec frame hx
  obtain ⟨hvy, hsy⟩ := repShift_spec frame hy
  have hst := TransferW1.strictInterior_star frame hsx
  have hp : y + repShift frame x ∈ frame.closedPolygon := by
    rcases hadj with h | h
    · rw [h, ← incomingNeg_add x _ (ProtectedWeb.span_even frame hvx)]
      exact hst.2.1
    · rw [h, ← incomingPos_add x _ (ProtectedWeb.span_even frame hvx)]
      exact hst.2.2
  have hd : (y + repShift frame y) - (y + repShift frame x) ∈ frame.child.modifiedDeck.span := by
    have e : (y + repShift frame y) - (y + repShift frame x) = repShift frame y - repShift frame x := by abel
    rw [e]
    exact span_sub_mem frame hvy hvx
  exact (add_left_cancel (strict_span_zero frame hp hsy hd)).symm

theorem adj_east (a b : ℤ) : (a + 1, b) = incomingPos (a, b) ∨ (a, b) = incomingNeg (a + 1, b) := by
  unfold incomingPos incomingNeg EvenSite
  split_ifs <;> simp_all
  all_goals omega

theorem adj_north (a b : ℤ) : (a, b + 1) = incomingPos (a, b) ∨ (a, b) = incomingNeg (a, b + 1) := by
  unfold incomingPos incomingNeg EvenSite
  split_ifs <;> simp_all
  all_goals omega

/-- The four corners of a unit square share one strict representative shift when all four are nonfree. -/
theorem repShift_square (frame : ChildFrame) {a b : ℤ} (hQ : ∀ x ∈ squareCorners a b, Nonfree frame x) :
    ∀ x ∈ squareCorners a b, repShift frame x = repShift frame (a, b) := by
  have h00 : (a, b) ∈ squareCorners a b := by simp [squareCorners]
  have h10 : (a + 1, b) ∈ squareCorners a b := by simp [squareCorners]
  have h01 : (a, b + 1) ∈ squareCorners a b := by simp [squareCorners]
  have h11 : (a + 1, b + 1) ∈ squareCorners a b := by simp [squareCorners]
  have e10 : repShift frame (a, b) = repShift frame (a + 1, b) := by
    rcases adj_east a b with h | h
    · exact repShift_of_input frame (hQ _ h00) (hQ _ h10) (Or.inr h)
    · exact (repShift_of_input frame (hQ _ h10) (hQ _ h00) (Or.inl h)).symm
  have e01 : repShift frame (a, b) = repShift frame (a, b + 1) := by
    rcases adj_north a b with h | h
    · exact repShift_of_input frame (hQ _ h00) (hQ _ h01) (Or.inr h)
    · exact (repShift_of_input frame (hQ _ h01) (hQ _ h00) (Or.inl h)).symm
  have e11 : repShift frame (a + 1, b) = repShift frame (a + 1, b + 1) := by
    rcases adj_north (a + 1) b with h | h
    · exact repShift_of_input frame (hQ _ h10) (hQ _ h11) (Or.inr h)
    · exact (repShift_of_input frame (hQ _ h11) (hQ _ h10) (Or.inl h)).symm
  have e11' : repShift frame (a, b + 1) = repShift frame (a + 1, b + 1) := by
    rcases adj_east a (b + 1) with h | h
    · exact repShift_of_input frame (hQ _ h01) (hQ _ h11) (Or.inr h)
    · exact (repShift_of_input frame (hQ _ h11) (hQ _ h01) (Or.inl h)).symm
  intro x hx
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rfl
  · exact e10.symm
  · exact e01.symm
  · exact (e11'.symm.trans e01.symm)

/-- The bulk selection: the selection of `M` transported to the representative of each site. -/
noncomputable def bulkSel (frame : ChildFrame) (sel : Site → Site) (c : Site) : Site :=
  sel (c + repShift frame c) - repShift frame c

/-- A clause of the shifted square is a clause of the translated selection on the square. -/
theorem not_all_kept_translate (F : Field) (sel : Site → Site) (v : Site) (hv : EvenSite v)
    (hLap : ∀ c, laplacian F (c + v) = laplacian F c) (a b : ℤ)
    (hS : SquareClauseSat F sel (a + v.1) (b + v.2)) :
    ¬ ∀ c ∈ squareCorners a b, keptInside F (fun z => sel (z + v) - v) (squareCorners a b) c := by
  intro H
  apply hS
  intro y hy
  obtain ⟨z, rfl⟩ : ∃ z, y = z + v := ⟨y - v, by abel⟩
  have hz : z ∈ squareCorners a b := (mem_corners_translate a b v z).mp hy
  have Hz := H z hz
  unfold keptInside at Hz ⊢
  rw [hLap z]
  by_cases hl : laplacian F z = -1
  · rw [if_pos hl] at Hz ⊢
    rw [incomingNeg_add z v hv, incomingPos_add z v hv]
    rcases Hz with h | h
    · exact Or.inl ((mem_corners_translate a b v _).mpr h)
    · exact Or.inr ((mem_corners_translate a b v _).mpr h)
  · rw [if_neg hl] at Hz ⊢
    have h2 := (mem_corners_translate a b v (sel (z + v) - v)).mpr Hz
    rwa [sub_add_cancel] at h2

/-- A clause of `M` is a clause of `F` on squares whose corners have equal Laplacians. -/
theorem clause_of_agree {F M : Field} {sel : Site → Site} {a b : ℤ}
    (hl : ∀ c ∈ squareCorners a b, laplacian F c = laplacian M c)
    (h : SquareClauseSat M sel a b) : SquareClauseSat F sel a b := by
  intro H
  apply h
  intro c hc
  have hk := H c hc
  unfold keptInside at hk ⊢
  rw [← hl c hc]
  exact hk

theorem lap_agree_star (frame : ChildFrame) {F M : Field} (hFM : ∀ z ∈ frame.closedPolygon, F z = M z)
    {c : Site} (hc : c ∈ frame.closedPolygon ∧ incomingNeg c ∈ frame.closedPolygon ∧ incomingPos c ∈ frame.closedPolygon) :
    laplacian F c = laplacian M c := by
  obtain ⟨h1, h2, h3⟩ := hc
  unfold laplacian
  rw [hFM _ h1, hFM _ h2, hFM _ h3]

theorem eq_of_two_inputs {o i' B P Q : Site} (ho : o = P ∨ o = Q) (hi : i' = P ∨ i' = Q)
    (hB : B = P ∨ B = Q) (hoi : o ≠ i') (hBi : B ≠ i') : o = B := by
  rcases ho with h1 | h1 <;> rcases hi with h2 | h2 <;> rcases hB with h3 | h3 <;> simp_all

/-- **Forced-output uniqueness (Q39 §5).** Every unseeded forced white of `F` is nonfree, and its forced input is the bulk
selection of its representative. -/
theorem forced_bulk (frame : ChildFrame) {F M : Field} (hW : ProtectedWeb.WebHyp frame F)
    (hFM : ∀ z ∈ frame.closedPolygon, F z = M z) (sel : Site → Site)
    (hselM : ∀ c, laplacian M c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hsqM : ∀ a b : ℤ, SquareClauseSat M sel a b) :
    ∀ c i : Site, SquareClauses.ForcedEdge F (fun _ _ => False) c i →
      Nonfree frame c ∧ i = bulkSel frame sel c := by
  intro c i h
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b cc oo inside hc hw ho hout hin hforced ih =>
    -- the other corners are not free
    have hother : ∀ c' ∈ squareCorners a b, c' ≠ cc → ¬ freeClosure frame c' := by
      intro c' hc' hne hfc
      rcases hin c' hc' hne with hb | ⟨hwh, _, _⟩
      · have h0 := ProtectedWeb.white_of_freeClosure hW hfc
        rw [hb] at h0
        norm_num at h0
      · exact (nonfree_iff_not_freeClosure frame c').mp (ih c' hc' hne hwh).1 hfc
    -- the forced white is nonfree: a free forced white contradicts the protected web lemma
    have hcnf : Nonfree frame cc := by
      rw [nonfree_iff_not_freeClosure]
      intro hfc
      obtain ⟨u, huQ, hune, hlu, w, hwin, hwQ, hwfc⟩ := ProtectedWeb.web_general hW hc hfc hother
      rcases hin u huQ hune with hb | ⟨_, hiQ, _⟩
      · rw [hb] at hlu
        norm_num at hlu
      · have hfu := hforced u huQ hune hlu
        have hcon := (ProtectedWeb.forced_conj hW u _ hfu).2 w hwin hwfc
        rw [hcon] at hwQ
        exact hwQ hiQ
    -- all four corners are nonfree
    have hallnf : ∀ c' ∈ squareCorners a b, Nonfree frame c' := by
      intro c' hc'
      by_cases hcc : c' = cc
      · rw [hcc]
        exact hcnf
      · rcases hin c' hc' hcc with hb | ⟨hwh, _, _⟩
        · rw [nonfree_iff_not_freeClosure]
          intro hfc
          have h0 := ProtectedWeb.white_of_freeClosure hW hfc
          rw [hb] at h0
          norm_num at h0
        · exact (ih c' hc' hcc hwh).1
    have hrep := repShift_square frame hallnf
    have hcQ : cc ∈ squareCorners a b := hc
    have hv0 : repShift frame (a, b) ∈ frame.child.modifiedDeck.span :=
      (repShift_spec frame (hallnf (a, b) (by simp [squareCorners]))).1
    have hvEven : EvenSite (repShift frame (a, b)) := ProtectedWeb.span_even frame hv0
    have hLap : ∀ z, laplacian F (z + repShift frame (a, b)) = laplacian F z :=
      fun z => hW.inv z _ hv0
    -- the translated square carries the clause of `sel`
    have hS' : SquareClauseSat F sel (a + (repShift frame (a, b)).1) (b + (repShift frame (a, b)).2) := by
      refine clause_of_agree (M := M) ?_ (hsqM _ _)
      intro x hx
      have hz : x - repShift frame (a, b) ∈ squareCorners a b :=
        (mem_corners_translate a b (repShift frame (a, b)) (x - repShift frame (a, b))).mp
          (by rw [sub_add_cancel]; exact hx)
      have hsi := (repShift_spec frame (hallnf _ hz)).2
      rw [hrep _ hz, sub_add_cancel] at hsi
      exact lap_agree_star frame hFM (TransferW1.strictInterior_star frame hsi)
    have hnot := not_all_kept_translate F sel _ hvEven hLap a b hS'
    -- the corners of the square are white or black, and the bulk value of each white corner is in the square
    have hwb : ∀ c' ∈ squareCorners a b, laplacian F c' = -1 ∨ laplacian F c' = 0 := by
      intro c' hc'
      by_cases hcc : c' = cc
      · rw [hcc]
        exact Or.inr hw
      · rcases hin c' hc' hcc with hb | ⟨hwh, _, _⟩
        · exact Or.inl hb
        · exact Or.inr hwh
    have hbc : ∀ c' ∈ squareCorners a b, bulkSel frame sel c' = sel (c' + repShift frame (a, b)) - repShift frame (a, b) := by
      intro c' hc'
      unfold bulkSel
      rw [hrep c' hc']
    -- the bulk value of the forced white is not in the square
    have hbulk_notin : bulkSel frame sel cc ∉ squareCorners a b := by
      intro hin_b
      apply hnot
      intro c' hc'
      by_cases hl : laplacian F c' = -1
      · exact keptInside_of_black hc' hl
      · have hwhite : laplacian F c' = 0 := (hwb c' hc').resolve_left hl
        have hbs : bulkSel frame sel c' ∈ squareCorners a b := by
          by_cases hcc : c' = cc
          · rw [hcc]
            exact hin_b
          · rcases hin c' hc' hcc with hb | ⟨_, hiS, _⟩
            · exact absurd hb hl
            · have hcon := (ih c' hc' hcc hwhite).2
              rw [← hcon]
              exact hiS
        unfold keptInside
        rw [if_neg hl]
        show sel (c' + repShift frame (a, b)) - repShift frame (a, b) ∈ squareCorners a b
        rw [← hbc c' hc']
        exact hbs
    -- the bulk value is an input of the forced white
    have hbulk_input : bulkSel frame sel cc = incomingNeg cc ∨ bulkSel frame sel cc = incomingPos cc := by
      have hSIv := (repShift_spec frame (hallnf cc hcQ)).2
      rw [hrep cc hcQ] at hSIv
      have hstar := lap_agree_star frame hFM (TransferW1.strictInterior_star frame hSIv)
      have hM0 : laplacian M (cc + repShift frame (a, b)) = 0 := by
        rw [← hstar, hW.inv cc _ hv0, hw]
      have hsc := hselM _ hM0
      unfold bulkSel
      rw [hrep cc hcQ]
      rcases hsc with h | h
      · left
        rw [h, incomingNeg_add cc _ hvEven, add_sub_cancel_right]
      · right
        rw [h, incomingPos_add cc _ hvEven, add_sub_cancel_right]
    obtain ⟨i', hi'S, hi'in⟩ := square_corner_input a b hc
    exact ⟨hcnf, eq_of_two_inputs ho hi'in hbulk_input
      (fun h => hout (by rw [h]; exact hi'S)) (fun h => hbulk_notin (by rw [h]; exact hi'S))⟩

end FLatticePaper.BulkForced
