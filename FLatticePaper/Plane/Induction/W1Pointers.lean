import FLatticePaper.Plane.Induction.W1Ties
import FLatticePaper.Plane.Induction.SheetReflection
import FLatticePaper.Plane.Induction.I3Permits
import FLatticePaper.Plane.Induction.SheetMinRank
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.W1Exit

/-! Task 62 (1): the §5 pointers from the sheet policies, and the tie consequences (W1_CONSTRUCTOR §5).

* Translation by an even vector and reflection about an even centre commute with the input pairs (`incomingNeg`, `incomingPos`),
  so the laplacian and the quota transfer (`laplacian_translate`, `laplacian_reflect`, `reflect_quota`, `translate_quota`).
* The A-sheet `sheetA Fp = Fp(· − lv)` and the C-sheet `sheetC Fp (z) = sheetA Fp (centre − z) + (t z − κ)` (`SheetExchange`) carry the
  quota of the transported policy `Q`: `sheetA_quota`, `sheetC_quota`.
* A pointer of a site is one of its inputs that the policy retains (`pointerOf`); a sign-directed pointer (A on `Ψ ≥ 0`, C on
  `Ψ < 0`) is retained by its sheet's policy (`arrowOut`).
* At a tie (`Ψ(c) = 0`) with `F` white both parents are white (`tie_parents_white`), and the inputs of a tie are ties
  (`tie_inputs_tie`). The monotonicity of the matched policies gives nothing more at a tie: the A-policy needs `Ψ(i) ≥ 0` and the
  C-policy `Ψ(i) ≤ 0`, both already given by the tied inputs. So the agreement of the two arrows at ties is NOT a consequence of the
  monotonicity; it needs the rank descent of §5 (the archive's recurrence argument), which is a named hypothesis here. -/

namespace FLatticePaper.W1Pointers

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- The two inputs of a translated site: translation by an even vector commutes with `incomingNeg` and `incomingPos`. -/
theorem incomingNeg_sub_even (c v : Site) (hv : EvenSite v) :
    incomingNeg (c - v) = incomingNeg c - v := by
  unfold EvenSite at hv
  unfold incomingNeg EvenSite
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases hc : (c.1 + c.2) % 2 = 0
  · have h1 : (c.1 - v.1 + (c.2 - v.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_true]
    ext
    all_goals simp
    all_goals omega
  · have h1 : ¬ (c.1 - v.1 + (c.2 - v.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_false]
    ext
    all_goals simp
    all_goals omega

theorem incomingPos_sub_even (c v : Site) (hv : EvenSite v) :
    incomingPos (c - v) = incomingPos c - v := by
  unfold EvenSite at hv
  unfold incomingPos EvenSite
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases hc : (c.1 + c.2) % 2 = 0
  · have h1 : (c.1 - v.1 + (c.2 - v.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_true]
    ext
    all_goals simp
    all_goals omega
  · have h1 : ¬ (c.1 - v.1 + (c.2 - v.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_false]
    ext
    all_goals simp
    all_goals omega

/-- A reflection about an even centre exchanges the two inputs. -/
theorem refl_neg_pos (R c : Site) (hR : EvenSite R) :
    R - incomingNeg c = incomingPos (R - c) ∧ R - incomingPos c = incomingNeg (R - c) := by
  unfold EvenSite at hR
  unfold incomingNeg incomingPos EvenSite
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases hc : (c.1 + c.2) % 2 = 0
  · have h1 : (R.1 - c.1 + (R.2 - c.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_true]
    constructor
    all_goals ext
    all_goals simp
    all_goals omega
  · have h1 : ¬ (R.1 - c.1 + (R.2 - c.2)) % 2 = 0 := by omega
    simp only [h1, hc, if_false]
    constructor
    all_goals ext
    all_goals simp
    all_goals omega

theorem laplacian_translate (G : Field) (v c : Site) (hv : EvenSite v) :
    laplacian (fun z => G (z - v)) c = laplacian G (c - v) := by
  simp only [laplacian, incomingNeg_sub_even c v hv, incomingPos_sub_even c v hv]

theorem laplacian_reflect (G : Field) (R c : Site) (hR : EvenSite R) :
    laplacian (fun z => G (R - z)) c = laplacian G (R - c) := by
  simp only [laplacian]
  obtain ⟨h1, h2⟩ := refl_neg_pos R c hR
  rw [h1, h2]
  ring

/-- The laplacian of an affine function vanishes (the two inputs of a site average to the site). -/
theorem laplacian_affine (a b k : ℤ) (c : Site) :
    laplacian (fun z => a * z.1 + b * z.2 + k) c = 0 := by
  unfold laplacian incomingNeg incomingPos
  split_ifs <;> simp <;> ring

theorem laplacian_add (f g : Site → ℤ) (c : Site) :
    laplacian (fun z => f z + g z) c = laplacian f c + laplacian g c := by
  unfold laplacian
  ring

/-- Translation by an even vector transports a quota policy. -/
theorem translate_quota (G : Field) (Q : Site → Site → Prop) (v : Site) (hv : EvenSite v)
    (hq : RetainQuota G Q) :
    RetainQuota (fun z => G (z - v)) (fun c i => Q (c - v) (i - v)) := by
  constructor
  · intro c hc
    rw [laplacian_translate G v c hv] at hc
    obtain ⟨h1, h2⟩ := hq.1 (c - v) hc
    rw [incomingNeg_sub_even c v hv] at h1
    rw [incomingPos_sub_even c v hv] at h2
    exact ⟨h1, h2⟩
  · intro c hc
    rw [laplacian_translate G v c hv] at hc
    rcases hq.2 (c - v) hc with h | h
    · left
      rw [incomingNeg_sub_even c v hv] at h
      exact h
    · right
      rw [incomingPos_sub_even c v hv] at h
      exact h

/-- Reflection about an even centre transports a quota policy, with the two inputs exchanged. -/
theorem reflect_quota (G : Field) (Q : Site → Site → Prop) (R : Site) (hR : EvenSite R)
    (hq : RetainQuota G Q) :
    RetainQuota (fun z => G (R - z)) (fun c i => Q (R - c) (R - i)) := by
  constructor
  · intro c hc
    rw [laplacian_reflect G R c hR] at hc
    obtain ⟨h1, h2⟩ := hq.1 (R - c) hc
    obtain ⟨e1, e2⟩ := refl_neg_pos R c hR
    show Q (R - c) (R - incomingNeg c) ∧ Q (R - c) (R - incomingPos c)
    rw [e1, e2]
    exact ⟨h2, h1⟩
  · intro c hc
    rw [laplacian_reflect G R c hR] at hc
    rcases hq.2 (R - c) hc with h | h
    · right
      obtain ⟨e1, e2⟩ := refl_neg_pos R c hR
      show Q (R - c) (R - incomingPos c)
      rw [e2]
      exact h
    · left
      obtain ⟨e1, e2⟩ := refl_neg_pos R c hR
      show Q (R - c) (R - incomingNeg c)
      rw [e1]
      exact h

/-- A field with the same laplacian carries the same quota policy. -/
theorem retainQuota_of_laplacian_eq (F F' : Field) (Q : Site → Site → Prop)
    (hF : ∀ c, laplacian F' c = laplacian F c) (hq : RetainQuota F Q) : RetainQuota F' Q := by
  constructor
  · intro c hc
    exact hq.1 c (by rw [← hF c]; exact hc)
  · intro c hc
    exact hq.2 c (by rw [← hF c]; exact hc)

/-- The pointer of a site under a policy: the negative input when retained, else the positive one. -/
noncomputable def pointerOf (Q : Site → Site → Prop) (c : Site) : Site := by
  classical
  exact if Q c (incomingNeg c) then incomingNeg c else incomingPos c

theorem pointerOf_input (Q : Site → Site → Prop) (c : Site) :
    pointerOf Q c = incomingNeg c ∨ pointerOf Q c = incomingPos c := by
  unfold pointerOf
  split_ifs <;> simp

/-- A pointer is retained by the policy when the field is binary and the policy has the quota. -/
theorem pointerOf_retained (F : Field) (Q : Site → Site → Prop) (hq : RetainQuota F Q) (c : Site)
    (hbin : laplacian F c = -1 ∨ laplacian F c = 0) : Q c (pointerOf Q c) := by
  unfold pointerOf
  split_ifs with h
  · exact h
  · rcases hbin with hb | hb
    · exact (hq.1 c hb).2
    · rcases hq.2 c hb with h' | h'
      · exact absurd h' h
      · exact h'

/-- The sign-directed arrow: the A pointer on `Ψ ≥ 0` and the C pointer on `Ψ < 0`. -/
noncomputable def arrowOut (Ψ : Site → ℤ) (QA QC : Site → Site → Prop) (c : Site) : Site := by
  classical
  exact if 0 ≤ Ψ c then pointerOf QA c else pointerOf QC c

theorem arrowOut_input (Ψ : Site → ℤ) (QA QC : Site → Site → Prop) (c : Site) :
    arrowOut Ψ QA QC c = incomingNeg c ∨ arrowOut Ψ QA QC c = incomingPos c := by
  unfold arrowOut
  split_ifs
  · exact pointerOf_input QA c
  · exact pointerOf_input QC c

/-- The sign-directed arrow is retained by the policy of its sign. -/
theorem arrowOut_retained (Ψ : Site → ℤ) (FA FC : Field) (QA QC : Site → Site → Prop)
    (hqA : RetainQuota FA QA) (hqC : RetainQuota FC QC) (c : Site)
    (hbA : laplacian FA c = -1 ∨ laplacian FA c = 0) (hbC : laplacian FC c = -1 ∨ laplacian FC c = 0) :
    (0 ≤ Ψ c → QA c (arrowOut Ψ QA QC c)) ∧ (¬ 0 ≤ Ψ c → QC c (arrowOut Ψ QA QC c)) := by
  constructor
  · intro h
    unfold arrowOut
    simp only [h, if_true]
    exact pointerOf_retained FA QA hqA c hbA
  · intro h
    unfold arrowOut
    simp only [h, if_false]
    exact pointerOf_retained FC QC hqC c hbC

/-- At a tie with `F` white, the parents are white: `lap A c = lap C c = lap F c`. -/
theorem tie_parents_white (A C F : Site → ℤ) (c : Site)
    (htie : A c = C c) (hFc : F c = min (A c) (C c))
    (hFi : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → F i = min (A i) (C i))
    (hΨ : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) →
      (C i - A i) - (C c - A c) ≤ 1 ∧ (C c - A c) - (C i - A i) ≤ 1)
    (hA : laplacian A c = -1 ∨ laplacian A c = 0) (hC : laplacian C c = -1 ∨ laplacian C c = 0)
    (hw : laplacian F c = 0) :
    laplacian A c = 0 ∧ laplacian C c = 0 := by
  have hti := FLatticePaper.W1Ties.tie_inputs_of_white A C F c hA hC htie hFc hFi hΨ hw
  have h1 := hFi (incomingNeg c) (Or.inl rfl)
  have h2 := hFi (incomingPos c) (Or.inr rfl)
  have t1 := hti (incomingNeg c) (Or.inl rfl)
  have t2 := hti (incomingPos c) (Or.inr rfl)
  unfold laplacian at hw hA hC ⊢
  constructor <;> omega

/-- A tie's inputs are ties (the A-private return of §5 stays on `Ψ = 0`). -/
theorem tie_inputs_tie (A C F : Site → ℤ) (c : Site)
    (htie : A c = C c) (hFc : F c = min (A c) (C c))
    (hFi : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → F i = min (A i) (C i))
    (hA : laplacian A c = -1 ∨ laplacian A c = 0) (hC : laplacian C c = -1 ∨ laplacian C c = 0)
    (hΨ : ∀ i, (i = incomingNeg c ∨ i = incomingPos c) →
      (C i - A i) - (C c - A c) ≤ 1 ∧ (C c - A c) - (C i - A i) ≤ 1)
    (hw : laplacian F c = 0) :
    ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → C i - A i = C c - A c :=
  FLatticePaper.W1Ties.tie_inputs_of_white A C F c hA hC htie hFc hFi hΨ hw

/-! ### The sheets of a child frame: the quotas of `sheetA` and `sheetC` -/

theorem laplacian_tGrade_sub (frame : ChildFrame) (k : ℤ) (c : Site) :
    laplacian (fun z => frame.tGrade z - k) c = 0 := by
  have hf : (fun z => frame.tGrade z - k) =
      fun z => frame.child.num * z.1 + (-frame.child.den) * z.2 + (-k) := by
    funext z
    unfold ChildFrame.tGrade
    ring
  rw [hf]
  exact laplacian_affine _ _ _ c

theorem centre_even (frame : ChildFrame) : EvenSite frame.centre := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  unfold ChildFrame.centre
  rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The A-sheet carries the quota of the transported policy `Q`, shifted by the even `sheetShift`. -/
theorem sheetA_retainQuota (frame : ChildFrame) (Fp : Field) (Q : Site → Site → Prop) (hq : RetainQuota Fp Q) :
    RetainQuota (fun z => frame.sheetA Fp z)
      (fun c i => Q (c - frame.sheetShift) (i - frame.sheetShift)) :=
  translate_quota Fp Q frame.sheetShift frame.evenSite_sheetShift hq

/-- The C-sheet carries the quota of the reflected A-policy: `C(z) = A(centre − z) + (t z − κ)` (`SheetExchange`). -/
theorem sheetC_retainQuota (frame : ChildFrame) (Fp : Field) (Q : Site → Site → Prop) (hq : RetainQuota Fp Q)
    (hX : frame.SheetExchange Fp) :
    RetainQuota (fun z => frame.sheetC Fp z)
      (fun c i => Q (frame.centre - c - frame.sheetShift) (frame.centre - i - frame.sheetShift)) := by
  have hA := sheetA_retainQuota frame Fp Q hq
  have hRA := reflect_quota (fun z => frame.sheetA Fp z)
    (fun c i => Q (c - frame.sheetShift) (i - frame.sheetShift)) frame.centre (centre_even frame) hA
  refine retainQuota_of_laplacian_eq (fun z => frame.sheetA Fp (frame.centre - z)) (fun z => frame.sheetC Fp z) _
    ?_ hRA
  intro c
  have hfun : (fun z => frame.sheetC Fp z) =
      fun z => (fun w => frame.sheetA Fp (frame.centre - w)) z + (frame.tGrade z - frame.symmetryConstant) := by
    funext z
    have h := hX.1 z
    simp only
    linarith
  rw [hfun, laplacian_add, laplacian_tGrade_sub, add_zero]

/-- The sign difference `Ψ = C − A` of a child frame. -/
def psiDiff (frame : ChildFrame) (Fp : Field) (z : Site) : ℤ :=
  frame.sheetC Fp z - frame.sheetA Fp z

/-- The sign-directed arrow of a child frame: the A pointer on `Ψ ≥ 0` and the C pointer on `Ψ < 0`, both transported from the
policies `Q` by the sheet shift and the reflection. -/
noncomputable def sheetArrow (frame : ChildFrame) (Fp : Field) (Q : Site → Site → Prop) (c : Site) : Site :=
  arrowOut (psiDiff frame Fp)
    (fun c i => Q (c - frame.sheetShift) (i - frame.sheetShift))
    (fun c i => Q (frame.centre - c - frame.sheetShift) (frame.centre - i - frame.sheetShift)) c


end FLatticePaper.W1Pointers
