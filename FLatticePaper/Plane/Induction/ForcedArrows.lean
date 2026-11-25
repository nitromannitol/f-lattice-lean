import FLatticePaper.Plane.Induction.RegionalCompat
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.StrictNonfree

/-! # Forced arrows at nonfree whites (Q32 even H and V steps, the generic forcing lemmas)

* `forced_to_free_input` (source §A, "a nonfree white adjacent along its input edge to a free white cannot be forced to reject that
  input"): a white nonfree `x` whose input `u` is not nonfree is forced to `u`.
* `forced_two_chain` (the two-site region, source §C.2 with the exit): a white nonfree `x` whose white input `y` has a non-nonfree
  input `w ≠ x` is forced to `y`.

Both are instances of `RegionalCompat.regional_forced` at a strict-interior translate, transported back by the deck. -/

namespace FLatticePaper.ForcedArrows

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.RegionalCompat

theorem evenSite_add_even {x v : Site} (hv : EvenSite v) : EvenSite (x + v) ↔ EvenSite x := by
  unfold EvenSite at hv ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem incomingNeg_add_even {x v : Site} (hv : EvenSite v) : incomingNeg (x + v) = incomingNeg x + v := by
  unfold incomingNeg
  by_cases hx : EvenSite x
  · rw [if_pos hx, if_pos ((evenSite_add_even hv).mpr hx)]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · rw [if_neg hx, if_neg (fun h => hx ((evenSite_add_even hv).mp h))]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring

theorem incomingPos_add_even {x v : Site} (hv : EvenSite v) : incomingPos (x + v) = incomingPos x + v := by
  unfold incomingPos
  by_cases hx : EvenSite x
  · rw [if_pos hx, if_pos ((evenSite_add_even hv).mpr hx)]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring
  · rw [if_neg hx, if_neg (fun h => hx ((evenSite_add_even hv).mp h))]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals ring

/-- An input of `x` is not `x`. -/
theorem input_ne {x u : Site} (hu : u = incomingNeg x ∨ u = incomingPos x) : u ≠ x := by
  intro h
  rcases hu with hu | hu
  · unfold incomingNeg at hu
    split_ifs at hu with hx
    · have h1 := congrArg Prod.fst hu
      have h2 := congrArg Prod.snd hu
      simp only at h1 h2
      rw [h] at h1 h2
      omega
    · have h1 := congrArg Prod.fst hu
      have h2 := congrArg Prod.snd hu
      simp only at h1 h2
      rw [h] at h1 h2
      omega
  · unfold incomingPos at hu
    split_ifs at hu with hx
    · have h1 := congrArg Prod.fst hu
      have h2 := congrArg Prod.snd hu
      simp only at h1 h2
      rw [h] at h1 h2
      omega
    · have h1 := congrArg Prod.fst hu
      have h2 := congrArg Prod.snd hu
      simp only at h1 h2
      rw [h] at h1 h2
      omega

/-- A nonfree point whose translate is nonfree-free: `Nonfree (u + v)` forces `Nonfree u` for a span vector `v`. -/
theorem nonfree_of_add_span {frame : ChildFrame} {u v : Site} (hv : v ∈ frame.child.modifiedDeck.span)
    (h : Nonfree frame (u + v)) : Nonfree frame u := by
  unfold Nonfree at h ⊢
  intro w hw hmem
  apply h (w + -v) (span_add_mem hw (span_neg_mem hv))
  rw [show u + v + (w + -v) = u + w by abel]
  exact hmem

/-- **A nonfree white forced to a non-nonfree input** (source §A). -/
theorem forced_to_free_input {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    {x u : Site} (hxn : Nonfree frame x) (hw : laplacian G x = 0)
    (hu : u = incomingNeg x ∨ u = incomingPos x) (hfree : ¬ Nonfree frame u) :
    ForcedEdge G (fun _ _ => False) x u := by
  obtain ⟨v, hv, hSI⟩ := nonfree_bridge frame x hxn
  have hev : EvenSite v := evenSite_of_span frame hv
  have hlap : laplacian G (x + v) = 0 := by
    rw [laplacian_span_inv frame G hP hv x]
    exact hw
  obtain ⟨o, ho⟩ := hW1 (x + v) hSI hlap
  have hnoSI : ¬ StrictInterior frame.child.num frame.child.den (u + v) := by
    intro h
    exact hfree (nonfree_of_add_span hv (strictInterior_nonfree frame h))
  have hne : u + v ≠ x + v := by
    intro h
    exact input_ne hu (add_right_cancel h)
  have hreg := regional_forced (F := G)
    (R := StrictInterior frame.child.num frame.child.den)
    (S := fun p => p = x + v) (C := fun p t => p = x + v ∧ t = u + v)
    (r := fun p => if p = x + v then (1 : ℤ) else 0)
    (by
      rintro p t ⟨rfl, rfl⟩
      simp [hne])
    (by
      intro p t _ hC hR
      obtain ⟨_, rfl⟩ := hC
      exact absurd hR hnoSI)
    (by
      intro p hp hl
      rw [hp, hlap] at hl
      norm_num at hl)
    (by
      intro p hp _
      subst hp
      refine ⟨u + v, ⟨rfl, rfl⟩, ?_⟩
      rcases hu with h | h
      · left
        rw [h, incomingNeg_add_even hev]
      · right
        rw [h, incomingPos_add_even hev])
    ho rfl
  obtain ⟨_, ho2⟩ := hreg
  rw [ho2] at ho
  have hF : ForcedEdge G (fun _ _ => False) (x + v) (u + v) := FLatticePaper.W1.forcedEdgeIn_forced ho
  have hnv : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
  have hback := forcedEdge_add G (evenSite_of_span frame hnv)
    (fun y => laplacian_span_inv frame G hP hnv y) hF
  rw [add_neg_cancel_right, add_neg_cancel_right] at hback
  exact hback

/-- **A nonfree white forced to its white input whose other input is not nonfree** (the two-site region `{x+v, y+v}` with the exit
`w+v`, source §C.2). -/
theorem forced_two_chain {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    {x y w : Site} (hxn : Nonfree frame x) (hxw : laplacian G x = 0) (hy : laplacian G y = 0)
    (hyx : y = incomingNeg x ∨ y = incomingPos x)
    (hw : w = incomingNeg y ∨ w = incomingPos y) (hwfree : ¬ Nonfree frame w) :
    ForcedEdge G (fun _ _ => False) x y := by
  obtain ⟨v, hv, hSI⟩ := nonfree_bridge frame x hxn
  have hev : EvenSite v := evenSite_of_span frame hv
  have hlapx : laplacian G (x + v) = 0 := by
    rw [laplacian_span_inv frame G hP hv x]
    exact hxw
  have hlapy : laplacian G (y + v) = 0 := by
    rw [laplacian_span_inv frame G hP hv y]
    exact hy
  obtain ⟨o, ho⟩ := hW1 (x + v) hSI hlapx
  have hnoSI : ¬ StrictInterior frame.child.num frame.child.den (w + v) := fun h =>
    hwfree (nonfree_of_add_span hv (strictInterior_nonfree frame h))
  have hyx' : y + v ≠ x + v := fun h => input_ne hyx (add_right_cancel h)
  have hwy : w + v ≠ y + v := fun h => input_ne hw (add_right_cancel h)
  have hwx : w + v ≠ x + v := by
    intro h
    apply hnoSI
    rw [h]
    exact hSI
  have hreg := regional_forced (F := G)
    (R := StrictInterior frame.child.num frame.child.den)
    (S := fun p => p = x + v ∨ p = y + v)
    (C := fun p t => (p = x + v ∧ t = y + v) ∨ (p = y + v ∧ t = w + v))
    (r := fun p => if p = x + v then (2 : ℤ) else if p = y + v then 1 else 0)
    (by
      rintro p t (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · simp [hyx']
      · simp [hwx, hwy, input_ne hyx])
    (by
      intro p t _ hC hR
      rcases hC with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr rfl
      · exact absurd hR hnoSI)
    (by
      intro p hp hl
      rcases hp with rfl | rfl
      · rw [hlapx] at hl
        norm_num at hl
      · rw [hlapy] at hl
        norm_num at hl)
    (by
      intro p hp _
      rcases hp with rfl | rfl
      · refine ⟨y + v, Or.inl ⟨rfl, rfl⟩, ?_⟩
        rcases hyx with h | h
        · left
          rw [h, incomingNeg_add_even hev]
        · right
          rw [h, incomingPos_add_even hev]
      · refine ⟨w + v, Or.inr ⟨rfl, rfl⟩, ?_⟩
        rcases hw with h | h
        · left
          rw [h, incomingNeg_add_even hev]
        · right
          rw [h, incomingPos_add_even hev])
    ho (Or.inl rfl)
  have ho2 : o = y + v := by
    rcases hreg with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (fun e => hyx' e.symm)
  rw [ho2] at ho
  have hF : ForcedEdge G (fun _ _ => False) (x + v) (y + v) := FLatticePaper.W1.forcedEdgeIn_forced ho
  have hnv : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
  have hback := forcedEdge_add G (evenSite_of_span frame hnv)
    (fun y' => laplacian_span_inv frame G hP hnv y') hF
  rw [add_neg_cancel_right, add_neg_cancel_right] at hback
  exact hback

end FLatticePaper.ForcedArrows
