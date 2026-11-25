import FLatticePaper.Plane.Induction.MinPolicy
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 72 / Q24 (`fixes/Q24.md`, GAP (b)): the level-`k` policy of the forced-transfer repair, as a proof.

Fix a level `k`, with `D = slip F η = F − g` and `g = F(· + ησ)`. Off the level `D = k` the selection is the F-selection `C.sel`. On the
level, at a white centre, an input of strictly lower `D` is chosen if one exists; otherwise the tie: the translated opposite selection
`O` when both inputs tie (then `g` is white there), the tied input when the other input steps up (then `g` is black there, and `O`
keeps both inputs). At a black centre both inputs are kept (`C` keeps both off the level as well).

The rank `q24Key` is the pair `(D, R_g)` on the level and `(D, R_F)` off it. Every kept input has a strictly smaller key
(`black_key_lt`, `white_key`), so `squareClauses_of_burning` gives every unit square clause for `q24Sel`. Hence unit propagation of `F`
agrees with `q24Sel` (`forced_eq_q24`), and a forced literal at a flat white-white tie is the `g` choice (`forced_flat_eq_g`). Where the
F-selection and the Q24 selection disagree at a white root, neither literal is forced (`neither_forced_of_disagree`). -/

namespace FLatticePaper.Q24Policy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1MRank FLatticePaper.MinPolicy

variable {frame : ChildFrame} {F : Field} {η k : ℤ}

/-- The F-side rank of a site: its price, rounded slip and the F-policy rank. -/
def rankF (C : CanonicalSignedPolicy frame F η) (x : Site) : Lex (ℤ × Lex (ℤ × ℤ)) :=
  toLex (frame.price F x, toLex (frame.cutGrade F 0 1 η x, C.rank x))

/-- The g-side rank of a site: the price, rounded slip and rank of the opposite policy at `x + ησ`. -/
def rankG (O : CanonicalSignedPolicy frame F (-η)) (x : Site) : Lex (ℤ × Lex (ℤ × ℤ)) :=
  toLex (frame.price F (x + η • frame.shortShift),
    toLex (frame.cutGrade F 0 1 (-η) (x + η • frame.shortShift), O.rank (x + η • frame.shortShift)))

/-- The Q24 rank: the pair `(D, R_g)` on the level `D = k`, and `(D, R_F)` off it. -/
def q24Key (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (x : Site) :
    Lex (ℤ × Lex (ℤ × Lex (ℤ × ℤ))) :=
  toLex (frame.slip F η x, if frame.slip F η x = k then rankG O x else rankF C x)

/-- The tie choice at a white centre with no lower input: the translated `g` selection when both inputs tie, else the tied input. -/
def tieSel (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (c : Site) : Site :=
  if frame.slip F η (incomingNeg c) = k ∧ frame.slip F η (incomingPos c) = k then
    O.sel (c + η • frame.shortShift) - η • frame.shortShift
  else if frame.slip F η (incomingNeg c) = k then incomingNeg c else incomingPos c

/-- The Q24 selection: the F-selection off the level; on it, a lower input if one exists, otherwise the tie. -/
def q24Sel (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (c : Site) : Site :=
  if frame.slip F η c = k then
    if frame.slip F η (incomingNeg c) < k then incomingNeg c
    else if frame.slip F η (incomingPos c) < k then incomingPos c
    else tieSel O k c
  else C.sel c

/-- Translation by an even shift preserves the lower input. -/
theorem incomingNeg_add_even (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingNeg (x + s) = incomingNeg x + s := by
  have h : EvenSite (x + s) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · have hx' : EvenSite (x + s) := h.mpr hx
    unfold incomingNeg
    rw [if_pos hx, if_pos hx']
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · have hx' : ¬ EvenSite (x + s) := fun h' => hx (h.mp h')
    unfold incomingNeg
    rw [if_neg hx, if_neg hx']
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

theorem incomingPos_add_even (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingPos (x + s) = incomingPos x + s := by
  have h : EvenSite (x + s) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · have hx' : EvenSite (x + s) := h.mpr hx
    unfold incomingPos
    rw [if_pos hx, if_pos hx']
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · have hx' : ¬ EvenSite (x + s) := fun h' => hx (h.mp h')
    unfold incomingPos
    rw [if_neg hx, if_neg hx']
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

/-- The divergence of `D` over the two inputs of a centre is the difference of the Laplacians of `F` and `g`. -/
theorem slip_split (c : Site) :
    (frame.slip F η (incomingNeg c) - frame.slip F η c) + (frame.slip F η (incomingPos c) - frame.slip F η c)
      = laplacian F c - laplacian (gF frame F η) c := by
  simp only [slip_eq_gF, laplacian]
  ring

/-- The translated opposite selection of a `g`-white centre: an input of the centre with `D` at least `D(centre)`, selected by `O`. -/
theorem O_sel_spec (O : CanonicalSignedPolicy frame F (-η)) (hη : η = 1 ∨ η = -1) {c : Site}
    (hw : laplacian F (c + η • frame.shortShift) = 0) :
    (O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingNeg c ∨
      O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingPos c) ∧
    frame.slip F η c ≤ frame.slip F η (O.sel (c + η • frame.shortShift) - η • frame.shortShift) ∧
    O.policy (c + η • frame.shortShift) (O.sel (c + η • frame.shortShift)) := by
  have hpar := shift_even frame hη
  have hpol : O.policy (c + η • frame.shortShift) (O.sel (c + η • frame.shortShift)) :=
    (O.white_policy _ hw _).mpr rfl
  refine ⟨?_, ?_, hpol⟩
  · rcases O.sel_input _ hw with h | h
    · left
      rw [h, incomingNeg_add_even c _ hpar, add_sub_cancel_right]
    · right
      rw [h, incomingPos_add_even c _ hpar, add_sub_cancel_right]
  · exact slip_le_of_G O (by rw [sub_add_cancel]; exact hpol)

/-- At a `g`-black centre the opposite policy keeps both inputs of the translated centre. -/
theorem O_keeps_of_black (O : CanonicalSignedPolicy frame F (-η)) (hη : η = 1 ∨ η = -1) {c x : Site}
    (hb : laplacian F (c + η • frame.shortShift) = -1) (hx : x = incomingNeg c ∨ x = incomingPos c) :
    O.policy (c + η • frame.shortShift) (x + η • frame.shortShift) := by
  have hpar := shift_even frame hη
  have hq := O.quota.1 _ hb
  rcases hx with rfl | rfl
  · rw [← incomingNeg_add_even c _ hpar]
    exact hq.1
  · rw [← incomingPos_add_even c _ hpar]
    exact hq.2

/-- At a `g`-white centre, the opposite policy keeps an input `x` of the centre when `x` is tied and every other input is lower. -/
theorem O_keeps_of_tie (O : CanonicalSignedPolicy frame F (-η)) (hη : η = 1 ∨ η = -1) {c x : Site}
    (hw : laplacian F (c + η • frame.shortShift) = 0) (hc : frame.slip F η c = k)
    (hy : ∀ y, (y = incomingNeg c ∨ y = incomingPos c) → y ≠ x → frame.slip F η y < k) :
    O.policy (c + η • frame.shortShift) (x + η • frame.shortShift) := by
  obtain ⟨hz, hle, hpol⟩ := O_sel_spec O hη hw
  by_cases hzx : O.sel (c + η • frame.shortShift) - η • frame.shortShift = x
  · have hsel : O.sel (c + η • frame.shortShift) = x + η • frame.shortShift := by
      rw [← hzx, sub_add_cancel]
    rw [← hsel]
    exact hpol
  · exfalso
    have hlow := hy _ hz hzx
    omega

/-- Lower `D` decreases the Q24 rank. -/
theorem key_lt_lower (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) {c x : Site}
    (h : frame.slip F η x < frame.slip F η c) : q24Key C O k x < q24Key C O k c := by
  unfold q24Key
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Off the level, an F-kept input of equal `D` decreases the F-rank. -/
theorem key_lt_F (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) {c x : Site}
    (hC : C.policy c x) (hc : frame.slip F η c ≠ k) (hD : frame.slip F η x = frame.slip F η c) :
    q24Key C O k x < q24Key C O k c := by
  have hx : frame.slip F η x ≠ k := by
    rw [hD]
    exact hc
  unfold q24Key
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hD, ?_⟩
  rw [if_neg hx, if_neg hc]
  exact lex_of_canonical C hC

/-- On the level, an opposite-kept input of equal `D` decreases the g-rank. -/
theorem key_lt_G (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) {c x : Site}
    (hO : O.policy (c + η • frame.shortShift) (x + η • frame.shortShift)) (hc : frame.slip F η c = k)
    (hD : frame.slip F η x = frame.slip F η c) : q24Key C O k x < q24Key C O k c := by
  have hx : frame.slip F η x = k := hD.trans hc
  unfold q24Key
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hD, ?_⟩
  rw [if_pos hx, if_pos hc]
  exact lex_of_canonical O hO

/-- On the level, the other input of a tied input of a `g`-white centre is lower. -/
theorem other_lower {c x y : Site} (hb : laplacian F c = -1) (hg : laplacian (gF frame F η) c = 0)
    (hx : x = incomingNeg c ∨ x = incomingPos c) (hxk : frame.slip F η x = frame.slip F η c)
    (hy : y = incomingNeg c ∨ y = incomingPos c) (hyx : y ≠ x) :
    frame.slip F η y < frame.slip F η c := by
  have hs := slip_split (frame := frame) (F := F) (η := η) c
  rw [hb, hg] at hs
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hyx
  · omega
  · omega
  · exact absurd rfl hyx

/-- **The black roots decrease.** Both inputs of an F-black centre have a smaller Q24 rank. -/
theorem black_key_lt (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {c x : Site}
    (hb : laplacian F c = -1) (hx : x = incomingNeg c ∨ x = incomingPos c) :
    q24Key C O k x < q24Key C O k c := by
  have hkeep : C.policy c x := by
    rcases hx with rfl | rfl
    · exact (C.quota.1 c hb).1
    · exact (C.quota.1 c hb).2
  have hle := slip_le_of_F C hkeep
  by_cases hc : frame.slip F η c = k
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower C O hlt
    · have hlapg : laplacian F (c + η • frame.shortShift) = laplacian (gF frame F η) c :=
        (lap_gF_eq_shift hη c).symm
      have hO : O.policy (c + η • frame.shortShift) (x + η • frame.shortShift) := by
        rcases hbin (c + η • frame.shortShift) with hg1 | hg0
        · exact O_keeps_of_black O hη hg1 hx
        · have hg : laplacian (gF frame F η) c = 0 := by
            rw [← hlapg]
            exact hg0
          apply O_keeps_of_tie O hη (x := x) hg0 hc
          intro y hy1 hyx
          have := other_lower hb hg hx heq hy1 hyx
          omega
      exact key_lt_G C O hO hc heq
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower C O hlt
    · exact key_lt_F C O hkeep hc heq

/-- **The white selection decreases.** At a white centre the Q24 selection is an input whose Q24 rank is smaller. -/
theorem white_key (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {c : Site}
    (hw : laplacian F c = 0) :
    (q24Sel C O k c = incomingNeg c ∨ q24Sel C O k c = incomingPos c) ∧
      q24Key C O k (q24Sel C O k c) < q24Key C O k c := by
  by_cases hc : frame.slip F η c = k
  · have hlapg : laplacian F (c + η • frame.shortShift) = laplacian (gF frame F η) c :=
      (lap_gF_eq_shift hη c).symm
    have hs := slip_split (frame := frame) (F := F) (η := η) c
    rw [hw] at hs
    have hgb : laplacian (gF frame F η) c = -1 ∨ laplacian (gF frame F η) c = 0 := by
      rw [← hlapg]
      exact hbin _
    unfold q24Sel
    rw [if_pos hc]
    by_cases hA : frame.slip F η (incomingNeg c) < k
    · rw [if_pos hA]
      exact ⟨Or.inl rfl, key_lt_lower C O (by rw [hc]; exact hA)⟩
    · rw [if_neg hA]
      by_cases hB : frame.slip F η (incomingPos c) < k
      · rw [if_pos hB]
        exact ⟨Or.inr rfl, key_lt_lower C O (by rw [hc]; exact hB)⟩
      · rw [if_neg hB]
        by_cases hT : frame.slip F η (incomingNeg c) = k ∧ frame.slip F η (incomingPos c) = k
        · -- both inputs tie: `g` is white and the choice is the translated opposite selection
          have hg0 : laplacian (gF frame F η) c = 0 := by omega
          have hgw : laplacian F (c + η • frame.shortShift) = 0 := by
            rw [hlapg]
            exact hg0
          obtain ⟨hz, _, hpol⟩ := O_sel_spec O hη hgw
          unfold tieSel
          rw [if_pos hT]
          refine ⟨hz, ?_⟩
          have hD : frame.slip F η (O.sel (c + η • frame.shortShift) - η • frame.shortShift) = frame.slip F η c := by
            rcases hz with h | h
            · rw [h]
              omega
            · rw [h]
              omega
          apply key_lt_G C O (x := O.sel (c + η • frame.shortShift) - η • frame.shortShift) _ hc hD
          rw [sub_add_cancel]
          exact hpol
        · -- one input ties and the other steps up: `g` is black and keeps both inputs
          unfold tieSel
          rw [if_neg hT]
          by_cases hA3 : frame.slip F η (incomingNeg c) = k
          · rw [if_pos hA3]
            have hg1 : laplacian (gF frame F η) c = -1 := by omega
            have hgb1 : laplacian F (c + η • frame.shortShift) = -1 := by
              rw [hlapg]
              exact hg1
            refine ⟨Or.inl rfl, ?_⟩
            exact key_lt_G C O (O_keeps_of_black O hη hgb1 (Or.inl rfl)) hc (by rw [hA3, hc])
          · rw [if_neg hA3]
            have hB3 : frame.slip F η (incomingPos c) = k := by omega
            have hg1 : laplacian (gF frame F η) c = -1 := by omega
            have hgb1 : laplacian F (c + η • frame.shortShift) = -1 := by
              rw [hlapg]
              exact hg1
            refine ⟨Or.inr rfl, ?_⟩
            exact key_lt_G C O (O_keeps_of_black O hη hgb1 (Or.inr rfl)) hc (by rw [hB3, hc])
  · -- off the level the selection is the F-selection
    unfold q24Sel
    rw [if_neg hc]
    have hkeep : C.policy c (C.sel c) := (C.white_policy c hw _).mpr rfl
    have hle := slip_le_of_F C hkeep
    refine ⟨C.sel_input c hw, ?_⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower C O hlt
    · exact key_lt_F C O hkeep hc heq

/-- **The Q24 square clauses.** Every unit square clause holds for the Q24 selection (`squareClauses_of_burning`). -/
theorem q24_squares (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) (a b : ℤ) :
    SquareClauseSat F (q24Sel C O k) a b :=
  squareClauses_of_burning (R := q24Key C O k) (sel := q24Sel C O k) hbin
    (fun _ hb _ hi => black_key_lt C O hη hbin hb hi) (fun _ hw => white_key C O hη hbin hw) a b

/-- **Soundness of unit propagation for Q24.** Every forced literal of `F` is the Q24 selection. -/
theorem q24_forced_sound (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {c i : Site}
    (h : ForcedEdge F (fun _ _ => False) c i) : q24Sel C O k c = i :=
  forced_sound F (fun _ _ => False) (q24Sel C O k) (fun _ hw => (white_key C O hη hbin hw).1)
    (fun _ _ h => False.elim h) (q24_squares C O hη hbin) c i h

/-- **Forced literals at a flat white-white tie are the `g` choice.** -/
theorem forced_flat_eq_g (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {c i : Site}
    (hc : frame.slip F η c = k) (hA : frame.slip F η (incomingNeg c) = k)
    (hB : frame.slip F η (incomingPos c) = k) (h : ForcedEdge F (fun _ _ => False) c i) :
    i = O.sel (c + η • frame.shortShift) - η • frame.shortShift := by
  have hq := q24_forced_sound (k := k) C O hη hbin h
  have h1 : ¬ frame.slip F η (incomingNeg c) < k := by omega
  have h2 : ¬ frame.slip F η (incomingPos c) < k := by omega
  rw [← hq]
  unfold q24Sel tieSel
  rw [if_pos hc, if_neg h1, if_neg h2, if_pos ⟨hA, hB⟩]

/-- **A rise with disagreeing choices forces neither literal.** If the Q24 selection differs from the F-selection at a white root, then
neither the F-choice nor the Q24 choice is a forced literal of `F`. -/
theorem neither_forced_of_disagree (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) {z : Site}
    (hne : q24Sel C O k z ≠ C.sel z) :
    ¬ ForcedEdge F (fun _ _ => False) z (C.sel z) ∧ ¬ ForcedEdge F (fun _ _ => False) z (q24Sel C O k z) := by
  constructor
  · intro h
    exact hne (q24_forced_sound C O hη hbin h)
  · intro h
    exact hne (forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h => False.elim h) C.squares z _ h).symm

/-- An input edge translates to an input edge of the translated centre. -/
theorem edge_shift (frame : ChildFrame) (hη : η = 1 ∨ η = -1) {x c : Site} (h : Edge x c) :
    Edge (x + η • frame.shortShift) (c + η • frame.shortShift) := by
  have hpar := shift_even frame hη
  unfold Edge at h ⊢
  rcases h with h | h
  · left
    rw [incomingNeg_add_even c _ hpar, h]
  · right
    rw [incomingPos_add_even c _ hpar, h]

/-- Two distinct inputs of a centre carry the sum of the two inputs. -/
theorem inputs_sum (f : Site → ℤ) {z u v : Site} (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hv : v = incomingNeg z ∨ v = incomingPos z) (huv : u ≠ v) : f u + f v = f (incomingNeg z) + f (incomingPos z) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · rfl
  · ring
  · exact absurd rfl huv

/-- Two distinct inputs of a centre that are both tied make both inputs tied. -/
theorem inputs_both (f : Site → ℤ) (k : ℤ) {z u v : Site} (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hv : v = incomingNeg z ∨ v = incomingPos z) (huv : u ≠ v) (hfu : f u = k) (hfv : f v = k) :
    f (incomingNeg z) = k ∧ f (incomingPos z) = k := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · exact ⟨hfu, hfv⟩
  · exact ⟨hfv, hfu⟩
  · exact absurd rfl huv

/-- **The rise reduction (`Q24.md`, the rising-edge paragraph).** At a retained F-edge `z → u` of `C` with `Φ_η z < Φ_η u`, the root
`z` is an F-white flat tie of the level `D(z)`, the `g` root `z + ησ` is white, and the Q24 selection at `z` is the opposite choice
`v ≠ u`, so it differs from the F-choice `C.sel z`. -/
theorem rise_reduction (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hUp : HasUnitPrice frame F) {z u : Site} (hC : C.policy z u)
    (hrise : frame.chainPotential F η z < frame.chainPotential F η u) :
    laplacian F z = 0 ∧ laplacian F (z + η • frame.shortShift) = 0 ∧
      q24Sel C O (frame.slip F η z) z ≠ C.sel z := by
  have hedge : Edge u z := C.policyEdge z u hC
  have hle : frame.slip F η u ≤ frame.slip F η z := slip_le_of_F C hC
  have hpU := hUp _ _ (edge_shift frame hη hedge)
  unfold priceIncrement at hpU
  unfold ChildFrame.chainPotential at hrise
  have hD : frame.slip F η u = frame.slip F η z := by omega
  have hP : frame.price F (u + η • frame.shortShift) = frame.price F (z + η • frame.shortShift) + 1 := by omega
  have hgw : laplacian F (z + η • frame.shortShift) = 0 := by
    rcases hbin (z + η • frame.shortShift) with h | h
    · exfalso
      have hOk := O_keeps_of_black O hη h (x := u) hedge
      have hm := O.nonincreasingP _ _ hOk
      rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at hm
      omega
    · exact h
  obtain ⟨hzin, hle2, hpol⟩ := O_sel_spec O hη hgw
  have hvu : O.sel (z + η • frame.shortShift) - η • frame.shortShift ≠ u := by
    intro h
    have hsel : O.sel (z + η • frame.shortShift) = u + η • frame.shortShift := by
      rw [← h, sub_add_cancel]
    have hOk : O.policy (z + η • frame.shortShift) (u + η • frame.shortShift) := by
      rw [← hsel]
      exact hpol
    have hm := O.nonincreasingP _ _ hOk
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at hm
    omega
  have hpair := slip_split (frame := frame) (F := F) (η := η) z
  have hg0 : laplacian (gF frame F η) z = 0 := by
    rw [lap_gF_eq_shift hη z]
    exact hgw
  have hsum := inputs_sum (frame.slip F η) hedge hzin hvu.symm
  have hw : laplacian F z = 0 := by
    rcases hbin z with hb | hw
    · exfalso
      rw [hb, hg0] at hpair
      omega
    · exact hw
  rw [hw, hg0] at hpair
  have hT := inputs_both (frame.slip F η) (frame.slip F η z) hedge hzin hvu.symm hD (by omega)
  have hq : q24Sel C O (frame.slip F η z) z = O.sel (z + η • frame.shortShift) - η • frame.shortShift := by
    have h1 : ¬ frame.slip F η (incomingNeg z) < frame.slip F η z := by
      rw [hT.1]
      exact lt_irrefl _
    have h2 : ¬ frame.slip F η (incomingPos z) < frame.slip F η z := by
      rw [hT.2]
      exact lt_irrefl _
    unfold q24Sel tieSel
    rw [if_pos (rfl : frame.slip F η z = frame.slip F η z), if_neg h1, if_neg h2, if_pos hT]
  have hCsel : C.sel z = u := ((C.white_policy z hw u).mp hC).symm
  exact ⟨hw, hgw, by rw [hq, hCsel]; exact hvu⟩

/-- **A rising F-edge forces neither literal.** At a retained edge `z → u` of `C` with `Φ_η z < Φ_η u`, the F-choice `C.sel z` and the
Q24 choice at the level `D(z)` are not forced literals of `F`. -/
theorem rise_neither_forced (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hUp : HasUnitPrice frame F) {z u : Site} (hC : C.policy z u)
    (hrise : frame.chainPotential F η z < frame.chainPotential F η u) :
    ¬ ForcedEdge F (fun _ _ => False) z (C.sel z) ∧
      ¬ ForcedEdge F (fun _ _ => False) z (q24Sel C O (frame.slip F η z) z) :=
  neither_forced_of_disagree C O hη hbin (rise_reduction C O hη hbin hUp hC hrise).2.2

end FLatticePaper.Q24Policy
