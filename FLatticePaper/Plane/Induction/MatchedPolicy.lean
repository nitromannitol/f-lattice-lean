import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.Q3Paragraph8
import FLatticePaper.Plane.Induction.Q3Strong
import FLatticePaper.Plane.Induction.SheetReflection
import FLatticePaper.Plane.Induction.OldPolicy

/-! Task 63: the matched policies as Lean objects, and the leaves of `noBlackPairRise_of_cases` wired to the proved lemmas.

* `zTurn x = (−x₂, x₁ − 1)` (the offset quarter turn `Z`); `zTurn ((1,−1) − w) = reflectionI − zTurn w`.
* `parentPolicy P`: the conjugate's policy `P` (on the conjugate field) transported to the parent sheet by `Z`:
  `parentPolicy P c i := P.retained (Z c) (Z i)`. Its reflection about `I = (1,−1)` is `P.reflection`, and its price is
  nondecreasing: `p(x) = c₀ − P'(Zx)` (paragraph 5), so `P.priceNonincreasing` gives the price step.
* `sheetPolicyA lv`: the A-sheet policy `(c, i) ↦ parentPolicy (c − lv) (i − lv)`; `sheetPolicyC`: its image under the
  sheet exchange `R z = centre − z` (`SheetExchange`), `C`-policy `(c, i) ↦ A-policy (R c) (R i)`.
* Leaves: `nonfree_drop_excluded` (paragraph 7 and the reflection), `H_drop_excluded` (`H_root_a_eq_zero`, with `hweb`
  as an explicit input), `first_offer_of_strict` (`p_shift_bound_of_strong`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The offset quarter turn `Z(x, y) = (−y, x − 1)` of the paragraph-5 identity. -/
def zTurn (x : Site) : Site := (-x.2, x.1 - 1)

theorem zTurn_reflect (w : Site) : zTurn ((1, -1) - w) = reflectionI - zTurn w := by
  unfold zTurn reflectionI
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring

/-- The conjugate's policy transported to the parent sheet by `Z`. -/
def parentPolicy {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyData frame G seed) :
    Site → Site → Prop :=
  fun c i => P.retained (zTurn c) (zTurn i)

/-- The transported policy is reflected about `I = (1, −1)`. -/
theorem parentPolicy_reflection {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) {c i : Site} (h : parentPolicy P c i)
    (hroot : laplacian G (zTurn c) = -1 ∨ SquareClauses.ForcedEdge G seed (zTurn c) (zTurn i)) :
    parentPolicy P ((1, -1) - c) ((1, -1) - i) := by
  unfold parentPolicy at h ⊢
  rw [zTurn_reflect, zTurn_reflect]
  exact P.reflection (zTurn c) (zTurn i) h hroot

/-- The price step of the transported policy: `p(x) = c₀ − P'(Zx)` does not decrease along it. -/
theorem parentPolicy_price {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) :
    NondecreasingAlong (fun y => frame.cutPrice - frame.price G (zTurn y)) (parentPolicy P) := by
  intro c i h
  unfold parentPolicy at h
  have h' : frame.price G (zTurn i) ≤ frame.price G (zTurn c) := P.priceNonincreasing _ _ h
  show frame.cutPrice - frame.price G (zTurn c) ≤ frame.cutPrice - frame.price G (zTurn i)
  omega

/-- The A-sheet policy: the transported policy at the sheet coordinates `c − lv`, `i − lv`. -/
def sheetPolicyA {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyData frame G seed)
    (lv : Site) : Site → Site → Prop :=
  fun c i => parentPolicy P (c - lv) (i - lv)

/-- The C-sheet policy: the A-sheet policy pulled back by the sheet exchange `R z = centre − z` (`SheetExchange`). -/
def sheetPolicyC {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyData frame G seed)
    (lv : Site) (centre : Site) : Site → Site → Prop :=
  fun c i => sheetPolicyA P lv (centre - c) (centre - i)

/-- The jump of the parent field along the even shift `εU_q` (the quantity `a` of paragraph 5). -/
def jumpA (frame : ChildFrame) (f : Field) (x : Site) : ℤ :=
  f (x + (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) - f x

/-- Paragraphs 5 and 7: the jump `a(x)` is the price `c₀ − P'(Z(I − x))`. -/
theorem jumpA_eq_cutPrice {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x =
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn ((1, -1) - x)) := by
  unfold jumpA
  rw [paragraph7_of_strong hSE x]
  have h5 := paragraph5_field_identity_of_strong h hSE ((1, -1) - x)
  have e : (1, -1) - x - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) =
      (1, -1) - x + (-(frameAt word).eps * (frameAt word).parents.even.den,
        -(frameAt word).eps * (frameAt word).parents.even.num) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e, h5]
  rfl

/-- The A-sheet policy carries the price step in its own coordinates: `p` at `c − lv` does not decrease along it. -/
theorem sheetPolicyA_price {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) (lv : Site) :
    NondecreasingAlong (fun c => frame.cutPrice - frame.price G (zTurn (c - lv))) (sheetPolicyA P lv) :=
  fun c i h => parentPolicy_price P (c - lv) (i - lv) h

/-- The C-sheet policy carries the price step in its own coordinates, through the exchange `z ↦ centre − z`. -/
theorem sheetPolicyC_price {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) (lv centre : Site) :
    NondecreasingAlong (fun c => frame.cutPrice - frame.price G (zTurn (centre - c - lv)))
      (sheetPolicyC P lv centre) :=
  fun c i h => parentPolicy_price P (centre - c - lv) (centre - i - lv) h

/-- Paragraph 3, strict root on the `A` side: with `Ψ = C − A ≥ 1` at the centre and the unit bound `Ψ(i) ≥ Ψ(c) − 1` on
the input, the minimum `M = min(A, C)` at the input is the `A` sheet. The unit bound `hΨ` (on the sheet difference) is
the named input of `SheetLocalInputs`: it is stated there for the chain potential `Ξ`, not for `C − A`. -/
theorem sheetMin_A_at_input (frame : ChildFrame) (Fp : Field) {c i : Site}
    (hc : 1 ≤ frame.sheetC Fp c - frame.sheetA Fp c)
    (hΨ : frame.sheetC Fp i - frame.sheetA Fp i ≥ frame.sheetC Fp c - frame.sheetA Fp c - 1) :
    frame.sheetMin Fp i = frame.sheetA Fp i := by
  unfold ChildFrame.sheetMin
  exact min_eq_left (by omega)

/-- Paragraph 3, strict root on the `C` side (`Ψ(c) ≤ −1`). -/
theorem sheetMin_C_at_input (frame : ChildFrame) (Fp : Field) {c i : Site}
    (hc : frame.sheetC Fp c - frame.sheetA Fp c ≤ -1)
    (hΨ : frame.sheetC Fp i - frame.sheetA Fp i ≤ frame.sheetC Fp c - frame.sheetA Fp c + 1) :
    frame.sheetMin Fp i = frame.sheetC Fp i := by
  unfold ChildFrame.sheetMin
  exact min_eq_right (by omega)

/-- Paragraph 3, tie: at `Ψ(c) = 0` the centre minimum is the `A` sheet (the target winner is chosen as `A`). -/
theorem sheetMin_A_at_tie (frame : ChildFrame) (Fp : Field) {c : Site}
    (hc : frame.sheetC Fp c - frame.sheetA Fp c = 0) : frame.sheetMin Fp c = frame.sheetA Fp c := by
  unfold ChildFrame.sheetMin
  exact min_eq_left (by omega)

/-- Paragraph 7 leaf (nonfree root): a drop `a(x) = 1 → a(x') = 0` along a transported policy edge is impossible. The
reflected edge is retained, and `p = c₀ − P'(Z·)` does not decrease along it. -/
theorem nonfree_drop_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {x x' : Site} (hpol : parentPolicy P x x')
    (h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1)
    (h0 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x' = 0)
    (hroot : laplacian (standardField (conjWord word)) (zTurn x) = -1 ∨
      SquareClauses.ForcedEdge (standardField (conjWord word)) seed (zTurn x) (zTurn x')) : False := by
  have hrefl := parentPolicy_reflection P hpol hroot
  have hmono : (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn ((1, -1) - x)) ≤
      (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn ((1, -1) - x')) :=
    parentPolicy_price P _ _ hrefl
  rw [← jumpA_eq_cutPrice h hSE x, ← jumpA_eq_cutPrice h hSE x'] at hmono
  omega

/-- Paragraph 8 leaf (H root): a drop from `a(x) = 1` at an old H root is impossible, since `a(x) = 0` there
(`H_root_a_eq_zero`). The H-web condition `hweb` is the open named input of paragraph 8. -/
theorem H_drop_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site)
    (hweb : HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den ((frameAt word).parentTGrade x))
    (h1 : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) x = 1) : False := by
  have h0 := H_root_a_eq_zero h hSE x hweb
  unfold jumpA at h1
  omega

/-- Paragraph 5 with the sheet step: the adjacent-chart first offer. At a strict `A` target (`Ψ ≥ 1`) the minimum
`min(p(x), Ψ + p(x − e))` is `p(x)`, because `p(x − e) ≥ p(x) − 1` (`p_shift_bound_of_strong`). -/
theorem first_offer_of_strict {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x : Site) {Ψ : ℤ} (hΨ : 1 ≤ Ψ) :
    min ((frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn x))
      (Ψ + ((frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn (x - (frameAt word).sheetStep)))) =
    (frameAt (conjWord word)).cutPrice -
        (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn x) := by
  have hb := p_shift_bound_of_strong h hSE x
  apply min_eq_left
  unfold zTurn at *
  omega

/-- The paragraph-5 quantity `p(y) = f(y − εU_q) − f(y)` of the parent field `f`. -/
def pJump (frame : ChildFrame) (f : Field) (y : Site) : ℤ :=
  f (y + (-(frame.eps * frame.parents.even.den), -(frame.eps * frame.parents.even.num))) - f y

theorem parentTGrade_add_site (frame : ChildFrame) (x y : Site) :
    frame.parentTGrade (x + y) = frame.parentTGrade x + frame.parentTGrade y := by
  unfold ChildFrame.parentTGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- `t_p(εU_q) = ε · eps`, so `t_p(−εU_q) = −1`. -/
theorem parentTGrade_neg_eps_uq (frame : ChildFrame) :
    frame.parentTGrade (-(frame.eps * frame.parents.even.den), -(frame.eps * frame.parents.even.num)) = -1 := by
  have hdet := frame.eps_det_even
  have hsq := frame.eps_sq_one
  unfold ChildFrame.parentTGrade
  simp only
  linear_combination (-frame.eps) * hdet - hsq

/-- The zero strip of `f` gives `p(0) = 0` (`t_p(0) = 0`, `t_p(−εU_q) = −1`). -/
theorem pJump_origin_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) 0 = 0 := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨hD, -, hND⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  unfold pJump
  rw [zero_add]
  have h1 := zeroStrip_of_strong h hSE (-((frameAt word).eps * (frameAt word).parents.even.den),
    -((frameAt word).eps * (frameAt word).parents.even.num)) (by rw [parentTGrade_neg_eps_uq]; omega)
    (by rw [parentTGrade_neg_eps_uq]; omega)
  have h0 := zeroStrip_of_strong h hSE 0 (by unfold ChildFrame.parentTGrade; simp; omega)
    (by unfold ChildFrame.parentTGrade; simp; omega)
  rw [h1, h0]
  ring

/-- The zero strip of `f` gives `p(1, 0) = 0` (`t_p(1, 0) = N`, `t_p((1,0) − εU_q) = N − 1`). -/
theorem pJump_corner_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (1, 0) = 0 := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨hD, -, hND⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  unfold pJump
  have ht1 : (frameAt word).parentTGrade (1, 0) = (frameAt word).parents.odd.num := by
    unfold ChildFrame.parentTGrade
    simp
  have ht2 := parentTGrade_add_site (frameAt word) (1, 0)
    (-((frameAt word).eps * (frameAt word).parents.even.den), -((frameAt word).eps * (frameAt word).parents.even.num))
  rw [parentTGrade_neg_eps_uq, ht1] at ht2
  have h1 := zeroStrip_of_strong h hSE ((1, 0) + (-((frameAt word).eps * (frameAt word).parents.even.den),
    -((frameAt word).eps * (frameAt word).parents.even.num)))
    (by rw [ht2]; omega) (by rw [ht2]; omega)
  have h0 := zeroStrip_of_strong h hSE (1, 0) (by rw [ht1]; omega) (by rw [ht1]; omega)
  rw [h1, h0]
  ring

/-- Paragraph 7 leaf (exceptional vertex `v`): the drop `a(v) = 1 → a(v − (1,0)) = 0` is impossible, because the two
values are `p(0) + 1` and `p(1,0) + 1` (named translation `hT`, the paper's `V_p`-step), and both `p` values vanish by
`pJump_origin_zero` and `pJump_corner_zero`. -/
theorem exceptional_drop_excluded {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (v : Site)
    (hT : jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (v - (1, 0)) =
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (1, 0) + 1) :
    jumpA (frameAt word) (quarterTurnField (standardField (conjWord word))) (v - (1, 0)) = 0 → False := by
  intro h0
  rw [hT, pJump_corner_zero h hSE] at h0
  omega

/-- Strict root (paragraph 3): with `Ψ = C − A` at the centre at least `1` and the unit bound on the input, the `A` sheet
is minimal at the input: `A(i) ≤ C(i)`. -/
theorem strict_root_A_at_input {A C : Site → ℤ} {c i : Site} (hc : 1 ≤ C c - A c)
    (hstep : C i - A i ≥ C c - A c - 1) : A i ≤ C i := by
  omega

/-- Strict root, `C` side: `Ψ(c) ≤ −1` and the unit bound give `C(i) ≤ A(i)`. -/
theorem strict_root_C_at_input {A C : Site → ℤ} {c i : Site} (hc : C c - A c ≤ -1)
    (hstep : C i - A i ≤ C c - A c + 1) : C i ≤ A i := by
  omega

end FLatticePaper.Induction
