import FLatticePaper.Plane.Induction.Q3Rise
import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.Potentials

/-! Task 62: `NoBlackPairRise` (OddRise.lean) assembled by the case split of fixes/Q3.md, paragraphs 3–10.

Proved here:
* `slipIncrement_eq_chain_gap`: the rise increment at an input `i` of `c` (shift `σ = shortShift`) equals the chain-gap
  increment `Φ₁(i) − Φ₁(c)` minus the increment of the shifted price `P(· + σ)`.
* `rise_excluded_at_edge`: a rise is impossible on an edge where `Φ₁` does not increase and `P(· + σ)` does not decrease
  (the first common chart).
* `laplacian_shortShift_eq_of_eps_one/neg_one`: the black partner `c + σ` has the Laplacian of `c − U_q` (ε = 1) or of
  `c + U_q` (ε = −1), since `σ = εU_p` and `U_p + U_q = U`; the packet period makes the Laplacian `U`-invariant.
* `not_rising_of_blockPair`: a black pair of the V block (paragraph 10, `black_centres_contradiction`) is impossible.
* `noBlackPairRise_of_cases`: `NoBlackPairRise` from the paper's case cover. The first common chart and the V block are
  proved; the other cases are named hypotheses (see the task-62 report for the reason each is not closed).
* `noBlackPairRise_of_oldPolicy`: the first common chart's chain-gap monotonicity taken from `OldPolicyData`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The configuration `NoBlackPairRise` excludes, at a centre `c` and an input `i`: a black centre with odd `D`, a black
translate `c + σ`, and the input `i` with slip increment `1`. -/
def RisingBlackPair (G : Field) (σ : Site) (c i : Site) : Prop :=
  (i = incomingNeg c ∨ i = incomingPos c) ∧ laplacian G c = -1 ∧ (G c - G (c + σ)) % 2 = 1 ∧
    laplacian G (c + σ) = -1 ∧ slipIncrement G (fun z => G (z + σ)) c i = 1

namespace ChildFrame
variable (frame : ChildFrame)

/-- The chain potential is the field minus the chain sheet `h_η`. -/
theorem chainPotential_eq_sub_chainSheet (G : Field) (η : ℤ) (z : Site) :
    frame.chainPotential G η z = G z - frame.chainSheet G η z := by
  unfold ChildFrame.chainPotential ChildFrame.chainSheet ChildFrame.price ChildFrame.slip
  ring

/-- The rise increment is the chain-gap increment minus the increment of the shifted price. -/
theorem slipIncrement_eq_chain_gap (G : Field) (c i : Site) :
    slipIncrement G (fun z => G (z + frame.shortShift)) c i =
      (frame.chainPotential G 1 i - frame.chainPotential G 1 c) -
        (frame.price G (i + frame.shortShift) - frame.price G (c + frame.shortShift)) := by
  unfold ChildFrame.chainPotential ChildFrame.slip slipIncrement
  simp only [one_smul]
  ring

/-- A rise is impossible on an edge where the chain potential does not increase and the shifted price does not decrease. -/
theorem rise_excluded_at_edge (G : Field) {c i : Site}
    (h1 : frame.chainPotential G 1 i ≤ frame.chainPotential G 1 c)
    (h2 : frame.price G (c + frame.shortShift) ≤ frame.price G (i + frame.shortShift)) :
    slipIncrement G (fun z => G (z + frame.shortShift)) c i ≠ 1 := by
  rw [frame.slipIncrement_eq_chain_gap]
  omega

/-- The Laplacian is invariant under the child kernel `U = (d, n)` (the packet period). -/
theorem laplacian_add_child_kernel {F : Field} (hP : frame.Packet F) (w : Site) :
    laplacian F (w + (frame.child.den, frame.child.num)) = laplacian F w := by
  obtain ⟨hper, -⟩ := hP.periods
  rw [frame.child_kernel] at hper
  exact laplacian_add_period F _ _ hper frame.child_evenSite_add_kernel w

theorem laplacian_sub_child_kernel {F : Field} (hP : frame.Packet F) (w : Site) :
    laplacian F (w - (frame.child.den, frame.child.num)) = laplacian F w := by
  have h := frame.laplacian_add_child_kernel hP (w - (frame.child.den, frame.child.num))
  rw [sub_add_cancel] at h
  exact h.symm

/-- For `ε = 1`: `c + σ = (c − U_q) + U`, so the black partner has the Laplacian of `c − U_q`. -/
theorem laplacian_shortShift_eq_of_eps_one {F : Field} (hP : frame.Packet F) (he : frame.eps = 1) (c : Site) :
    laplacian F (c + frame.shortShift) = laplacian F (c - (frame.parents.even.den, frame.parents.even.num)) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have e : c + frame.shortShift =
      (c - (frame.parents.even.den, frame.parents.even.num)) + (frame.child.den, frame.child.num) := by
    unfold ChildFrame.shortShift
    rw [he]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
  rw [e, frame.laplacian_add_child_kernel hP]

/-- For `ε = −1`: `c + σ = (c + U_q) − U`, so the black partner has the Laplacian of `c + U_q`. -/
theorem laplacian_shortShift_eq_of_eps_neg_one {F : Field} (hP : frame.Packet F) (he : frame.eps = -1) (c : Site) :
    laplacian F (c + frame.shortShift) = laplacian F (c + (frame.parents.even.den, frame.parents.even.num)) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have e : c + frame.shortShift =
      (c + (frame.parents.even.den, frame.parents.even.num)) - (frame.child.den, frame.child.num) := by
    unfold ChildFrame.shortShift
    rw [he]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
  rw [e, frame.laplacian_sub_child_kernel hP]

/-- The V-block pair of paragraph 10, in the form the black pair takes: for `ε = 1` the pair is `{c − U_q, c}`, for
`ε = −1` it is `{c, c + U_q}`; the base `x = v + k U_p` is a V-cut vertex and both ends lie in the closed polygon `E`. -/
def BlockPairAt (frame : ChildFrame) (c : Site) : Prop :=
  (frame.eps = 1 ∧ ∃ (v : Site) (k : ℤ), v ∈ frame.freeV ∧
      c - (frame.parents.even.den, frame.parents.even.num) =
        v + (k * (2 * frame.parents.odd.den), k * (2 * frame.parents.odd.num)) ∧
      c - (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon ∧
      c ∈ frame.closedPolygon) ∨
  (frame.eps = -1 ∧ ∃ (v : Site) (k : ℤ), v ∈ frame.freeV ∧
      c = v + (k * (2 * frame.parents.odd.den), k * (2 * frame.parents.odd.num)) ∧
      c ∈ frame.closedPolygon ∧ c + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon)

/-- Paragraph 10 for the black pair: a V-block pair cannot be a black pair with black translate `c + σ`. -/
theorem not_rising_of_blockPair {F : Field} (hP : frame.Packet F) {c : Site}
    (hb : laplacian F c = -1) (hbs : laplacian F (c + frame.shortShift) = -1) (hblk : BlockPairAt frame c) :
    False := by
  rcases hblk with ⟨he, v, k, hv, hx, hxE, hcE⟩ | ⟨he, v, k, hv, hx, hcE, hcuE⟩
  · have h1 := frame.laplacian_shortShift_eq_of_eps_one hP he c
    have hb' : laplacian F (c - (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [← h1]
      exact hbs
    have hbu : laplacian F (c - (frame.parents.even.den, frame.parents.even.num) +
        (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [sub_add_cancel]
      exact hb
    exact frame.black_centres_contradiction hP hv hx hxE (by rw [sub_add_cancel]; exact hcE) hb' hbu
  · have h1 := frame.laplacian_shortShift_eq_of_eps_neg_one hP he c
    have hbu : laplacian F (c + (frame.parents.even.den, frame.parents.even.num)) = -1 := by
      rw [← h1]
      exact hbs
    exact frame.black_centres_contradiction hP hv hx hcE hcuE hb hbu

/-- `NoBlackPairRise` from the paper's case cover (fixes/Q3.md, paragraphs 3–10). The named leaves are the cases this
file does not close (see the report); the first common chart and the V block are proved. -/
theorem noBlackPairRise_of_cases {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (firstCommon adjacentPositive exitSameSlip negativeNonfree negativeFreeH negativeFreeV exceptionalVertex :
      Site → Site → Prop)
    (hcover : ∀ c i, RisingBlackPair F frame.shortShift c i →
      firstCommon c i ∨ adjacentPositive c i ∨ exitSameSlip c i ∨ negativeNonfree c i ∨ negativeFreeH c i ∨
        negativeFreeV c i ∨ exceptionalVertex c i)
    (hfirst : ∀ c i, firstCommon c i →
      frame.chainPotential F 1 i ≤ frame.chainPotential F 1 c ∧
        frame.price F (c + frame.shortShift) ≤ frame.price F (i + frame.shortShift))
    (hadj : ∀ c i, adjacentPositive c i → ¬ RisingBlackPair F frame.shortShift c i)
    (hexit : ∀ c i, exitSameSlip c i → ¬ RisingBlackPair F frame.shortShift c i)
    (hnonfree : ∀ c i, negativeNonfree c i → ¬ RisingBlackPair F frame.shortShift c i)
    (hfreeH : ∀ c i, negativeFreeH c i → ¬ RisingBlackPair F frame.shortShift c i)
    (hfreeV : ∀ c i, negativeFreeV c i → BlockPairAt frame c)
    (hexc : ∀ c i, exceptionalVertex c i → ¬ RisingBlackPair F frame.shortShift c i) :
    NoBlackPairRise F frame.shortShift := by
  intro c hc hpar hbs i hi hone
  have hr : RisingBlackPair F frame.shortShift c i := ⟨hi, hc, hpar, hbs, hone⟩
  rcases hcover c i hr with h | h | h | h | h | h | h
  · obtain ⟨h1, h2⟩ := hfirst c i h
    exact frame.rise_excluded_at_edge F h1 h2 hone
  · exact hadj c i h hr
  · exact hexit c i h hr
  · exact hnonfree c i h hr
  · exact hfreeH c i h hr
  · exact frame.not_rising_of_blockPair hP hc hbs (hfreeV c i h)
  · exact hexc c i h hr

/-- The first common chart from `OldPolicyData`: its chain potential does not increase along the retained edges
(`chainNonincreasing`); the named inputs are that the first-chart edges are retained and that the shifted price does not
decrease on them. -/
theorem noBlackPairRise_of_oldPolicy {G : Field} {seed : Site → Site → Prop} (frame : ChildFrame) (hP : frame.Packet G)
    (P : OldPolicyData frame G seed)
    (firstCommon adjacentPositive exitSameSlip negativeNonfree negativeFreeH negativeFreeV exceptionalVertex :
      Site → Site → Prop)
    (hcover : ∀ c i, RisingBlackPair G frame.shortShift c i →
      firstCommon c i ∨ adjacentPositive c i ∨ exitSameSlip c i ∨ negativeNonfree c i ∨ negativeFreeH c i ∨
        negativeFreeV c i ∨ exceptionalVertex c i)
    (hfirst_retained : ∀ c i, firstCommon c i → P.retained c i)
    (hfirst_price : ∀ c i, firstCommon c i →
      frame.price G (c + frame.shortShift) ≤ frame.price G (i + frame.shortShift))
    (hadj : ∀ c i, adjacentPositive c i → ¬ RisingBlackPair G frame.shortShift c i)
    (hexit : ∀ c i, exitSameSlip c i → ¬ RisingBlackPair G frame.shortShift c i)
    (hnonfree : ∀ c i, negativeNonfree c i → ¬ RisingBlackPair G frame.shortShift c i)
    (hfreeH : ∀ c i, negativeFreeH c i → ¬ RisingBlackPair G frame.shortShift c i)
    (hfreeV : ∀ c i, negativeFreeV c i → BlockPairAt frame c)
    (hexc : ∀ c i, exceptionalVertex c i → ¬ RisingBlackPair G frame.shortShift c i) :
    NoBlackPairRise G frame.shortShift :=
  frame.noBlackPairRise_of_cases hP firstCommon adjacentPositive exitSameSlip negativeNonfree negativeFreeH
    negativeFreeV exceptionalVertex hcover
    (fun c i h => ⟨P.chainNonincreasing 1 (Or.inl rfl) c i (hfirst_retained c i h), hfirst_price c i h⟩)
    hadj hexit hnonfree hfreeH hfreeV hexc

end ChildFrame

end FLatticePaper.Induction
