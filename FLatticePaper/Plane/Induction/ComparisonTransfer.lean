import FLatticePaper.Plane.Induction.ComparisonFields
import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.W1Lower

/-! Task 70 part 2 (c): `P`, `J₊`, `J₋` do not increase along retained black edges and forced white edges (fixes/Q1.md
paragraphs 3–4).

Sources (archive, `canonical_evidence/chronology/B2_INDEPENDENT_PRERANK_AUDIT.md` §3, "Every required bulk edge is covered"):

* (T) the contained unit-proof transfer, quoted: "At a contact forced-white root, induct on its actual finite contained unit
  proof. If its forced input were not a contact, integrality forces the other input to be a contact and makes `m` black at the
  root. Propagation around the proof square then creates a finite empty clause for `m`." Lean: `hT`, with `ForcedEdge` the
  contained unit proof (`SquareClauses.ForcedEdge`, seeded by the policy) and `EC m` the finite empty clause for `m`.
* (W) the W1 no-refutation transferred to `m`, quoted: "`m` is an even-parity translate of `F` plus affine, so the current W1
  global no-refutation statement transfers to it." Lean: `hW : ¬ EC m` for each comparison field `m`.

Black roots need no transfer: `contact_black_E` (binarity of `m` and `m ≤ F` on `E`) gives both inputs as contacts.

The rounded values: `J₊ = ⌈D₊/2⌉` with `D₊ ∈ [0, 2]`, so `J₊ = 0` exactly when `D₊ = 0`, the contact of `cmpUp`; `J₋ = ⌈D₋/2⌉`
with `D₋ ∈ [−2, 0]`, so `J₋ = −1` exactly when `D₋ = −2`, the contact of `cmpDown`. `P` takes the lower value `c₀ − 1` exactly at the
contact of `cmpLow`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The lower comparison field `m(z) = F(z − v) + ε a·z + c₀ − 1` of the word (paragraph 4(a)). -/
noncomputable def cmpLowW (word : Word) : Field :=
  FLatticePaper.Contacts.cmpLow (standardField word) (frameAt word).parentShift (frameAt word).eps
    ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den) (frameAt word).cutPrice

/-- The upper comparison field `m(z) = F(z + σ)` of the word (paragraph 4(b), `D₊`). -/
noncomputable def cmpUpW (word : Word) : Field :=
  FLatticePaper.Contacts.cmpUp (standardField word) (frameAt word).shortShift

/-- The lower-slip comparison field `m(z) = F(z − σ) − 2` of the word (paragraph 4(b), `D₋`). -/
noncomputable def cmpDownW (word : Word) : Field :=
  FLatticePaper.Contacts.cmpDown (standardField word) (frameAt word).shortShift

/-- The three comparison fields of paragraph 4. -/
def IsCmpField (word : Word) (m : Field) : Prop :=
  m = cmpLowW word ∨ m = cmpUpW word ∨ m = cmpDownW word

/-- Each comparison field lies below `F` on the closed polygon (ComparisonFields). -/
theorem isCmp_le_on_E {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {m : Field} (hm : IsCmpField word m) :
    ∀ z ∈ (frameAt word).closedPolygon, m z ≤ standardField word z := by
  rcases hm with rfl | rfl | rfl
  · exact cmpLow_le_of_price hWord
  · exact cmpUp_le_of_slip h hSE
  · exact cmpDown_le_of_slip h hSE

/-- Each comparison field is binary (ComparisonContacts). -/
theorem isCmp_binary {word : Word} (hpk : (frameAt word).Packet (standardField word)) {m : Field}
    (hm : IsCmpField word m) : ∀ z, laplacian m z = -1 ∨ laplacian m z = 0 := by
  rcases hm with rfl | rfl | rfl
  · intro z
    exact FLatticePaper.Contacts.cmpLow_binary hpk.binary (FLatticePaper.W1Lower.evenSite_parentShift (frameAt word)) _ _ _ z
  · intro z
    exact FLatticePaper.Contacts.cmpUp_binary hpk.binary (evenSite_shortShift (frameAt word)) z
  · intro z
    exact FLatticePaper.Contacts.cmpDown_binary hpk.binary (evenSite_shortShift (frameAt word)) z

/-- The primitive price is at its lower value `c₀ − 1` exactly at the contacts of `cmpLow`. -/
theorem price_eq_low_iff {word : Word} (z : Site) :
    (frameAt word).price (standardField word) z = (frameAt word).cutPrice - 1 ↔
      standardField word z = cmpLowW word z := by
  unfold cmpLowW FLatticePaper.Contacts.cmpLow ChildFrame.price ChildFrame.parentSlope
  have e : z + -(frameAt word).parentShift = z - (frameAt word).parentShift := (sub_eq_add_neg z _).symm
  rw [e]
  have hs : (frameAt word).eps * (((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).1 * z.1 +
      ((frameAt word).parents.odd.num, -(frameAt word).parents.odd.den).2 * z.2) =
      (frameAt word).eps * ((frameAt word).parents.odd.num * z.1 - (frameAt word).parents.odd.den * z.2) := by
    ring
  constructor
  · intro hh
    linarith [hs]
  · intro hh
    linarith [hs]

/-- The reflected lower slip `D₋(z) = F z − F (z − σ) ∈ [−2, 0]` on the closed polygon (`slip_reflect_gen`). -/
theorem slip_minus_range {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word)) :
    ∀ z ∈ (frameAt word).closedPolygon,
      -2 ≤ standardField word z - standardField word (z + -(frameAt word).shortShift) ∧
        standardField word z - standardField word (z + -(frameAt word).shortShift) ≤ 0 := by
  intro z hz
  have hR := slipRange_of_strong h hSE ((frameAt word).centre - z) ((frameAt word).reflect_mem_closedPolygon hz)
  have hsr := (frameAt word).slip_reflect_gen hpk (frameAt word).shortShift ((frameAt word).centre - z)
  rw [sub_sub_cancel, (frameAt word).tGrade_shortShift] at hsr
  constructor <;> linarith [hR.1, hR.2, hsr]

/-- **The transfer step (T) and the W1 no-refutation (W) give the forced-contact property.** A contact forced-white root `c` of the
comparison field `m` has every forced input `o` a contact: otherwise (T) produces an empty clause `EC m`, which (W) excludes.
`EC m` is "a finite empty clause for `m`" in the unit closure. -/
theorem forced_contact_transfer {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {m : Field} (hm : IsCmpField word m) {c o : Site} (hw : laplacian (standardField word) c = 0)
    (hc : standardField word c = m c) (hf : SquareClauses.ForcedEdge (standardField word) seed c o)
    (hoE : o ∈ (frameAt word).closedPolygon) : standardField word o = m o := by
  by_contra hne
  have hle := isCmp_le_on_E h hSE hWord hm o hoE
  exact hW m hm (hT m hm c o hw hc hf hoE (lt_of_le_of_ne hle (fun e => hne e.symm)))

/-- A black centre's inputs lie in the closed polygon (`ChildFrame.black_input_mem`). -/
theorem input_mem_black {word : Word} (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    i ∈ (frameAt word).closedPolygon := by
  rcases hi with rfl | rfl
  · exact (frameAt word).black_input_mem hpk hcE hb (Or.inl rfl)
  · exact (frameAt word).black_input_mem hpk hcE hb (Or.inr rfl)

/-- At a black contact of the field `m`, the input `i` is a contact too (`contact_black_E`). -/
theorem black_pair {word : Word} (hpk : (frameAt word).Packet (standardField word)) {m : Field}
    (hm : ∀ z, laplacian m z = -1 ∨ laplacian m z = 0)
    (hle : ∀ z ∈ (frameAt word).closedPolygon, m z ≤ standardField word z)
    {c i : Site} (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (heq : standardField word c = m c) (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    standardField word i = m i := by
  have hp := contact_black_E hpk hm hle hcE hb heq
  rcases hi with rfl | rfl
  · exact hp.1
  · exact hp.2

/-! ### Forced white edges. -/

/-- `P` does not increase along a forced white edge (task 70 (c)): a lower contact root forces a lower contact input (T, W);
a non-lower root has `P = c₀` on the whole range. -/
theorem price_nonincrease_forced {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) c := by
  have hpc := hWord.priceRange c hcE
  have hpo := hWord.priceRange o hoE
  by_cases hlow : (frameAt word).price (standardField word) c = (frameAt word).cutPrice - 1
  · have hc' := (price_eq_low_iff c).mp hlow
    have ho' := forced_contact_transfer h hSE hWord EC hT hW (Or.inl rfl) hw hc' hf hoE
    have := (price_eq_low_iff o).mpr ho'
    omega
  · omega

/-- `J₊` does not increase along a forced white edge (task 70 (c)): `J₊ = ⌈D₊/2⌉` with `D₊ ∈ [0, 2]`; `J₊ = 0` exactly at the
contact of `cmpUp`, whose forced input is a contact (T, W). -/
theorem jplus_nonincrease_forced {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + (frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + (frameAt word).shortShift) + 1) / 2 := by
  have hDc := slipRange_of_strong h hSE c hcE
  have hDo := slipRange_of_strong h hSE o hoE
  by_cases hz : standardField word c - standardField word (c + (frameAt word).shortShift) = 0
  · have hc' : standardField word c = cmpUpW word c := by
      unfold cmpUpW FLatticePaper.Contacts.cmpUp
      linarith
    have ho' := forced_contact_transfer h hSE hWord EC hT hW (Or.inr (Or.inl rfl)) hw hc' hf hoE
    unfold cmpUpW FLatticePaper.Contacts.cmpUp at ho'
    omega
  · omega

/-- `J₋` does not increase along a forced white edge (task 70 (c)): `J₋ = ⌈D₋/2⌉` with `D₋ ∈ [−2, 0]`; `J₋ = −1` exactly at the
contact of `cmpDown`, whose forced input is a contact (T, W). -/
theorem jminus_nonincrease_forced {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hpk : (frameAt word).Packet (standardField word)) {seed : Site → Site → Prop}
    (EC : Field → Prop)
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → SquareClauses.ForcedEdge (standardField word) seed c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EC m)
    (hW : ∀ m, IsCmpField word m → ¬ EC m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : SquareClauses.ForcedEdge (standardField word) seed c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 := by
  have hDc := slip_minus_range h hSE hpk c hcE
  have hDo := slip_minus_range h hSE hpk o hoE
  by_cases hz : standardField word c - standardField word (c + -(frameAt word).shortShift) = -2
  · have hc' : standardField word c = cmpDownW word c := by
      unfold cmpDownW FLatticePaper.Contacts.cmpDown
      linarith
    have ho' := forced_contact_transfer h hSE hWord EC hT hW (Or.inr (Or.inr rfl)) hw hc' hf hoE
    unfold cmpDownW FLatticePaper.Contacts.cmpDown at ho'
    omega
  · omega

/-! ### Black edges: both inputs of a black contact root are contacts (`contact_black_E`, no transfer needed). -/

/-- `P` does not increase along a black edge (task 70 (c)). -/
theorem price_nonincrease_black {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c := by
  have hiE := input_mem_black hpk hcE hb hi
  have hpc := hWord.priceRange c hcE
  have hpi := hWord.priceRange i hiE
  by_cases hlow : (frameAt word).price (standardField word) c = (frameAt word).cutPrice - 1
  · have hc' := (price_eq_low_iff c).mp hlow
    have hpair := black_pair hpk (isCmp_binary hpk (Or.inl rfl : IsCmpField word (cmpLowW word)))
      (isCmp_le_on_E h hSE hWord (Or.inl rfl : IsCmpField word (cmpLowW word))) hcE hb hc' hi
    have := (price_eq_low_iff i).mpr hpair
    omega
  · omega

/-- `J₊` does not increase along a black edge (task 70 (c)): a black `c` with `D₊(c) = 0` is a contact of `cmpUp`, so both inputs
have `D₊ = 0`; otherwise `J₊(c) = 1` and `J₊ ≤ 1` everywhere. -/
theorem jplus_nonincrease_black {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    (standardField word i - standardField word (i + (frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + (frameAt word).shortShift) + 1) / 2 := by
  have hiE := input_mem_black hpk hcE hb hi
  have hDc := slipRange_of_strong h hSE c hcE
  have hDi := slipRange_of_strong h hSE i hiE
  by_cases hz : standardField word c - standardField word (c + (frameAt word).shortShift) = 0
  · have hc' : standardField word c =
        FLatticePaper.Contacts.cmpUp (standardField word) (frameAt word).shortShift c := by
      unfold FLatticePaper.Contacts.cmpUp
      linarith
    have hpair := black_pair hpk
      (fun z => FLatticePaper.Contacts.cmpUp_binary hpk.binary (evenSite_shortShift (frameAt word)) z)
      (cmpUp_le_of_slip h hSE) hcE hb hc' hi
    unfold FLatticePaper.Contacts.cmpUp at hpair
    omega
  · omega

/-- `J₋` does not increase along a black edge (task 70 (c)): a black `c` with `D₋(c) = −2` is a contact of `cmpDown`, so both inputs
have `D₋ = −2`; otherwise `J₋(c) = 0` and `J₋ ≤ 0` everywhere. -/
theorem jminus_nonincrease_black {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word)) {c i : Site}
    (hcE : c ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) c = -1)
    (hi : i = FLatticePaper.incomingNeg c ∨ i = FLatticePaper.incomingPos c) :
    (standardField word i - standardField word (i + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 := by
  have hiE := input_mem_black hpk hcE hb hi
  have hDc := slip_minus_range h hSE hpk c hcE
  have hDi := slip_minus_range h hSE hpk i hiE
  by_cases hz : standardField word c - standardField word (c + -(frameAt word).shortShift) = -2
  · have hc' : standardField word c =
        FLatticePaper.Contacts.cmpDown (standardField word) (frameAt word).shortShift c := by
      unfold FLatticePaper.Contacts.cmpDown
      linarith
    have hpair := black_pair hpk
      (fun z => FLatticePaper.Contacts.cmpDown_binary hpk.binary (evenSite_shortShift (frameAt word)) z)
      (cmpDown_le_of_slip h hSE) hcE hb hc' hi
    unfold FLatticePaper.Contacts.cmpDown at hpair
    omega
  · omega

end FLatticePaper.Induction
