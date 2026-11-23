import FLatticePaper.Plane.Induction.ComparisonTransfer

/-! Task 70 part 2 (c): the concrete empty clause and the satisfiability form of (W).

* `EmptyClause G`: the unseeded unit closure of `G` derives a conflict. Either (i) a white site has two distinct forced inputs, or
  (ii) a unit square has every corner black or forced into the square.
* `HasSatSelection F` (W): `F` has a white input selection satisfying every unit square clause. This is what the W1 construction
  supplies; `hasSat_of_strict` derives it from a strictly decreasing rank (`squareClauses_of_strict`).
* `not_emptyClause_of_sat`: a satisfying selection excludes `EmptyClause`, by `forced_sound` and `keptInside_of_black`.
* `not_emptyClause_of_cmp`: each comparison field `m` has `laplacian m c = laplacian F (c + t)` for an even `t` (`t = −v`, `σ`, `−σ`;
  the affine term and the constant do not change the Laplacian). The translated selection `z ↦ sel (z + t) − t` satisfies the clauses
  of `m`, so `EmptyClause m` fails.

(T) is not in this module: `forced_contact_of_sat` takes it as the hypothesis `hT`, with the concrete `EmptyClause`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The empty clause of the unseeded unit closure of `G`: (i) a white site with two distinct forced inputs, or (ii) a unit square
each of whose corners is black or forced into the square. -/
def EmptyClause (G : Field) : Prop :=
  (∃ c i j, laplacian G c = 0 ∧ ForcedEdge G (fun _ _ => False) c i ∧ ForcedEdge G (fun _ _ => False) c j ∧ i ≠ j) ∨
  (∃ a b : ℤ, ∀ c ∈ squareCorners a b, laplacian G c = -1 ∨
      (laplacian G c = 0 ∧ ∃ i, ForcedEdge G (fun _ _ => False) c i ∧ i ∈ squareCorners a b))

/-- (W): a white input selection satisfying every unit square clause. -/
def HasSatSelection (F : Field) : Prop :=
  ∃ sel : Site → Site, (∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c) ∧
    ∀ a b : ℤ, SquareClauseSat F sel a b

/-- (W) from a strictly decreasing rank: a black site's inputs have smaller rank, and each white site has an input of smaller rank. -/
theorem hasSat_of_strict {F R : Field} (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i + 1 ≤ R c)
    (hwhite : ∀ c, ∃ i, laplacian F c = 0 → (i = incomingNeg c ∨ i = incomingPos c) ∧ R i + 1 ≤ R c) :
    HasSatSelection F := by
  choose sel hsel using hwhite
  exact ⟨sel, fun c hc => (hsel c hc).1, fun a b => squareClauses_of_strict hbin hblack hsel a b⟩

/-- A satisfying white selection excludes the empty clause. -/
theorem not_emptyClause_of_sat {G : Field} {sel : Site → Site}
    (hsel : ∀ c, laplacian G c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hsq : ∀ a b : ℤ, SquareClauseSat G sel a b) : ¬ EmptyClause G := by
  intro h
  unfold EmptyClause at h
  rcases h with ⟨c, i, j, _, hi, hj, hij⟩ | ⟨a, b, hall⟩
  · have h1 := forced_sound G (fun _ _ => False) sel hsel (fun _ _ h => h.elim) hsq c i hi
    have h2 := forced_sound G (fun _ _ => False) sel hsel (fun _ _ h => h.elim) hsq c j hj
    exact hij (h1.symm.trans h2)
  · apply hsq a b
    intro c hc
    rcases hall c hc with hb | ⟨hw, i, hi, hin⟩
    · exact keptInside_of_black hc hb
    · unfold keptInside
      rw [if_neg (by rw [hw]; norm_num), forced_sound G (fun _ _ => False) sel hsel (fun _ _ h => h.elim) hsq c i hi]
      exact hin

/-- Translating a unit square by an even `t`: a corner `x` of `(a, b)` shifts to a corner of `(a + t₁, b + t₂)`. -/
theorem mem_corners_add (a b : ℤ) (t x : Site) :
    x + t ∈ squareCorners (a + t.1) (b + t.2) ↔ x ∈ squareCorners a b := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨t1, t2⟩ := t
  show (x1 + t1, x2 + t2) ∈ squareCorners (a + t1) (b + t2) ↔ (x1, x2) ∈ squareCorners a b
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- The kept-inside condition is preserved under an even shift that matches the Laplacians. -/
theorem keptInside_shift {F G : Field} {sel : Site → Site} {a b : ℤ} {t : Site} (ht : EvenSite t)
    (hL : ∀ c, laplacian G c = laplacian F (c + t)) (c : Site) :
    keptInside G (fun z => sel (z + t) - t) (squareCorners a b) c ↔
      keptInside F sel (squareCorners (a + t.1) (b + t.2)) (c + t) := by
  unfold keptInside
  by_cases h : laplacian G c = -1
  · have h' : laplacian F (c + t) = -1 := by rw [← hL c]; exact h
    simp only [h, h', ↓reduceIte, FLatticePaper.Contacts.incomingNeg_add_even c t ht, FLatticePaper.Contacts.incomingPos_add_even c t ht]
    rw [mem_corners_add, mem_corners_add]
  · have h' : ¬ laplacian F (c + t) = -1 := by rw [← hL c]; exact h
    simp only [h, h', ↓reduceIte]
    have := mem_corners_add a b t (sel (c + t) - t)
    rw [sub_add_cancel] at this
    exact this.symm

/-- The translated selection satisfies the translated square clauses. -/
theorem sat_shift {F G : Field} {sel : Site → Site} {t : Site} (ht : EvenSite t)
    (hL : ∀ c, laplacian G c = laplacian F (c + t)) (hsat : ∀ a b : ℤ, SquareClauseSat F sel a b) :
    ∀ a b : ℤ, SquareClauseSat G (fun z => sel (z + t) - t) a b := by
  intro a b hall
  apply hsat (a + t.1) (b + t.2)
  intro c' hc'
  have hc : c' - t ∈ squareCorners a b := by
    rw [← mem_corners_add a b t (c' - t), sub_add_cancel]
    exact hc'
  have h := hall (c' - t) hc
  rw [keptInside_shift ht hL, sub_add_cancel] at h
  exact h

/-- The translated selection is a white input selection. -/
theorem white_sel_shift {F G : Field} {sel : Site → Site} {t : Site} (ht : EvenSite t)
    (hL : ∀ c, laplacian G c = laplacian F (c + t))
    (hsel : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c) :
    ∀ c, laplacian G c = 0 →
      (fun z => sel (z + t) - t) c = incomingNeg c ∨ (fun z => sel (z + t) - t) c = incomingPos c := by
  intro c hc
  have hF : laplacian F (c + t) = 0 := by rw [← hL c]; exact hc
  rcases hsel (c + t) hF with h | h
  · left
    show sel (c + t) - t = incomingNeg c
    rw [h, FLatticePaper.Contacts.incomingNeg_add_even c t ht]
    simp
  · right
    show sel (c + t) - t = incomingPos c
    rw [h, FLatticePaper.Contacts.incomingPos_add_even c t ht]
    simp

/-- A Laplacian-matching even translate of a field with (W) has no empty clause. -/
theorem not_emptyClause_of_hasSat {G F : Field} {t : Site} (ht : EvenSite t)
    (hL : ∀ c, laplacian G c = laplacian F (c + t)) (hF : HasSatSelection F) : ¬ EmptyClause G := by
  obtain ⟨sel, hsel, hsat⟩ := hF
  exact not_emptyClause_of_sat (white_sel_shift ht hL hsel) (sat_shift ht hL hsat)

/-- **(W) for the comparison fields.** Each comparison field `m` has no empty clause, given (W) for `F = standardField word`. -/
theorem not_emptyClause_of_cmp {word : Word} (hW : HasSatSelection (standardField word)) {m : Field}
    (hm : IsCmpField word m) : ¬ EmptyClause m := by
  rcases hm with rfl | rfl | rfl
  · refine not_emptyClause_of_hasSat (t := -(frameAt word).parentShift)
      (FLatticePaper.Contacts.evenSite_neg (FLatticePaper.W1Lower.evenSite_parentShift (frameAt word))) ?_ hW
    intro c
    unfold cmpLowW FLatticePaper.Contacts.cmpLow
    rw [FLatticePaper.Contacts.laplacian_affine (fun z => standardField word (z + -(frameAt word).parentShift)) _ _ _ c,
      FLatticePaper.Contacts.laplacian_shift_even _ _
        (FLatticePaper.Contacts.evenSite_neg (FLatticePaper.W1Lower.evenSite_parentShift (frameAt word))) c]
  · refine not_emptyClause_of_hasSat (t := (frameAt word).shortShift) (evenSite_shortShift (frameAt word)) ?_ hW
    intro c
    unfold cmpUpW FLatticePaper.Contacts.cmpUp
    exact FLatticePaper.Contacts.laplacian_shift_even _ _ (evenSite_shortShift (frameAt word)) c
  · refine not_emptyClause_of_hasSat (t := -(frameAt word).shortShift)
      (FLatticePaper.Contacts.evenSite_neg (evenSite_shortShift (frameAt word))) ?_ hW
    intro c
    unfold cmpDownW FLatticePaper.Contacts.cmpDown
    rw [FLatticePaper.Contacts.laplacian_sub_const _ 2 c,
      FLatticePaper.Contacts.laplacian_shift_even _ _
        (FLatticePaper.Contacts.evenSite_neg (evenSite_shortShift (frameAt word))) c]

/-- **Forced contacts from (T) and (W).** For the unseeded unit proofs, a contact forced-white root has a contact forced input,
where (T) is the hypothesis `hT` with the concrete empty clause and (W) is `hW`. -/
theorem forced_contact_of_sat {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {m : Field} (hm : IsCmpField word m) {c o : Site} (hw : laplacian (standardField word) c = 0)
    (hc : standardField word c = m c) (hf : ForcedEdge (standardField word) (fun _ _ => False) c o)
    (hoE : o ∈ (frameAt word).closedPolygon) : standardField word o = m o :=
  forced_contact_transfer h hSE hWord EmptyClause hT (fun _ hm' => not_emptyClause_of_cmp hW hm') hm hw hc hf hoE

/-- `P` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem price_nonincrease_forced_of_sat {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (frameAt word).price (standardField word) o ≤ (frameAt word).price (standardField word) c :=
  price_nonincrease_forced h hSE hWord EmptyClause hT (fun _ hm' => not_emptyClause_of_cmp hW hm') hw hcE hf hoE

/-- `J₊` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem jplus_nonincrease_forced_of_sat {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + (frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + (frameAt word).shortShift) + 1) / 2 :=
  jplus_nonincrease_forced h hSE hWord EmptyClause hT (fun _ hm' => not_emptyClause_of_cmp hW hm') hw hcE hf hoE

/-- `J₋` does not increase along unseeded forced white edges, from (T) with the concrete empty clause and (W). -/
theorem jminus_nonincrease_forced_of_sat {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hW : HasSatSelection (standardField word))
    (hT : ∀ m, IsCmpField word m → ∀ c o, laplacian (standardField word) c = 0 →
      standardField word c = m c → ForcedEdge (standardField word) (fun _ _ => False) c o →
      o ∈ (frameAt word).closedPolygon → m o < standardField word o → EmptyClause m)
    {c o : Site} (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 :=
  jminus_nonincrease_forced h hSE hWord (packet_of_strong h hSE) EmptyClause hT
    (fun _ hm' => not_emptyClause_of_cmp hW hm') hw hcE hf hoE

end FLatticePaper.Induction
