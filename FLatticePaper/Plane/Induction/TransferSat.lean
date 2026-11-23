import FLatticePaper.Plane.Induction.PassagePR
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.W1PrivateSquare

/-! # (T) by the direct proof: the transfer at a forced white contact (Q18)

Let `F`, `m` be binary fields with `m ≤ F` on `P`, and let `c` be a white site of `F` with `F c = m c` (a contact). Let `c` have a forced
derivation `ForcedEdgeIn F R ∅ c o` whose unit squares have all corners, and all inputs of those corners, in `P` (`StarIn P`). Take
satisfying selections `selF` (for `F`) and `selM` (for `m`). The modified selection `modSel` of `F` is the comparison selection at white
contacts with `m` white, the zero-gap input at white contacts with `m` black, and `selF` elsewhere.

* `sq_sat_mod`: `modSel` satisfies every such square. If some corner is a contact, contacts propagate to the in-square input (the gap identity
  at a contact), so around the four-cycle of the square every corner is a contact; then `selM` keeps each in-square input, contradicting
  `selM`'s clause for `m`. Otherwise `modSel = selF` on the square.
* `forced_sound_R`: a forced input of `c` is the value of the selection on squares satisfying the clause.
* `gap_zero_of_forced`: so the forced input `o` of the contact `c` has `F o = m o`.

Hence the transfer `(T)` in `ComparisonTransfer`'s form holds for derivations contained in `P` (`transfer_hT_of_contained`); the
unrestricted form needs the containment, since the gap signs are only known on `P`. -/

namespace FLatticePaper.TransferSat

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1PrivateSquare FLatticePaper.PassagePR

/-- A site and both of its inputs lie in `P`. -/
abbrev StarIn (P : Site → Prop) (c : Site) : Prop := P c ∧ P (incomingNeg c) ∧ P (incomingPos c)

open Classical in
/-- The modified selection of `F`: at a white contact `c` (`F c = m c`), the selection of `m` when `m` is white at `c`, and the input of zero
gap when `m` is black at `c`; elsewhere `selF`. -/
noncomputable def modSel (F m : Field) (selF selM : Site → Site) (c : Site) : Site :=
  if laplacian F c = 0 ∧ F c = m c then
    (if laplacian m c = 0 then selM c
     else if F (incomingNeg c) = m (incomingNeg c) then incomingNeg c else incomingPos c)
  else selF c

/-- The gap identity at a contact: the two input gaps sum to `ΔF − Δm`. -/
theorem gap_sum {F m : Field} {c : Site} (hc : F c = m c) :
    (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) =
      laplacian F c - laplacian m c := by
  unfold laplacian
  omega

/-- **The modified selection satisfies a square** whose corners and corner-inputs lie in `P`, given satisfying selections for `F` and `m`. -/
theorem sq_sat_mod {F m : Field} {P : Site → Prop} {selF selM : Site → Site} {a b : ℤ}
    (hF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0) (hm : ∀ z, laplacian m z = -1 ∨ laplacian m z = 0)
    (hle : ∀ z, P z → m z ≤ F z) (hstar : ∀ x ∈ squareCorners a b, StarIn P x)
    (hsqF : SquareClauseSat F selF a b) (hsqM : SquareClauseSat m selM a b) :
    SquareClauseSat F (modSel F m selF selM) a b := by
  intro hall
  -- the gaps of the two inputs of a corner of the square are nonnegative
  have gaps : ∀ x ∈ squareCorners a b, 0 ≤ F (incomingNeg x) - m (incomingNeg x) ∧
      0 ≤ F (incomingPos x) - m (incomingPos x) := by
    intro x hx
    obtain ⟨-, hn, hp⟩ := hstar x hx
    have h1 := hle _ hn
    have h2 := hle _ hp
    constructor <;> omega
  -- a contact propagates to each in-square input of the square
  have prop : ∀ x ∈ squareCorners a b, F x = m x → ∀ w ∈ squareCorners a b,
      (w = incomingNeg x ∨ w = incomingPos x) → F w = m w := by
    intro x hx hcx w hw hwin
    obtain ⟨g1, g2⟩ := gaps x hx
    have hsum := gap_sum hcx
    rcases hF x with hfx | hfx
    · rcases hm x with hmx | hmx
      · rcases hwin with rfl | rfl <;> omega
      · omega
    rcases hm x with hmx | hmx
    · -- `F` white, `m` black at `x`: the modified selection picks the zero-gap input, which is the in-square input
      have hfx' : ¬ laplacian F x = -1 := by rw [hfx]; norm_num
      have hmx' : ¬ laplacian m x = 0 := by rw [hmx]; norm_num
      have hk := hall x hx
      unfold keptInside at hk
      rw [if_neg hfx'] at hk
      unfold modSel at hk
      rw [if_pos (And.intro hfx hcx), if_neg hmx'] at hk
      by_cases hz : F (incomingNeg x) = m (incomingNeg x)
      · rw [if_pos hz] at hk
        have huniq : w = incomingNeg x := square_input_unique hx hw hk hwin (Or.inl rfl)
        rw [huniq]
        exact hz
      · rw [if_neg hz] at hk
        have hpos : F (incomingPos x) = m (incomingPos x) := by omega
        have huniq : w = incomingPos x := square_input_unique hx hw hk hwin (Or.inr rfl)
        rw [huniq]
        exact hpos
    · -- both `F` and `m` white at `x`: both gaps vanish
      rcases hwin with rfl | rfl <;> omega
  by_cases hcont : ∃ x0 ∈ squareCorners a b, F x0 = m x0
  swap
  · -- no contact on the square: the modified selection is `selF` there
    apply hsqF
    intro c hc
    have hne : ¬ F c = m c := fun e => hcont ⟨c, hc, e⟩
    have hk := hall c hc
    have hmod : modSel F m selF selM c = selF c := by
      unfold modSel
      rw [if_neg (fun h => hne h.2)]
    unfold keptInside at hk ⊢
    rw [hmod] at hk
    exact hk
  obtain ⟨x0, hx0, hc0⟩ := hcont
  -- the in-square inputs `y1 y2 y3` of `x0`, all contacts by propagation
  obtain ⟨y1, hy1, hy1in⟩ := square_corner_input a b hx0
  have hc1 : F y1 = m y1 := prop x0 hx0 hc0 y1 hy1 hy1in
  obtain ⟨y2, hy2, hy2in⟩ := square_corner_input a b hy1
  have hc2 : F y2 = m y2 := prop y1 hy1 hc1 y2 hy2 hy2in
  obtain ⟨y3, hy3, hy3in⟩ := square_corner_input a b hy2
  have hc3 : F y3 = m y3 := prop y2 hy2 hc2 y3 hy3 hy3in
  -- the four corners `x0 y1 y2 y3` are distinct: a directed four-cycle
  have hxy : x0 ≠ y1 := fun e => edge_ne (show Edge y1 x0 from hy1in) e.symm
  have hxz : x0 ≠ y2 := fun e =>
    no_two_cycle (show Edge y1 x0 from hy1in) (show Edge x0 y1 by rw [e]; exact hy2in)
  have hxw : x0 ≠ y3 := fun e => by
    have p1 := edge_parity hy1in
    have p2 := edge_parity hy2in
    have p3 := edge_parity hy3in
    rw [e] at p1
    tauto
  have hyz : y1 ≠ y2 := fun e => edge_ne (show Edge y2 y1 from hy2in) e.symm
  have hyw : y1 ≠ y3 := fun e =>
    no_two_cycle (show Edge y1 y2 by rw [e]; exact hy3in) (show Edge y2 y1 from hy2in)
  have hzw : y2 ≠ y3 := fun e => edge_ne (show Edge y3 y2 from hy3in) e.symm
  have hcov : ∀ z ∈ squareCorners a b, F z = m z := by
    intro z hz
    rcases square_exhaust hx0 hy1 hy2 hy3 hz hxy hxz hxw hyz hyw hzw with e | e | e | e <;> rw [e]
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  -- every corner is a contact, so the modified selection agrees with `selM` at each white corner: a contradiction with `selM`'s clause
  apply hsqM
  intro c hc
  have hcF := hcov c hc
  obtain ⟨g1, g2⟩ := gaps c hc
  have hsumc := gap_sum hcF
  by_cases hlm : laplacian m c = -1
  · exact keptInside_of_black hc hlm
  · have hlm0 : laplacian m c = 0 := by
      rcases hm c with h | h
      · exact absurd h hlm
      · exact h
    have hlF : laplacian F c = 0 := by
      rcases hF c with h | h
      · omega
      · exact h
    have hk := hall c hc
    unfold keptInside at hk
    rw [if_neg (by rw [hlF]; norm_num)] at hk
    unfold modSel at hk
    rw [if_pos (And.intro hlF hcF), if_pos hlm0] at hk
    unfold keptInside
    rw [if_neg hlm]
    exact hk

/-- Forced inputs are the values of the selection on squares satisfying the clause (the proof of `forced_sound`, with the clause only on the
squares of the derivation). -/
theorem forced_sound_R {F : Field} {R : Site → Prop} (sel : Site → Site)
    (hsel : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hsq : ∀ a b, (∀ c ∈ squareCorners a b, R c) → SquareClauseSat F sel a b) :
    ∀ c i, FLatticePaper.W1.ForcedEdgeIn F R (fun _ _ => False) c i → sel c = i := by
  intro c i h
  induction h with
  | seed hs => exact False.elim hs
  | @unit a b c o inside hR hc hw ho hout hin hforced ih =>
    have hkeptOther : ∀ c', c' ∈ squareCorners a b → c' ≠ c → keptInside F sel (squareCorners a b) c' := by
      intro c' hc' hne
      rcases hin c' hc' hne with hb | ⟨hw', hmem, _⟩
      · exact keptInside_of_black hc' hb
      · unfold keptInside
        rw [if_neg (by rw [hw']; norm_num), ih c' hc' hne hw']
        exact hmem
    have hkc : ¬ keptInside F sel (squareCorners a b) c := by
      intro hk
      exact hsq a b hR (fun c'' hc'' => by
        by_cases hcc : c'' = c
        · rw [hcc]
          exact hk
        · exact hkeptOther c'' hc'' hcc)
    have hcS : sel c ∉ squareCorners a b := by
      unfold keptInside at hkc
      rw [if_neg (by rw [hw]; norm_num)] at hkc
      exact hkc
    obtain ⟨t, ht, htin⟩ := square_corner_input a b hc
    have hto : t ≠ o := fun h => hout (h ▸ ht)
    have hsc := hsel c hw
    have hsc_t : sel c ≠ t := fun h => hcS (h ▸ ht)
    rcases hsc with h1 | h1 <;> rcases htin with h2 | h2 <;> rcases ho with h3 | h3 <;>
      first
      | exact h1.trans h3.symm
      | exact absurd (h1.trans h2.symm) hsc_t
      | exact absurd (h2.trans h3.symm) hto

/-- **The forced input of a contact has zero gap.** For a white contact `c` of `F` with `F c = m c` and a forced derivation of `c` contained
in `P`, the forced input `o` satisfies `F o = m o`. -/
theorem gap_zero_of_forced {F m : Field} {P R : Site → Prop} (hR : ∀ c, R c → StarIn P c)
    (hF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0) (hm : ∀ z, laplacian m z = -1 ∨ laplacian m z = 0)
    (hle : ∀ z, P z → m z ≤ F z)
    {selF selM : Site → Site}
    (hselF : ∀ c, laplacian F c = 0 → selF c = incomingNeg c ∨ selF c = incomingPos c)
    (hsqF : ∀ a b, SquareClauseSat F selF a b)
    (hselM : ∀ c, laplacian m c = 0 → selM c = incomingNeg c ∨ selM c = incomingPos c)
    (hsqM : ∀ a b, SquareClauseSat m selM a b)
    {c o : Site} (hw : laplacian F c = 0) (hc : F c = m c)
    (hf : FLatticePaper.W1.ForcedEdgeIn F R (fun _ _ => False) c o) : F o = m o := by
  have hRc : R c := by
    cases hf with
    | seed hs => exact False.elim hs
    | unit _ hR' hc' _ _ _ _ _ => exact hR' _ hc'
  obtain ⟨-, hn, hp⟩ := hR c hRc
  have hsel' : ∀ x, laplacian F x = 0 → modSel F m selF selM x = incomingNeg x ∨
      modSel F m selF selM x = incomingPos x := by
    intro x hx
    unfold modSel
    by_cases hcx : F x = m x
    · rw [if_pos (And.intro hx hcx)]
      by_cases hlm : laplacian m x = 0
      · rw [if_pos hlm]
        exact hselM x hlm
      · rw [if_neg hlm]
        by_cases hz : F (incomingNeg x) = m (incomingNeg x)
        · rw [if_pos hz]
          exact Or.inl rfl
        · rw [if_neg hz]
          exact Or.inr rfl
    · rw [if_neg (fun h => hcx h.2)]
      exact hselF x hx
  have hsq' : ∀ a b, (∀ x ∈ squareCorners a b, R x) → SquareClauseSat F (modSel F m selF selM) a b :=
    fun a b hRS => sq_sat_mod hF hm hle (fun x hx => hR x (hRS x hx)) (hsqF a b) (hsqM a b)
  have hout := forced_sound_R (modSel F m selF selM) hsel' hsq' c o hf
  unfold modSel at hout
  rw [if_pos (And.intro hw hc)] at hout
  have hsum := gap_sum hc
  have g1 := hle _ hn
  have g2 := hle _ hp
  by_cases hlm : laplacian m c = 0
  · rw [if_pos hlm] at hout
    have ho_in : o = incomingNeg c ∨ o = incomingPos c := by
      rw [← hout]
      exact hselM c hlm
    rcases ho_in with rfl | rfl <;> omega
  · have hlm1 : laplacian m c = -1 := by
      rcases hm c with h | h
      · exact h
      · exact absurd h hlm
    rw [if_neg hlm] at hout
    by_cases hz : F (incomingNeg c) = m (incomingNeg c)
    · rw [if_pos hz] at hout
      rw [← hout]
      exact hz
    · rw [if_neg hz] at hout
      rw [← hout]
      omega

/-- The shifted satisfying selection: a field `G` with `laplacian G c = laplacian F (c + t)` for an even `t` inherits (W). -/
theorem hasSat_of_shift {G F : Field} {t : Site} (ht : EvenSite t)
    (hL : ∀ c, laplacian G c = laplacian F (c + t)) (hF : HasSatSelection F) : HasSatSelection G := by
  obtain ⟨sel, hsel, hsat⟩ := hF
  exact ⟨_, white_sel_shift ht hL hsel, sat_shift ht hL hsat⟩

/-- (W) for the comparison fields, from (W) for `F = standardField word` (the three translates of `ComparisonEmpty`). -/
theorem hasSat_of_cmp {word : Word} (hW : HasSatSelection (standardField word)) {m : Field}
    (hm : IsCmpField word m) : HasSatSelection m := by
  rcases hm with rfl | rfl | rfl
  · refine hasSat_of_shift (t := -(frameAt word).parentShift)
      (FLatticePaper.Contacts.evenSite_neg (FLatticePaper.W1Lower.evenSite_parentShift (frameAt word))) ?_ hW
    intro c
    unfold cmpLowW FLatticePaper.Contacts.cmpLow
    rw [FLatticePaper.Contacts.laplacian_affine (fun z => standardField word (z + -(frameAt word).parentShift)) _ _ _ c,
      FLatticePaper.Contacts.laplacian_shift_even _ _
        (FLatticePaper.Contacts.evenSite_neg (FLatticePaper.W1Lower.evenSite_parentShift (frameAt word))) c]
  · refine hasSat_of_shift (t := (frameAt word).shortShift) (evenSite_shortShift (frameAt word)) ?_ hW
    intro c
    unfold cmpUpW FLatticePaper.Contacts.cmpUp
    exact FLatticePaper.Contacts.laplacian_shift_even _ _ (evenSite_shortShift (frameAt word)) c
  · refine hasSat_of_shift (t := -(frameAt word).shortShift)
      (FLatticePaper.Contacts.evenSite_neg (evenSite_shortShift (frameAt word))) ?_ hW
    intro c
    unfold cmpDownW FLatticePaper.Contacts.cmpDown
    rw [FLatticePaper.Contacts.laplacian_sub_const _ 2 c,
      FLatticePaper.Contacts.laplacian_shift_even _ _
        (FLatticePaper.Contacts.evenSite_neg (evenSite_shortShift (frameAt word))) c]

/-- **(T) in `ComparisonTransfer`'s form, from (W), for derivations contained in the closed polygon.** Let `m` be a comparison field and `c` a
forced white contact of `F = standardField word` with `F c = m c`, forced in the derivation `R` (each square's corners and corner-inputs in the
closed polygon). Then no forced input `o` of `c` in the closed polygon has `m o < F o`: the empty clause is excluded (the hypothesis `hT` of
`ComparisonTransfer`, restricted to contained derivations). -/
theorem transfer_hT_of_contained {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    {R : Site → Prop} (hR : ∀ c, R c → StarIn (fun z => z ∈ (frameAt word).closedPolygon) c)
    {m : Field} (hm : IsCmpField word m) {c o : Site}
    (hw : laplacian (standardField word) c = 0) (hc : standardField word c = m c)
    (hf : FLatticePaper.W1.ForcedEdgeIn (standardField word) R (fun _ _ => False) c o) :
    standardField word o = m o := by
  obtain ⟨selF, hselF, hsqF⟩ := hW
  obtain ⟨selM, hselM, hsqM⟩ := hasSat_of_cmp ⟨selF, hselF, hsqF⟩ hm
  exact gap_zero_of_forced hR (packet_of_strong h hSE).binary (isCmp_binary (packet_of_strong h hSE) hm)
    (fun z hz => isCmp_le_on_E_PR h hSE hPR hm z hz) hselF hsqF hselM hsqM hw hc hf

end FLatticePaper.TransferSat
