import FLatticePaper.Plane.Induction.CollarSquare
import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.CollarCReflect
import FLatticePaper.Plane.Induction.FaceWitness
import FLatticePaper.Plane.Induction.FaceReflect
import FLatticePaper.Plane.Induction.CollarTie

/-! # The explicit parent square of a forcing unit (Q33 (2)): `PSquare` from the unit fields of `ForcedEdge`

`psquare_of_unit` is the proof of `W1NonfreeOut.parentSquareOut_of_forced` with the unit data as arguments, so the explicit square
(the corners `q0 q1 q2` of the square `(a,b)` and the rejected output `o`) is available. -/

namespace FLatticePaper.CollarChain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1NonfreeOut FLatticePaper.CollarSquare FLatticePaper.W1SheetSquare FLatticePaper.W1PrivateSquare
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1CollarFrame FLatticePaper.W1NonfreeHsqC FLatticePaper.ChainWire

theorem psquare_of_unit {G : Field} {R : Site → Site → Prop} {c o : Site} {a b : ℤ} (inside : Site → Site)
    (hq : RetainQuota G R)
    (hret : ∀ c' i, ForcedEdge G (fun _ _ => False) c' i → R c' i)
    (hfw : ∀ z i, R z i → laplacian G z = 0 → ∀ o', ForcedEdge G (fun _ _ => False) z o' → o' = i)
    (hc : c ∈ squareCorners a b) (hw : laplacian G c = 0)
    (ho : o = incomingNeg c ∨ o = incomingPos c) (hout : o ∉ squareCorners a b)
    (hin : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = -1 ∨
      (laplacian G c' = 0 ∧ inside c' ∈ squareCorners a b ∧
        (inside c' = incomingNeg c' ∨ inside c' = incomingPos c')))
    (hforced : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian G c' = 0 →
      ForcedEdge G (fun _ _ => False) c' (inside c')) :
    ∃ q0 q1 q2 : Site, PSquare G R c q0 q1 q2 o a b := by
  have h : ForcedEdge G (fun _ _ => False) c o :=
    ForcedEdge.unit inside hc hw ho hout hin hforced
  -- the retained inputs of a corner `x ≠ c` of the square: its in-square input
  have key : ∀ x ∈ squareCorners a b, x ≠ c → ∀ w ∈ squareCorners a b,
      (w = incomingNeg x ∨ w = incomingPos x) → R x w := by
    intro x hx hxc w hwS hwin
    rcases hin x hx hxc with hb | ⟨hw0, hinS, hinIn⟩
    · have hb2 := hq.1 x hb
      rcases hwin with rfl | rfl
      · exact hb2.1
      · exact hb2.2
    · have hR := hret x (inside x) (hforced x hx hxc hw0)
      have hu := square_input_unique hx hinS hwS hinIn hwin
      rw [hu] at hR
      exact hR
  -- the in-square input `q₀` of `c`, the rejected input (not retained)
  obtain ⟨q0, hq0S, hq0in⟩ := square_corner_input a b hc
  have hq0o : q0 ≠ o := fun e => hout (by rw [← e]; exact hq0S)
  have hq0c : q0 ≠ c := edge_ne (show Edge q0 c from hq0in)
  have hRc0 : ¬ R c q0 := fun hR => hq0o (hfw c q0 hR hw o h).symm
  -- the in-square input `q₁` of `q₀`, retained by `q₀`
  obtain ⟨q1, hq1S, hq1in⟩ := square_corner_input a b hq0S
  have hq1c : q1 ≠ c := fun e => no_two_cycle (show Edge q0 c from hq0in) (e ▸ hq1in)
  have hR01 : R q0 q1 := key q0 hq0S hq0c q1 hq1S hq1in
  -- the in-square input `q₂` of `q₁`, retained by `q₁`
  obtain ⟨q2, hq2S, hq2in⟩ := square_corner_input a b hq1S
  have hq2c : q2 ≠ c := by
    intro e
    have hp : EvenSite q2 ↔ ¬ EvenSite c := by
      rw [edge_parity hq2in, edge_parity hq1in, edge_parity hq0in]
      tauto
    rw [e] at hp
    rcases em (EvenSite c) with h' | h'
    · exact hp.1 h' h'
    · exact h' (hp.2 h')
  have hR12 : R q1 q2 := key q1 hq1S hq1c q2 hq2S hq2in
  have hq1q0 : q1 ≠ q0 := edge_ne hq1in
  have hq2q1 : q2 ≠ q1 := edge_ne hq2in
  have hq2q0 : q2 ≠ q0 := fun e => no_two_cycle hq1in (e ▸ hq2in)
  -- the in-square input of `q₂` is `c`
  have hEc2 : Edge c q2 := by
    obtain ⟨w, hwS, hwin⟩ := square_corner_input a b hq2S
    have hcov := square_exhaust hc hq0S hq1S hq2S hwS (Ne.symm hq0c) (Ne.symm hq1c) (Ne.symm hq2c)
      (Ne.symm hq1q0) (Ne.symm hq2q0) (Ne.symm hq2q1)
    rcases hcov with e | e | e | e
    · rw [e] at hwin
      exact hwin
    · exfalso
      rw [e] at hwin
      have hp := edge_parity hwin
      have hp1 := edge_parity hq1in
      have hp2 := edge_parity hq2in
      have key2 : EvenSite q2 ↔ EvenSite q0 := by
        rw [hp2, hp1, not_not]
      rcases em (EvenSite q0) with h' | h'
      · exact (hp.1 h') (key2.2 h')
      · exact h' (hp.2 (fun h2 => h' (key2.1 h2)))
    · exfalso
      rw [e] at hwin
      exact no_two_cycle hq2in hwin
    · exfalso
      rw [e] at hwin
      exact edge_ne hwin rfl
  have hR2c : R q2 c := key q2 hq2S hq2c c hc hEc2
  have hq0q1 : q0 ≠ q1 := Ne.symm hq1q0
  have hq1q2 : q1 ≠ q2 := Ne.symm hq2q1
  have hq0q2 : q0 ≠ q2 := Ne.symm hq2q0
  refine ⟨q0, q1, q2, hc, hq0S, hq1S, hq2S, ?_, hq0q1, hq1q2, hq0q2, hq0in, hRc0, hq1in, hq2in, hEc2,
    hR01, hR12, hR2c, ho, hout, hret c o h, fun j hj => (hfw c j hj hw o h).symm, ?_, ?_, ?_⟩
  · intro c' hc' hne
    rcases square_exhaust hc hq0S hq1S hq2S hc' (Ne.symm hq0c) (Ne.symm hq1c) (Ne.symm hq2c)
      (Ne.symm hq1q0) (Ne.symm hq2q0) (Ne.symm hq2q1) with e | e | e | e
    · exact absurd e hne
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · rcases hin q0 hq0S hq0c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq0S hinS hq1S hinIn hq1in
      have hj' := hfw q0 j hj hw0 (inside q0) (hforced q0 hq0S hq0c hw0)
      rw [hu] at hj'
      exact hj'.symm
  · rcases hin q1 hq1S hq1c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq1S hinS hq2S hinIn hq2in
      have hj' := hfw q1 j hj hw0 (inside q1) (hforced q1 hq1S hq1c hw0)
      rw [hu] at hj'
      exact hj'.symm
  · rcases hin q2 hq2S hq2c with hb | ⟨hw0, hinS, hinIn⟩
    · exact Or.inl hb
    · refine Or.inr ⟨hw0, fun j hj => ?_⟩
      have hu := square_input_unique hq2S hinS hc hinIn hEc2
      have hj' := hfw q2 j hj hw0 (inside q2) (hforced q2 hq2S hq2c hw0)
      rw [hu] at hj'
      exact hj'.symm



/-- The square with corners shifted by `c`. -/
theorem mem_squareCorners_shift (x c : Site) (a b : ℤ) :
    x ∈ squareCorners a b ↔ x - c ∈ squareCorners (a - c.1) (b - c.2) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- The input of a shifted site, for an even shift. -/
theorem incomingNeg_sub_even (x c : Site) (hc : EvenSite c) : incomingNeg (x - c) = incomingNeg x - c := by
  have hp : EvenSite (x - c) ↔ EvenSite x := by
    unfold EvenSite at hc ⊢
    simp only [Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> omega
  unfold incomingNeg
  by_cases h : EvenSite x
  · rw [if_pos h, if_pos (hp.2 h)]
    refine Prod.ext ?_ ?_
    all_goals (simp <;> omega)
  · rw [if_neg h, if_neg (fun h' => h (hp.1 h'))]
    refine Prod.ext ?_ ?_
    all_goals (simp <;> omega)

theorem incomingPos_sub_even (x c : Site) (hc : EvenSite c) : incomingPos (x - c) = incomingPos x - c := by
  have hp : EvenSite (x - c) ↔ EvenSite x := by
    unfold EvenSite at hc ⊢
    simp only [Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> omega
  unfold incomingPos
  by_cases h : EvenSite x
  · rw [if_pos h, if_pos (hp.2 h)]
    refine Prod.ext ?_ ?_
    all_goals (simp <;> omega)
  · rw [if_neg h, if_neg (fun h' => h (hp.1 h'))]
    refine Prod.ext ?_ ?_
    all_goals (simp <;> omega)

/-- **The explicit square translated by a span vector** (the same square at the translate, with the same arrows). -/
theorem psquare_sub_span {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (z u : Site), R z u →
      R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) {ρ q0 q1 q2 o : Site} {a b : ℤ}
    (h : PSquare G R ρ q0 q1 q2 o a b) :
    PSquare G R (ρ - v) (q0 - v) (q1 - v) (q2 - v) (o - v) (a - v.1) (b - v.2) := by
  have hl : ∀ x, laplacian G (x - v) = laplacian G x := fun x => by
    have := laplacian_span_inv frame G hP hv (x - v)
    rw [sub_add_cancel] at this
    exact this.symm
  have hev : EvenSite v := evenSite_of_span frame hv
  obtain ⟨i, j, rfl⟩ := hv
  have hiff : ∀ x u, R (x - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j) ↔ R x u := by
    intro x u
    have := FLatticePaper.ChainWire.deck_shift_iff hdeck i j (x - frame.child.modifiedDeck.combine i j)
      (u - frame.child.modifiedDeck.combine i j)
    simp only [sub_add_cancel] at this
    exact this
  obtain ⟨hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3, hR0, hR1, hR2, ho, hout, hRo, hun,
    hL0, hL1, hL2⟩ := h
  have hcov' : ∀ c' ∈ squareCorners (a - (frame.child.modifiedDeck.combine i j).1) (b - (frame.child.modifiedDeck.combine i j).2),
      c' ≠ ρ - frame.child.modifiedDeck.combine i j →
      c' = q0 - frame.child.modifiedDeck.combine i j ∨ c' = q1 - frame.child.modifiedDeck.combine i j ∨
        c' = q2 - frame.child.modifiedDeck.combine i j := by
    intro c' hc' hne
    have h1 : c' + frame.child.modifiedDeck.combine i j ∈ squareCorners a b := by
      rw [mem_squareCorners_shift (c' + frame.child.modifiedDeck.combine i j) (frame.child.modifiedDeck.combine i j) a b,
        add_sub_cancel_right]
      exact hc'
    have hne2 : c' + frame.child.modifiedDeck.combine i j ≠ ρ := fun e => hne (by rw [← e, add_sub_cancel_right])
    rcases hcov _ h1 hne2 with e | e | e
    · exact Or.inl (eq_sub_of_add_eq e)
    · exact Or.inr (Or.inl (eq_sub_of_add_eq e))
    · exact Or.inr (Or.inr (eq_sub_of_add_eq e))
  refine ⟨(mem_squareCorners_shift ρ _ a b).1 hz, (mem_squareCorners_shift q0 _ a b).1 hq0,
    (mem_squareCorners_shift q1 _ a b).1 hq1, (mem_squareCorners_shift q2 _ a b).1 hq2, hcov',
    fun e => hne01 (sub_left_inj.mp e), fun e => hne12 (sub_left_inj.mp e), fun e => hne02 (sub_left_inj.mp e),
    ?_, fun hn => hrej ((hiff ρ q0).1 hn), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hin with e | e
    · rw [incomingNeg_sub_even ρ _ hev, e]
      exact Or.inl rfl
    · rw [incomingPos_sub_even ρ _ hev, e]
      exact Or.inr rfl
  · unfold Edge at hE1 ⊢
    rw [incomingNeg_sub_even q0 _ hev, incomingPos_sub_even q0 _ hev]
    rcases hE1 with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr (by rw [e])
  · unfold Edge at hE2 ⊢
    rw [incomingNeg_sub_even q1 _ hev, incomingPos_sub_even q1 _ hev]
    rcases hE2 with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr (by rw [e])
  · unfold Edge at hE3 ⊢
    rw [incomingNeg_sub_even q2 _ hev, incomingPos_sub_even q2 _ hev]
    rcases hE3 with e | e
    · exact Or.inl (by rw [e])
    · exact Or.inr (by rw [e])
  · exact (hiff q0 q1).2 hR0
  · exact (hiff q1 q2).2 hR1
  · exact (hiff q2 ρ).2 hR2
  · rcases ho with e | e
    · rw [incomingNeg_sub_even ρ _ hev, e]
      exact Or.inl rfl
    · rw [incomingPos_sub_even ρ _ hev, e]
      exact Or.inr rfl
  · exact fun hn => hout ((mem_squareCorners_shift o _ a b).2 hn)
  · exact (hiff ρ o).2 hRo
  · intro k hk
    have hk' : R ρ (k + frame.child.modifiedDeck.combine i j) := by
      rw [← hiff ρ (k + frame.child.modifiedDeck.combine i j), add_sub_cancel_right]
      exact hk
    exact eq_sub_of_add_eq (hun _ hk')
  · rcases hL0 with e | ⟨e, u⟩
    · exact Or.inl (by rw [hl]; exact e)
    · refine Or.inr ⟨by rw [hl]; exact e, fun k hk => ?_⟩
      have hk' : R q0 (k + frame.child.modifiedDeck.combine i j) := by
        rw [← hiff q0 (k + frame.child.modifiedDeck.combine i j), add_sub_cancel_right]
        exact hk
      exact eq_sub_of_add_eq (u _ hk')
  · rcases hL1 with e | ⟨e, u⟩
    · exact Or.inl (by rw [hl]; exact e)
    · refine Or.inr ⟨by rw [hl]; exact e, fun k hk => ?_⟩
      have hk' : R q1 (k + frame.child.modifiedDeck.combine i j) := by
        rw [← hiff q1 (k + frame.child.modifiedDeck.combine i j), add_sub_cancel_right]
        exact hk
      exact eq_sub_of_add_eq (u _ hk')
  · rcases hL2 with e | ⟨e, u⟩
    · exact Or.inl (by rw [hl]; exact e)
    · refine Or.inr ⟨by rw [hl]; exact e, fun k hk => ?_⟩
      have hk' : R q2 (k + frame.child.modifiedDeck.combine i j) := by
        rw [← hiff q2 (k + frame.child.modifiedDeck.combine i j), add_sub_cancel_right]
        exact hk
      exact eq_sub_of_add_eq (u _ hk')

/-- **The tie agreement** (the named input `hagree`, Q15): at a tie `Ψ x = 0`, the `A` and `C` policies retain the same arrows. -/
def TieAgreeHyp (word : Word) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps) : Prop :=
  ∀ x : Site, sheetPsi word x = 0 → ∀ y : Site,
    FLatticePaper.Induction.sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x y ↔
      FLatticePaper.Induction.sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
        (frameAt word).centre x y

/-- **The forced-case top-square strictness** (the named input `hTop`): for a strict white centre `c` with `Ψ c ≥ 0` (no collar or
nonfree condition is used), and for every unit square of a `ForcedEdgeIn` at a strict translate `ρ = zTurn(c − lv) + v` of the parent
root, its child corners `lv + zTurnInv (q − v)` are strictly interior. Numerically checked on the sheet field for words of length at
most 4 (no violation; without the white or the `Ψ ≥ 0` condition there are violations). -/
def TopStrictHyp (word : Word) (G : Field)
    (lvAt : Site) : Prop :=
  ∀ (c v ρ o : Site) (a b : ℤ) (inside : Site → Site),
    FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c →
    (FLatticePaper.FaceWitness.BottomWit (frameAt word) c ∨ FLatticePaper.FaceWitness.AlignedWit (frameAt word) c) →
    ρ = zTurn (c - lvAt) + v →
    FLatticePaper.W1.StrictInterior (frameAt (conjWord word)).child.num
      (frameAt (conjWord word)).child.den ρ →
    (∀ c' ∈ squareCorners a b, FLatticePaper.W1.StrictInterior (frameAt (conjWord word)).child.num
      (frameAt (conjWord word)).child.den c') →
    ρ ∈ squareCorners a b → laplacian G ρ = 0 → (o = incomingNeg ρ ∨ o = incomingPos ρ) → o ∉ squareCorners a b →
    (∀ c' ∈ squareCorners a b, c' ≠ ρ → laplacian G c' = -1 ∨
      (laplacian G c' = 0 ∧ inside c' ∈ squareCorners a b ∧
        (inside c' = incomingNeg c' ∨ inside c' = incomingPos c'))) →
    (∀ c' ∈ squareCorners a b, c' ≠ ρ → laplacian G c' = 0 →
      FLatticePaper.W1.ForcedEdgeIn G (FLatticePaper.W1.StrictInterior (frameAt (conjWord word)).child.num
        (frameAt (conjWord word)).child.den) (fun _ _ => False) c' (inside c')) →
    ∀ q ∈ squareCorners a b,
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        (lvAt + FLatticePaper.W1Phase.zTurnInv (q - v))


/-- **The free-root strictness** (the named input `hRow`): for a strict white collar centre `c` with `Ψ c ≥ 0` whose parent root is
free up to a deck translate, an explicit parent square at the root has strictly interior child corners (the six face rows, Q33 (1)). -/
def RowStrictHyp (word : Word) (G : Field) (R : Site → Site → Prop) : Prop :=
  ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q2)

/-- **The collar `HsqAt` at the centres with `Ψ c ≥ 0`**, from the named inputs `TopStrictHyp` (the forced case, from the unit square of
the derivation at a strict translate) and `RowStrictHyp` (the free-root case). -/
theorem collar_psquare_A {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hTop : TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift)
    (hRow : RowStrictHyp word (standardField (conjWord word)) P.retained)
    {c : Site} (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0) (hc0 : 0 ≤ sheetPsi word c)
    (hcoll : FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c)
    (hWit : FLatticePaper.FaceWitness.BottomWit (frameAt word) c ∨ FLatticePaper.FaceWitness.AlignedWit (frameAt word) c) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q2) := by
  subst hs
  have hP : (frameAt (conjWord word)).Packet (standardField (conjWord word)) := hSE.packet
  have hdeck := deck_of_games G (frameAt word).eps_unit P.toOldPolicyWitness hW
  have hr0 := FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE hc0 hM
  by_cases hnf : Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))
  · obtain ⟨v, hv, hSI⟩ := nonfree_bridge (frameAt (conjWord word)) _ hnf
    have hlap : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift) + v) = 0 := by
      rw [laplacian_span_inv (frameAt (conjWord word)) (standardField (conjWord word)) hP hv]
      exact hr0
    obtain ⟨o, hD⟩ := hW1 _ hSI hlap
    cases hD with
    | seed hs0 => exact False.elim hs0
    | @unit a b _ _ inside hR hc hw' ho hout hin hforced =>
      have hforcedF : ∀ c' ∈ squareCorners a b, c' ≠ zTurn (c - (frameAt word).sheetShift) + v →
          laplacian (standardField (conjWord word)) c' = 0 →
          ForcedEdge (standardField (conjWord word)) (fun _ _ => False) c' (inside c') :=
        fun c' hc' hne h0 => FLatticePaper.W1.forcedEdgeIn_forced (hforced c' hc' hne h0)
      obtain ⟨q0, q1, q2, hPS⟩ := psquare_of_unit inside P.quota P.forcedRetained P.forcedWhiteUnique hc hw' ho hout hin
        hforcedF
      have hPS' := psquare_sub_span hP hdeck hv hPS
      rw [add_sub_cancel_right] at hPS'
      have hstr := hTop c v (zTurn (c - (frameAt word).sheetShift) + v) o a b inside hcS hM hc0 hWit rfl hSI hR hc hw' ho hout hin hforced
      exact ⟨q0 - v, q1 - v, q2 - v, o - v, a - v.1, b - v.2, hPS', hstr q0 hPS.2.1, hstr q1 hPS.2.2.1,
        hstr q2 hPS.2.2.2.1⟩
  · exact hRow c hcS hM hc0 hcoll hnf

/-- **The collar `HsqAt` at a tie with a top or opposite witness (`Ψ c = 0`)**: the reflected partner `R - c` has the bottom or aligned
witness (`topWit_bottom`, `oppositeWit_alignedWit`), so its explicit parent square gives the `C`-square at `c` by `hsq_C_collar_le`,
with the tie agreement `hagree` as the named premise. -/
theorem hC_tie {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hTop : TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift)
    (hRow : RowStrictHyp word (standardField (conjWord word)) P.retained)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hagree : TieAgreeHyp word P)
    {c : Site} (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0) (hψ : sheetPsi word c = 0)
    (hcoll : FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c)
    (hWit : FLatticePaper.FaceWitness.TopWit (frameAt word) c ∨ FLatticePaper.FaceWitness.OppositeWit (frameAt word) c) :
    HsqAt word P c := by
  have hcS' : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).centre - c) :=
    (FLatticePaper.CollarTop.strict_reflect_centre (frameAt word) c).mpr hcS
  have hM' : laplacian (MW word) ((frameAt word).centre - c) = 0 := by
    rw [FLatticePaper.W1NonfreeHsqC.lap_MW_reflect hw hSE c]
    exact hM
  have hψ' : 0 ≤ sheetPsi word ((frameAt word).centre - c) := by
    rw [FLatticePaper.W1NonfreeHsqC.psi_reflect hw hSE c, hψ]
    simp
  have hcoll' := FLatticePaper.CollarCReflect.collar_reflect hw hcoll
  have hWit' : FLatticePaper.FaceWitness.BottomWit (frameAt word) ((frameAt word).centre - c) ∨
      FLatticePaper.FaceWitness.AlignedWit (frameAt word) ((frameAt word).centre - c) := by
    rcases hWit with h | h
    · exact Or.inl (FLatticePaper.FaceReflect.topWit_bottom (frameAt word) h)
    · exact Or.inr (FLatticePaper.FaceReflect.oppositeWit_alignedWit (frameAt word) h)
  obtain ⟨q0, q1, q2, o, qa, qb, hPS, h0, h1, h2⟩ :=
    collar_psquare_A hw hSE P hs hW1 G hW hTop hRow hcS' hM' hψ' hcoll' hWit'
  exact FLatticePaper.CollarTie.hsq_C_collar_le hw hSE P hs hW1 hfree hagree hcS (le_of_eq hψ)
    (fun _ => hM) hPS h0 h1 h2

/-- **The collar `HsqAt` at the centres with `Ψ c ≥ 0`**: the explicit parent square (`collar_psquare_A`) and `hsq_collar_of_psquare`
for a bottom or aligned witness; a top or opposite witness forces `Ψ c = 0` by `PsiFaceSign`, and then `hC_tie`. -/
theorem hcollar_A {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hTop : TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift)
    (hRow : RowStrictHyp word (standardField (conjWord word)) P.retained)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hPsi : FLatticePaper.FaceWitness.PsiFaceSign word)
    (hagree : TieAgreeHyp word P) :
    ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
      HsqAt word P c := by
  intro c hcS hM hc0 hcoll
  rcases FLatticePaper.FaceReflect.collar_witness_cases (frameAt word) hcoll with hB | hA | hT | hO
  · obtain ⟨q0, q1, q2, o, qa, qb, hPS, h0, h1, h2⟩ :=
      collar_psquare_A hw hSE P hs hW1 G hW hTop hRow hcS hM hc0 hcoll (Or.inl hB)
    exact hsq_collar_of_psquare hw hSE P hcS hc0 hM hPS h0 h1 h2
  · obtain ⟨q0, q1, q2, o, qa, qb, hPS, h0, h1, h2⟩ :=
      collar_psquare_A hw hSE P hs hW1 G hW hTop hRow hcS hM hc0 hcoll (Or.inr hA)
    exact hsq_collar_of_psquare hw hSE P hcS hc0 hM hPS h0 h1 h2
  · have hψ : sheetPsi word c = 0 := le_antisymm ((hPsi c hcS hM hcoll).2 (Or.inl hT)) hc0
    exact hC_tie hw hSE P hs hW1 G hW hTop hRow hfree hagree hcS hM hψ hcoll (Or.inl hT)
  · have hψ : sheetPsi word c = 0 := le_antisymm ((hPsi c hcS hM hcoll).2 (Or.inr hO)) hc0
    exact hC_tie hw hSE P hs hW1 G hW hTop hRow hfree hagree hcS hM hψ hcoll (Or.inr hO)

/-- **The collar `HsqAt` at the centres with `Ψ c < 0`**: the reflected centre `K − c` is on the collar (`collar_reflect`), its
explicit parent square gives the `C`-square at `c` (`hsq_C_collar`). The reflected centre has `Ψ > 0`, so by `PsiFaceSign` its
witness is bottom or aligned. -/
theorem hC_of_inputs {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hTop : TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift)
    (hRow : RowStrictHyp word (standardField (conjWord word)) P.retained)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hPsi : FLatticePaper.FaceWitness.PsiFaceSign word) :
    ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c → sheetPsi word c < 0 →
      HsqAt word P c := by
  intro c hcS hM hcoll hc0
  have hcS' : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).centre - c) :=
    (FLatticePaper.CollarTop.strict_reflect_centre (frameAt word) c).mpr hcS
  have hM' : laplacian (MW word) ((frameAt word).centre - c) = 0 := by
    rw [FLatticePaper.W1NonfreeHsqC.lap_MW_reflect hw hSE c]
    exact hM
  have hpos : 0 ≤ sheetPsi word ((frameAt word).centre - c) := by
    rw [FLatticePaper.W1NonfreeHsqC.psi_reflect hw hSE c]
    omega
  have hpos' : 0 < sheetPsi word ((frameAt word).centre - c) := by
    rw [FLatticePaper.W1NonfreeHsqC.psi_reflect hw hSE c]
    omega
  have hcoll' := FLatticePaper.CollarCReflect.collar_reflect hw hcoll
  have hWit' : FLatticePaper.FaceWitness.BottomWit (frameAt word) ((frameAt word).centre - c) ∨
      FLatticePaper.FaceWitness.AlignedWit (frameAt word) ((frameAt word).centre - c) := by
    rcases FLatticePaper.FaceReflect.collar_witness_cases (frameAt word) hcoll' with hB | hA | hT | hO
    · exact Or.inl hB
    · exact Or.inr hA
    · exact absurd ((hPsi _ hcS' hM' hcoll').2 (Or.inl hT)) (not_le.mpr hpos')
    · exact absurd ((hPsi _ hcS' hM' hcoll').2 (Or.inr hO)) (not_le.mpr hpos')
  obtain ⟨q0, q1, q2, o, qa, qb, hPS, h0, h1, h2⟩ :=
    collar_psquare_A hw hSE P hs hW1 G hW hTop hRow hcS' hM' hpos hcoll' hWit'
  exact FLatticePaper.CollarCReflect.hsq_C_collar hw hSE P hs hW1 hfree hcS hc0 hPS h0 h1 h2

/-- **W1Forced of the sheet minimum, end to end**: `hcollar` is derived from `hcollar_A` (the `Ψ ≥ 0` chart, from the named `hTop`, `hRow`)
and the named `hC` (the `Ψ < 0` chart). -/
theorem W1Forced_end_to_end {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : FLatticePaper.Induction.StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (δ : ℤ) (hη : (frameAt word).eps = -δ) (hδ : δ = 1 ∨ δ = -1)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hH : ∀ z ∈ (frameAt (conjWord word)).freeH, laplacian (standardField (conjWord word)) z = 0 →
      ParentSquareOut (standardField (conjWord word)) P.retained z)
    (hVodd : ∀ z ∈ (frameAt (conjWord word)).freeV, ¬ EvenSite z →
      laplacian (standardField (conjWord word)) z = 0 → ParentSquareOut (standardField (conjWord word)) P.retained z)
    (hX3 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      (z.1, z.2 - δ) ∈ (frameAt (conjWord word)).freeV ∧
        laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 →
      P.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    (hTop : TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift)
    (hRow : RowStrictHyp word (standardField (conjWord word)) P.retained)
    (hPsi : FLatticePaper.FaceWitness.PsiFaceSign word)
    (hagree : TieAgreeHyp word P) :
    FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) := by
  have hdeck := deck_of_games G (frameAt word).eps_unit P.toOldPolicyWitness hW
  have hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) :=
    fun c h0 hM hnf =>
      hfree_of_classes hη hδ hSE.packet hW1 (G.game (frameAt word).eps (frameAt word).eps_unit)
        P.toOldPolicyWitness hW hdeck hH hVodd hX3 hX1 hX2 hcanon hnf
        (FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE h0 hM)
  have hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c → HsqAt word P c := by
    intro c hcS hM hcoll
    by_cases h0 : 0 ≤ sheetPsi word c
    · exact hcollar_A hw hSE P hs hW1 G hW hTop hRow hfree hPsi hagree c hcS hM h0 hcoll
    · exact hC_of_inputs hw hSE P hs hW1 G hW hTop hRow hfree hPsi c hcS hM hcoll (by omega)
  exact FLatticePaper.ChainWire.W1Forced_chain hw hSE P hs hW1 hn3 δ hη hδ G hW hH hVodd hX3 hX1 hX2 hcanon hcollar


end FLatticePaper.CollarChain
