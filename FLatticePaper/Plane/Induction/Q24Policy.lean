import FLatticePaper.Plane.Induction.W1MRank
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 72 / Q24 (`fixes/Q24.md`, GAP (b)): the level-`k` policy of the forced-transfer repair, over an abstract pair of fields.

Let `A`, `B` be binary fields on the lattice with `D = A − B`. A `PairData A B β` gives an `A`-policy `pA` with selection `selA`
(kept inputs have `D` no larger, `KA` strictly smaller at equal `D`) and a `B`-policy `pB` with selection `selB` (kept inputs have `D` no
smaller, `KB` strictly smaller at equal `D`). In the chain, `A = F`, `B = g = F(· + ησ)`; the symmetric statement is the swap `(B, A)`
(`PairData.swap`, with `D` replaced by `−D`).

Fix a level `k`. Off the level `D = k` the selection is `selA`. On the level, at a white centre, an input of strictly lower `D` is chosen
if one exists; otherwise the tie: `selB` when both inputs tie, the tied input when the other steps up. The rank `q24Key` is the pair
`(D, KB)` on the level and `(D, KA)` off it. Every kept input has a strictly smaller key (`black_key_lt`, `white_key`), so
`squareClauses_of_burning` gives every unit square clause. Hence every forced literal of `A` is the Q24 selection (`q24_forced`), a flat
white-white tie forces the `B` choice (`forced_flat_eq_selB`), and a disagreement forces neither literal (`neither_forced_of_disagree`).
The rising-edge reduction (`rise_both`) gives both roots unforced. -/

namespace FLatticePaper.Q24Policy

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.W1MRank

/-- The signed difference `D = A − B` of two fields. -/
def Dd (A B : Field) (x : Site) : ℤ := A x - B x

theorem Dd_swap (A B : Field) (x : Site) : Dd B A x = -(Dd A B x) := by
  unfold Dd
  ring

/-- The data of an ordered pair of binary fields `A`, `B` on the lattice: the `A`-policy and the `B`-policy with their selections, the
monotonicity of `D = A − B` along the kept inputs, and the strict keys at equal `D`. -/
structure PairData (A B : Field) (β : Type) [LinearOrder β] where
  pA : Site → Site → Prop
  selA : Site → Site
  pB : Site → Site → Prop
  selB : Site → Site
  KA : Site → β
  KB : Site → β
  binA : ∀ c, laplacian A c = -1 ∨ laplacian A c = 0
  binB : ∀ c, laplacian B c = -1 ∨ laplacian B c = 0
  pA_edge : ∀ c i, pA c i → Edge i c
  pB_edge : ∀ c i, pB c i → Edge i c
  selA_input : ∀ c, laplacian A c = 0 → selA c = incomingNeg c ∨ selA c = incomingPos c
  pA_white : ∀ c, laplacian A c = 0 → ∀ i, pA c i ↔ i = selA c
  pA_black : ∀ c, laplacian A c = -1 → pA c (incomingNeg c) ∧ pA c (incomingPos c)
  squaresA : ∀ a b : ℤ, SquareClauseSat A selA a b
  pA_mono : ∀ c i, pA c i → Dd A B i ≤ Dd A B c
  pA_key : ∀ c i, pA c i → Dd A B i = Dd A B c → KA i < KA c
  selB_input : ∀ c, laplacian B c = 0 → selB c = incomingNeg c ∨ selB c = incomingPos c
  pB_white : ∀ c, laplacian B c = 0 → ∀ i, pB c i ↔ i = selB c
  pB_black : ∀ c, laplacian B c = -1 → pB c (incomingNeg c) ∧ pB c (incomingPos c)
  squaresB : ∀ a b : ℤ, SquareClauseSat B selB a b
  pB_mono : ∀ c i, pB c i → Dd A B c ≤ Dd A B i
  pB_key : ∀ c i, pB c i → Dd A B i = Dd A B c → KB i < KB c

/-- The swapped pair `(B, A)`: the roles of the two policies exchange, and `D` becomes `−D`. -/
def PairData.swap {A B : Field} {β : Type} [LinearOrder β] (P : PairData A B β) : PairData B A β where
  pA := P.pB
  selA := P.selB
  pB := P.pA
  selB := P.selA
  KA := P.KB
  KB := P.KA
  binA := P.binB
  binB := P.binA
  pA_edge := P.pB_edge
  pB_edge := P.pA_edge
  selA_input := P.selB_input
  pA_white := P.pB_white
  pA_black := P.pB_black
  squaresA := P.squaresB
  pA_mono := fun c i h => by
    have h1 := Dd_swap A B i
    have h2 := Dd_swap A B c
    linarith [P.pB_mono c i h]
  pA_key := fun c i h e => P.pB_key c i h (by
    have h1 := Dd_swap A B i
    have h2 := Dd_swap A B c
    linarith)
  selB_input := P.selA_input
  pB_white := P.pA_white
  pB_black := P.pA_black
  squaresB := P.squaresA
  pB_mono := fun c i h => by
    have h1 := Dd_swap A B i
    have h2 := Dd_swap A B c
    linarith [P.pA_mono c i h]
  pB_key := fun c i h e => P.pA_key c i h (by
    have h1 := Dd_swap A B i
    have h2 := Dd_swap A B c
    linarith)

variable {A B : Field} {β : Type} [LinearOrder β]

/-- The Laplacian split: the increments of `D` over the two inputs of a centre sum to the difference of the Laplacians. -/
theorem Dd_split (c : Site) :
    (Dd A B (incomingNeg c) - Dd A B c) + (Dd A B (incomingPos c) - Dd A B c) = laplacian A c - laplacian B c := by
  unfold Dd laplacian
  ring

/-- The Q24 rank: the pair `(D, KB)` on the level `D = k`, and `(D, KA)` off it. -/
def q24Key (P : PairData A B β) (k : ℤ) (x : Site) : Lex (ℤ × β) :=
  toLex (Dd A B x, if Dd A B x = k then P.KB x else P.KA x)

/-- The tie choice at a white centre with no lower input: the `B` selection when both inputs tie, else the tied input. -/
def tieSel (P : PairData A B β) (k : ℤ) (c : Site) : Site :=
  if Dd A B (incomingNeg c) = k ∧ Dd A B (incomingPos c) = k then P.selB c
  else if Dd A B (incomingNeg c) = k then incomingNeg c else incomingPos c

/-- The Q24 selection: the `A`-selection off the level; on it, a lower input if one exists, otherwise the tie. -/
def q24Sel (P : PairData A B β) (k : ℤ) (c : Site) : Site :=
  if Dd A B c = k then
    if Dd A B (incomingNeg c) < k then incomingNeg c
    else if Dd A B (incomingPos c) < k then incomingPos c
    else tieSel P k c
  else P.selA c

theorem key_lt_lower (P : PairData A B β) (k : ℤ) {c x : Site} (h : Dd A B x < Dd A B c) :
    q24Key P k x < q24Key P k c := by
  unfold q24Key
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Off the level, a kept `A`-input of equal `D` decreases the rank. -/
theorem key_lt_A (P : PairData A B β) (k : ℤ) {c x : Site} (hc : Dd A B c ≠ k) (hp : P.pA c x)
    (hD : Dd A B x = Dd A B c) : q24Key P k x < q24Key P k c := by
  have hx : Dd A B x ≠ k := by
    rw [hD]
    exact hc
  unfold q24Key
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hD, ?_⟩
  rw [if_neg hx, if_neg hc]
  exact P.pA_key c x hp hD

/-- On the level, a kept `B`-input of equal `D` decreases the rank. -/
theorem key_lt_B (P : PairData A B β) (k : ℤ) {c x : Site} (hc : Dd A B c = k) (hp : P.pB c x)
    (hD : Dd A B x = Dd A B c) : q24Key P k x < q24Key P k c := by
  have hx : Dd A B x = k := hD.trans hc
  unfold q24Key
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hD, ?_⟩
  rw [if_pos hx, if_pos hc]
  exact P.pB_key c x hp hD

/-- At an `A`-black centre with a tied input `x` and `B` white, the other input is lower. -/
theorem other_lower {c x y : Site} (hb : laplacian A c = -1) (hg : laplacian B c = 0)
    (hx : x = incomingNeg c ∨ x = incomingPos c) (hxk : Dd A B x = Dd A B c)
    (hy : y = incomingNeg c ∨ y = incomingPos c) (hyx : y ≠ x) : Dd A B y < Dd A B c := by
  have hs := Dd_split (A := A) (B := B) c
  rw [hb, hg] at hs
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hyx
  · omega
  · omega
  · exact absurd rfl hyx

/-- On the level, the `B`-policy keeps the tied input `x` when every other input is lower. -/
theorem pB_keeps_tie (P : PairData A B β) {k : ℤ} {c x : Site} (hw : laplacian B c = 0) (hc : Dd A B c = k)
    (hy : ∀ y, (y = incomingNeg c ∨ y = incomingPos c) → y ≠ x → Dd A B y < k) : P.pB c x := by
  have hz := P.selB_input c hw
  have hmono := P.pB_mono c (P.selB c) ((P.pB_white c hw _).mpr rfl)
  by_cases hzx : P.selB c = x
  · rw [← hzx]
    exact (P.pB_white c hw _).mpr rfl
  · exfalso
    have := hy _ hz hzx
    omega

/-- **The black roots decrease.** Both inputs of an `A`-black centre have a smaller Q24 rank. -/
theorem black_key_lt (P : PairData A B β) (k : ℤ) {c x : Site} (hb : laplacian A c = -1)
    (hx : x = incomingNeg c ∨ x = incomingPos c) : q24Key P k x < q24Key P k c := by
  have hkeep : P.pA c x := by
    rcases hx with rfl | rfl
    · exact (P.pA_black c hb).1
    · exact (P.pA_black c hb).2
  have hle := P.pA_mono c x hkeep
  by_cases hc : Dd A B c = k
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower P k hlt
    · have hO : P.pB c x := by
        rcases P.binB c with hg1 | hg0
        · rcases hx with rfl | rfl
          · exact (P.pB_black c hg1).1
          · exact (P.pB_black c hg1).2
        · apply pB_keeps_tie P hg0 hc
          intro y hy1 hyx
          have := other_lower hb hg0 hx heq hy1 hyx
          omega
      exact key_lt_B P k hc hO heq
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower P k hlt
    · exact key_lt_A P k hc hkeep heq

/-- **The white selection decreases.** At an `A`-white centre the Q24 selection is an input whose Q24 rank is smaller. -/
theorem white_key (P : PairData A B β) (k : ℤ) {c : Site} (hw : laplacian A c = 0) :
    (q24Sel P k c = incomingNeg c ∨ q24Sel P k c = incomingPos c) ∧
      q24Key P k (q24Sel P k c) < q24Key P k c := by
  by_cases hc : Dd A B c = k
  · have hs := Dd_split (A := A) (B := B) c
    rw [hw] at hs
    have hgb := P.binB c
    unfold q24Sel
    rw [if_pos hc]
    by_cases hA : Dd A B (incomingNeg c) < k
    · rw [if_pos hA]
      exact ⟨Or.inl rfl, key_lt_lower P k (by rw [hc]; exact hA)⟩
    · rw [if_neg hA]
      by_cases hB : Dd A B (incomingPos c) < k
      · rw [if_pos hB]
        exact ⟨Or.inr rfl, key_lt_lower P k (by rw [hc]; exact hB)⟩
      · rw [if_neg hB]
        by_cases hT : Dd A B (incomingNeg c) = k ∧ Dd A B (incomingPos c) = k
        · have hg0 : laplacian B c = 0 := by omega
          unfold tieSel
          rw [if_pos hT]
          refine ⟨P.selB_input c hg0, ?_⟩
          have hD : Dd A B (P.selB c) = Dd A B c := by
            rcases P.selB_input c hg0 with h | h
            · rw [h]
              omega
            · rw [h]
              omega
          exact key_lt_B P k hc ((P.pB_white c hg0 _).mpr rfl) hD
        · unfold tieSel
          rw [if_neg hT]
          by_cases hA3 : Dd A B (incomingNeg c) = k
          · rw [if_pos hA3]
            have hg1 : laplacian B c = -1 := by omega
            refine ⟨Or.inl rfl, ?_⟩
            exact key_lt_B P k hc (P.pB_black c hg1).1 (by rw [hA3, hc])
          · rw [if_neg hA3]
            have hB3 : Dd A B (incomingPos c) = k := by omega
            have hg1 : laplacian B c = -1 := by omega
            refine ⟨Or.inr rfl, ?_⟩
            exact key_lt_B P k hc (P.pB_black c hg1).2 (by rw [hB3, hc])
  · unfold q24Sel
    rw [if_neg hc]
    have hkeep : P.pA c (P.selA c) := (P.pA_white c hw _).mpr rfl
    have hle := P.pA_mono c _ hkeep
    refine ⟨P.selA_input c hw, ?_⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact key_lt_lower P k hlt
    · exact key_lt_A P k hc hkeep heq

/-- **The Q24 square clauses.** Every unit square clause of `A` holds for the Q24 selection (`squareClauses_of_burning`). -/
theorem q24_squares (P : PairData A B β) (k : ℤ) (a b : ℤ) : SquareClauseSat A (q24Sel P k) a b :=
  squareClauses_of_burning (R := q24Key P k) (sel := q24Sel P k) P.binA
    (fun _ hb _ hi => black_key_lt P k hb hi) (fun _ hw => white_key P k hw) a b

/-- **Soundness of unit propagation for Q24.** Every forced literal of `A` is the Q24 selection. -/
theorem q24_forced (P : PairData A B β) (k : ℤ) {c i : Site}
    (h : ForcedEdge A (fun _ _ => False) c i) : q24Sel P k c = i :=
  forced_sound A (fun _ _ => False) (q24Sel P k) (fun _ hw => (white_key P k hw).1)
    (fun _ _ h => False.elim h) (q24_squares P k) c i h

/-- At a flat tie (both inputs at level `k`), the Q24 selection is the `B` selection. -/
theorem q24_flat (P : PairData A B β) {k : ℤ} {c : Site} (hc : Dd A B c = k)
    (hT : Dd A B (incomingNeg c) = k ∧ Dd A B (incomingPos c) = k) : q24Sel P k c = P.selB c := by
  have h1 : ¬ Dd A B (incomingNeg c) < k := by omega
  have h2 : ¬ Dd A B (incomingPos c) < k := by omega
  unfold q24Sel tieSel
  rw [if_pos hc, if_neg h1, if_neg h2, if_pos hT]

/-- **Forced literals at a flat tie are the `B` choice.** -/
theorem forced_flat_eq_selB (P : PairData A B β) {k : ℤ} {c i : Site} (hc : Dd A B c = k)
    (hT : Dd A B (incomingNeg c) = k ∧ Dd A B (incomingPos c) = k)
    (h : ForcedEdge A (fun _ _ => False) c i) : i = P.selB c := by
  rw [← q24_flat P hc hT]
  exact (q24_forced P k h).symm

/-- **Soundness for the `B`-side.** Every forced literal of `B` is the `B` selection. -/
theorem forcedB_eq_selB (P : PairData A B β) {c i : Site}
    (h : ForcedEdge B (fun _ _ => False) c i) : P.selB c = i :=
  forced_sound B (fun _ _ => False) P.selB (fun x hw => P.selB_input x hw)
    (fun _ _ h => False.elim h) P.squaresB c i h

/-- **A disagreement forces neither literal.** If the Q24 selection differs from the `A` selection at a centre, neither is forced. -/
theorem neither_forced_of_disagree (P : PairData A B β) (k : ℤ) {z : Site} (hne : q24Sel P k z ≠ P.selA z) :
    ¬ ForcedEdge A (fun _ _ => False) z (P.selA z) ∧ ¬ ForcedEdge A (fun _ _ => False) z (q24Sel P k z) := by
  constructor
  · intro h
    exact hne (q24_forced P k h)
  · intro h
    exact hne (forced_sound A (fun _ _ => False) P.selA P.selA_input (fun _ _ h => False.elim h) P.squaresA z _ h).symm

/-- Inputs of a centre: two distinct inputs carry the sum of the two inputs. -/
theorem inputs_sum (f : Site → ℤ) {z u v : Site} (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hv : v = incomingNeg z ∨ v = incomingPos z) (huv : u ≠ v) :
    f u + f v = f (incomingNeg z) + f (incomingPos z) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · rfl
  · ring
  · exact absurd rfl huv

/-- Inputs of a centre: two distinct inputs that are both tied make both inputs tied. -/
theorem inputs_both (f : Site → ℤ) (k : ℤ) {z u v : Site} (hu : u = incomingNeg z ∨ u = incomingPos z)
    (hv : v = incomingNeg z ∨ v = incomingPos z) (huv : u ≠ v) (hfu : f u = k) (hfv : f v = k) :
    f (incomingNeg z) = k ∧ f (incomingPos z) = k := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · exact ⟨hfu, hfv⟩
  · exact ⟨hfv, hfu⟩
  · exact absurd rfl huv

/-- **The rising-edge reduction (`Q24.md`, the rising paragraph).** Let `P'` be the shifted price of the `B`-side, non-increasing along the
kept `B`-inputs and with unit increments along the edges. At a kept `A`-edge `z → u` with `Φ z < Φ u`, where `Φ = D + P'`, both roots are
white, the two inputs of `z` tie at the level `D(z)`, and the `B` choice differs from the `A` choice. -/
theorem rise_reduction (P : PairData A B β) (P' : Site → ℤ)
    (hPB : ∀ c i, P.pB c i → P' i ≤ P' c) (hPu : ∀ c i, Edge i c → P' i - P' c ≤ 1)
    {z u : Site} (hC : P.pA z u) (hrise : Dd A B z + P' z < Dd A B u + P' u) :
    laplacian A z = 0 ∧ laplacian B z = 0 ∧ P.selB z ≠ P.selA z ∧
      (Dd A B (incomingNeg z) = Dd A B z ∧ Dd A B (incomingPos z) = Dd A B z) := by
  have hedge : Edge u z := P.pA_edge z u hC
  have hle : Dd A B u ≤ Dd A B z := P.pA_mono z u hC
  have hpu := hPu z u hedge
  have hD : Dd A B u = Dd A B z := by omega
  have hP : P' u = P' z + 1 := by omega
  have hgw : laplacian B z = 0 := by
    rcases P.binB z with h | h
    · exfalso
      have hOk : P.pB z u := by
        rcases hedge with h' | h'
        · rw [h']
          exact (P.pB_black z h).1
        · rw [h']
          exact (P.pB_black z h).2
      have := hPB z u hOk
      omega
    · exact h
  have hzin := P.selB_input z hgw
  have hpolB : P.pB z (P.selB z) := (P.pB_white z hgw _).mpr rfl
  have hle2 := P.pB_mono z _ hpolB
  have hvu : P.selB z ≠ u := by
    intro h
    have hOk : P.pB z u := by
      rw [← h]
      exact hpolB
    have := hPB z u hOk
    omega
  have hsum := inputs_sum (Dd A B) hedge hzin hvu.symm
  have hs := Dd_split (A := A) (B := B) z
  have hw : laplacian A z = 0 := by
    rcases P.binA z with h | h
    · exfalso
      rw [h, hgw] at hs
      omega
    · exact h
  rw [hw, hgw] at hs
  have hfv : Dd A B (P.selB z) = Dd A B z := by omega
  have hT := inputs_both (Dd A B) (Dd A B z) hedge hzin hvu.symm hD hfv
  have hCsel : P.selA z = u := ((P.pA_white z hw u).mp hC).symm
  exact ⟨hw, hgw, by rw [hCsel]; exact hvu, hT⟩

/-- **Both roots are unforced at a rising edge.** At a rising `A`-edge `z → u`, the `A`-literal and the `B`-literal at `z` are not forced
(`A` by the Q24 disagreement, `B` by the swapped Q24 policy). -/
theorem rise_both (P : PairData A B β) (P' : Site → ℤ)
    (hPB : ∀ c i, P.pB c i → P' i ≤ P' c) (hPu : ∀ c i, Edge i c → P' i - P' c ≤ 1)
    {z u : Site} (hC : P.pA z u) (hrise : Dd A B z + P' z < Dd A B u + P' u) :
    ¬ ForcedEdge A (fun _ _ => False) z (P.selA z) ∧
      ¬ ForcedEdge B (fun _ _ => False) z (P.selB z) := by
  obtain ⟨hw, hgw, hne, hT⟩ := rise_reduction P P' hPB hPu hC hrise
  constructor
  · have hq : q24Sel P (Dd A B z) z = P.selB z := q24_flat P rfl hT
    exact (neither_forced_of_disagree P (Dd A B z) (by rw [hq]; exact hne)).1
  · have hc' : Dd B A z = -Dd A B z := Dd_swap A B z
    have hT' : Dd B A (incomingNeg z) = -Dd A B z ∧ Dd B A (incomingPos z) = -Dd A B z := by
      rw [Dd_swap A B, Dd_swap A B]
      exact ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hq' := q24_flat P.swap hc' hT'
    have hne' : q24Sel P.swap (-Dd A B z) z ≠ P.swap.selA z := by
      rw [hq']
      exact hne.symm
    exact (neither_forced_of_disagree P.swap (-Dd A B z) hne').1

end FLatticePaper.Q24Policy
