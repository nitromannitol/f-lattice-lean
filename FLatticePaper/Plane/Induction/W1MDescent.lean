import FLatticePaper.Plane.Induction.W1FreeDescent

/-! # Task 85: the M-level descent (the common arrow by forcing, Q15 §5)

The earlier minimum `M` is the field of the unseeded unit clauses. Let `T` be the tie predicate (the two sheets agree at the site), `Rel`
the retained relation of the A policy, and `rankA` its strictly decreasing rank. For a tie `c` with `M` white, the private square gives a unit
square `Q ∋ c` whose other corners are `p0 → p1 → p2 → c` (each step a retained edge to an input), with `p0` the REJECTED input of `c`
(not retained by `c`).

Claim (`mforced_of_descent`): every M-white tie `c` has an input `o`, retained by `c`, with `ForcedEdge M c o`. Proof by strong induction
downward on the rank, the rank being bounded above on the tie band. The unit rule applies to `Q`: a black corner needs no premise; a white
corner `c'` (a tie, by `hcl`, of greater rank) is forced to its chain step `y` by the induction hypothesis, because its own kept input `o'`
equals `y`: both are inputs of `c'` and retained, and the rejected input of `c'` is not retained, so `o' = y`.

The square data for every M-white tie (`hsq`), the A quota at M-white ties (`hquot`), the closure of the tie band under the chain (`hcl`), and
the rank bound (`hB`) are the named inputs. -/

namespace FLatticePaper.W1MDescent

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1FreeDescent

/-- The two inputs of a site are distinct. -/
theorem incomingNeg_ne_incomingPos (x : Site) : incomingNeg x ≠ incomingPos x := by
  obtain ⟨x1, x2⟩ := x
  unfold incomingNeg incomingPos EvenSite
  split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega

/-- Two inputs `o`, `y` of `x`, both different from the input `q`, coincide. -/
theorem input_unique_of_ne {x o y q : Site} (ho : o = incomingNeg x ∨ o = incomingPos x)
    (hy : y = incomingNeg x ∨ y = incomingPos x) (hq : q = incomingNeg x ∨ q = incomingPos x)
    (hoq : o ≠ q) (hyq : y ≠ q) : o = y := by
  have hne := incomingNeg_ne_incomingPos x
  rcases ho with ho | ho <;> rcases hy with hy | hy <;> rcases hq with hq | hq <;>
    simp_all

/-- **The M-level descent** (task 85): every M-white tie `c` is M-forced to an input retained by `c`. -/
theorem mforced_of_descent (M : Field) (T : Site → Prop) (Rel : Site → Site → Prop) (rankA : Site → ℤ) (B : ℤ)
    (hbinM : ∀ x, laplacian M x = -1 ∨ laplacian M x = 0)
    (hrank : ∀ x y, Rel x y → rankA y < rankA x)
    (hB : ∀ c, T c → rankA c ≤ B)
    (hquot : ∀ c, T c → laplacian M c = 0 → ∃ i : Site, (i = incomingNeg c ∨ i = incomingPos c) ∧ Rel c i)
    (hsq : ∀ c, T c → laplacian M c = 0 → ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧ ¬ Rel c p0 ∧
      Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧ Rel p0 p1 ∧ Rel p1 p2 ∧ Rel p2 c)
    (hcl : ∀ c p0 p1 p2 : Site, T c → laplacian M c = 0 → (p0 = incomingNeg c ∨ p0 = incomingPos c) →
      Rel p0 p1 → Rel p1 p2 → Rel p2 c → T p0 ∧ T p1 ∧ T p2) :
    ∀ c, T c → laplacian M c = 0 →
      ∃ o : Site, (o = incomingNeg c ∨ o = incomingPos c) ∧ Rel c o ∧ ForcedEdge M (fun _ _ => False) c o := by
  have key : ∀ n : ℕ, ∀ c, T c → laplacian M c = 0 → B - rankA c < n →
      ∃ o : Site, (o = incomingNeg c ∨ o = incomingPos c) ∧ Rel c o ∧ ForcedEdge M (fun _ _ => False) c o := by
    intro n
    induction n with
    | zero =>
      intro c hT _ hlt
      have := hB c hT
      push_cast at hlt
      omega
    | succ n ih =>
      intro c hT hw hlt
      obtain ⟨p0, p1, p2, a, b, hcc, hp0c, hp1c, hp2c, hcov, hne01, hne12, hne02, hp0in, hrej,
        hE1, hE2, hE3, hR0, hR1, hR2⟩ := hsq c hT hw
      push_cast at hlt
      have hr2 : rankA c < rankA p2 := hrank p2 c hR2
      have hr1 : rankA p2 < rankA p1 := hrank p1 p2 hR1
      have hr0 : rankA p1 < rankA p0 := hrank p0 p1 hR0
      obtain ⟨hT0, hT1, hT2⟩ := hcl c p0 p1 p2 hT hw hp0in hR0 hR1 hR2
      -- a white corner is forced to its chain step: its kept input equals the chain step
      have C : ∀ x y : Site, T x → laplacian M x = 0 → Rel x y → (y = incomingNeg x ∨ y = incomingPos x) →
          B - rankA x < (n : ℤ) → ForcedEdge M (fun _ _ => False) x y := by
        intro x y hTx hwx hRxy hyin hxlt
        obtain ⟨o', ho'in, hRo', hF⟩ := ih x hTx hwx hxlt
        obtain ⟨q0, q1, q2, a', b', _, _, _, _, _, _, _, _, hq0in, hqrej, _, _, _, _, _, _⟩ :=
          hsq x hTx hwx
        have hyo : o' = y := input_unique_of_ne ho'in hyin hq0in
          (fun e => hqrej (e ▸ hRo')) (fun e => hqrej (e ▸ hRxy))
        rw [hyo] at hF
        exact hF
      -- the outside input of c: an input other than p0, outside the square
      have hoex : ∃ o : Site, (o = incomingNeg c ∨ o = incomingPos c) ∧ o ≠ p0 ∧ o ∉ squareCorners a b := by
        have hout0 := other_input_outside hcc hp0c hp0in
        by_cases hp : p0 = incomingNeg c
        · rw [if_pos hp] at hout0
          exact ⟨incomingPos c, Or.inr rfl, fun e => incomingNeg_ne_incomingPos c (hp.symm.trans e.symm), hout0⟩
        · rw [if_neg hp] at hout0
          exact ⟨incomingNeg c, Or.inl rfl, fun e => hp e.symm, hout0⟩
      obtain ⟨o, ho, hop0, hout⟩ := hoex
      refine ⟨o, ho, ?_, ?_⟩
      · obtain ⟨i, hi, hRi⟩ := hquot c hT hw
        have hip : i ≠ p0 := fun e => hrej (e ▸ hRi)
        have : i = o := input_unique_of_ne hi ho hp0in hip hop0
        exact this ▸ hRi
      · refine ForcedEdge.unit (fun c' => if c' = p0 then p1 else if c' = p1 then p2 else c) hcc hw ho hout ?_ ?_
        · intro c' hc' hne
          rcases hcov c' hc' hne with h | h | h
          · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = p1 := if_pos h
            rw [hi]
            rcases hbinM c' with hb | hb
            · exact Or.inl hb
            · refine Or.inr ⟨hb, ?_, ?_⟩
              · exact hp1c
              · rw [h]
                exact hE1
          · have hne' : c' ≠ p0 := by
              rw [h]
              exact fun e => hne01 e.symm
            have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = p2 := by
              rw [if_neg hne', if_pos h]
            rw [hi]
            rcases hbinM c' with hb | hb
            · exact Or.inl hb
            · refine Or.inr ⟨hb, ?_, ?_⟩
              · exact hp2c
              · rw [h]
                exact hE2
          · have hne' : c' ≠ p0 := by
              rw [h]
              exact fun e => hne02 e.symm
            have hne'' : c' ≠ p1 := by
              rw [h]
              exact fun e => hne12 e.symm
            have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = c := by
              rw [if_neg hne', if_neg hne'']
            rw [hi]
            rcases hbinM c' with hb | hb
            · exact Or.inl hb
            · refine Or.inr ⟨hb, ?_, ?_⟩
              · exact hcc
              · rw [h]
                exact hE3
        · intro c' hc' hne hwc'
          rcases hcov c' hc' hne with h | h | h
          · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = p1 := if_pos h
            rw [hi]
            rw [h] at hwc' ⊢
            exact C p0 p1 hT0 hwc' hR0 hE1 (by omega)
          · have hne' : c' ≠ p0 := by
              rw [h]
              exact fun e => hne01 e.symm
            have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = p2 := by
              rw [if_neg hne', if_pos h]
            rw [hi]
            rw [h] at hwc' ⊢
            exact C p1 p2 hT1 hwc' hR1 hE2 (by omega)
          · have hne' : c' ≠ p0 := by
              rw [h]
              exact fun e => hne02 e.symm
            have hne'' : c' ≠ p1 := by
              rw [h]
              exact fun e => hne12 e.symm
            have hi : (if c' = p0 then p1 else if c' = p1 then p2 else c) = c := by
              rw [if_neg hne', if_neg hne'']
            rw [hi]
            rw [h] at hwc' ⊢
            exact C p2 c hT2 hwc' hR2 hE3 (by omega)
  intro c hT hw
  have hb := hB c hT
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B - rankA c < n := ⟨(B - rankA c).toNat + 1, by omega⟩
  exact key n c hT hw hn

end FLatticePaper.W1MDescent
