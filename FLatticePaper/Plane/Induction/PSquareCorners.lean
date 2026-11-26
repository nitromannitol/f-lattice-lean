import FLatticePaper.Plane.Induction.PrivateSquare
import FLatticePaper.Plane.Induction.CollarSquare

/-! # The parent square from its corners (generic)

A unit square `S = squareCorners a b` with a root `z ∈ S` carries a `PSquare` (three corners `q0, q1, q2` retained around the cycle back to
`z`, and the root keeps only its outward input `o`) as soon as every corner `y ≠ z` of `S` retains its in-square successor `nxtS a b y`
and, if it is white, retains nothing else. The successors form a 4-cycle on the corners (`PrivateSquare`), so the three non-root corners
are `nxtS z`, `nxtS (nxtS z)`, `nxtS (nxtS (nxtS z))`. -/

namespace FLatticePaper.PSquareCorners

open FLatticePaper FLatticePaper.PrivateSquare FLatticePaper.AndOrRank FLatticePaper.CollarSquare

/-- The explicit 4-cycle of the in-square successors. -/
theorem nxt_cycle {a b : ℤ} {z : Site} (hz : z ∈ squareCorners a b) :
    nxtS a b (nxtS a b (nxtS a b (nxtS a b z))) = z ∧
    nxtS a b z ≠ z ∧ nxtS a b (nxtS a b z) ≠ z ∧ nxtS a b (nxtS a b (nxtS a b z)) ≠ z ∧
    nxtS a b z ≠ nxtS a b (nxtS a b z) ∧ nxtS a b (nxtS a b z) ≠ nxtS a b (nxtS a b (nxtS a b z)) ∧
    nxtS a b z ≠ nxtS a b (nxtS a b (nxtS a b z)) := by
  obtain ⟨z1, z2⟩ := z
  rw [mem_square_coords] at hz
  obtain ⟨hz1, hz2⟩ := hz
  dsimp only at hz1 hz2
  by_cases hp : (a + b) % 2 = 0
  · obtain ⟨t1, t2, t3, t4⟩ := nxt_table_even hp
    rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl <;>
      simp only [t1, t2, t3, t4, Prod.mk.injEq, ne_eq, and_true, true_and] <;> omega
  · obtain ⟨t1, t2, t3, t4⟩ := nxt_table_odd (show (a + b) % 2 = 1 by omega)
    rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl <;>
      simp only [t1, t2, t3, t4, Prod.mk.injEq, ne_eq, and_true, true_and] <;> omega

/-- **The parent square from its corners.** With the root `z` in the square, its outward input `o` the only retained edge of `z`,
and every other corner retaining its in-square successor (and nothing else if white), there is a `PSquare` on the square. -/
theorem pSquare_of_corners {G : Field} {R : Site → Site → Prop} {a b : ℤ} {z o : Site}
    (hz : z ∈ squareCorners a b)
    (ho : o = incomingNeg z ∨ o = incomingPos z) (hout : o ∉ squareCorners a b)
    (hRo : R z o) (huniq : ∀ j, R z j → j = o)
    (hcorner : ∀ y ∈ squareCorners a b, y ≠ z →
      R y (nxtS a b y) ∧
        (laplacian G y = -1 ∨ (laplacian G y = 0 ∧ ∀ j, R y j → j = nxtS a b y))) :
    ∃ q0 q1 q2 : Site, PSquare G R z q0 q1 q2 o a b := by
  obtain ⟨hc4, hq0z, hq1z, hq2z, hq01, hq12, hq02⟩ := nxt_cycle hz
  have hq0S := nxtS_mem hz
  have hq1S := nxtS_mem hq0S
  have hq2S := nxtS_mem hq1S
  refine ⟨nxtS a b z, nxtS a b (nxtS a b z), nxtS a b (nxtS a b (nxtS a b z)), ?_⟩
  refine ⟨hz, hq0S, hq1S, hq2S, ?_, hq01, hq12, hq02, nxtS_isInput hz, ?_,
    nxtS_isInput hq0S, nxtS_isInput hq1S, ?_, ?_, ?_, ?_, ho, hout, hRo, huniq, ?_, ?_, ?_⟩
  · intro c' hc' hne
    rcases cover_of_square hz hc' with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro h
    have hj := huniq _ h
    exact hout (by rw [← hj]; exact hq0S)
  · have h := nxtS_isInput hq2S
    rw [hc4] at h
    exact h
  · exact (hcorner _ hq0S hq0z).1
  · exact (hcorner _ hq1S hq1z).1
  · have h := (hcorner _ hq2S hq2z).1
    rw [hc4] at h
    exact h
  · have h := (hcorner _ hq0S hq0z).2
    exact h
  · exact (hcorner _ hq1S hq1z).2
  · have h := (hcorner _ hq2S hq2z).2
    rw [hc4] at h
    exact h

end FLatticePaper.PSquareCorners
