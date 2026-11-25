import FLatticePaper.Tiles.CellTestGen

/-! Task Q25 (completeness of the seam), the interval property of the cell tile (`fixes/Q25.md`, "The cell boundary").

The cells passing the test (1) of `CellTestGen` form an interval in each column and in each row. The four one-sided tests are
monotone along the line: in a column the upper grade test and the lower slope test hold upward, the lower grade test and the upper
slope test hold downward (`t` decreases, `s` increases); in a row the signs of the monotonicity swap. The parity-dependent constants
`pk K0 K1 (x + y)` change by at most the step `N` (for `t`) or `D − N`, `D + N` (for `s`), which is what `pk_le` gives. -/

namespace FLatticePaper.Tiles.CellIntervals

/-- The constant of the cell at parity `s` (even `s` uses `K0`, odd `s` uses `K1`). -/
def pk (K0 K1 s : ℤ) : ℤ := if s % 2 = 0 then K0 else K1

/-- Two parity constants differing by at most `step` differ by at most `step` at any two parities. -/
theorem pk_le (K0 K1 step s s' : ℤ) (hA : K1 ≤ K0 + step) (hB : K0 ≤ K1 + step) :
    pk K0 K1 s ≤ pk K0 K1 s' + step := by
  unfold pk
  split_ifs <;> omega

/-- The interval property along a column: for `y1 ≤ y2 ≤ y3`, the cell `(x, y2)` passes the test when `(x, y1)` and `(x, y3)` do. -/
theorem col_interval (K0 K1 L0 L1 N D T top x y1 y2 y3 : ℤ) (hD : 0 < D) (_hN : 0 < N) (hND : N < D)
    (hK0 : K1 ≤ K0 + D) (hK1 : K0 ≤ K1 + D) (hL0 : L1 ≤ L0 + (D - N)) (hL1 : L0 ≤ L1 + (D - N))
    (h12 : y1 ≤ y2) (h23 : y2 ≤ y3)
    (H1 : 2 * D - T - pk K0 K1 (x + y1) ≤ N * x - D * y1 ∧ N * x - D * y1 ≤ pk K0 K1 (x + y1) ∧
      pk L0 L1 (x + y1) ≤ (D + N) * x + (D - N) * y1 ∧ (D + N) * x + (D - N) * y1 ≤ top - pk L0 L1 (x + y1))
    (H3 : 2 * D - T - pk K0 K1 (x + y3) ≤ N * x - D * y3 ∧ N * x - D * y3 ≤ pk K0 K1 (x + y3) ∧
      pk L0 L1 (x + y3) ≤ (D + N) * x + (D - N) * y3 ∧ (D + N) * x + (D - N) * y3 ≤ top - pk L0 L1 (x + y3)) :
    2 * D - T - pk K0 K1 (x + y2) ≤ N * x - D * y2 ∧ N * x - D * y2 ≤ pk K0 K1 (x + y2) ∧
      pk L0 L1 (x + y2) ≤ (D + N) * x + (D - N) * y2 ∧
        (D + N) * x + (D - N) * y2 ≤ top - pk L0 L1 (x + y2) := by
  obtain ⟨a1, b1, c1, d1⟩ := H1
  obtain ⟨a3, b3, c3, d3⟩ := H3
  rcases eq_or_lt_of_le h23 with e23 | l23
  · subst e23
    exact ⟨a3, b3, c3, d3⟩
  rcases eq_or_lt_of_le h12 with e12 | l12
  · subst e12
    exact ⟨a1, b1, c1, d1⟩
  have p12 := pk_le K0 K1 D (x + y1) (x + y2) hK0 hK1
  have p32 := pk_le K0 K1 D (x + y3) (x + y2) hK0 hK1
  have q21 := pk_le L0 L1 (D - N) (x + y2) (x + y1) hL0 hL1
  have q23 := pk_le L0 L1 (D - N) (x + y2) (x + y3) hL0 hL1
  have A : D * y1 + D ≤ D * y2 := by nlinarith
  have B : D * y2 + D ≤ D * y3 := by nlinarith
  have A' : (D - N) * y1 + (D - N) ≤ (D - N) * y2 := by nlinarith
  have B' : (D - N) * y2 + (D - N) ≤ (D - N) * y3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- The interval property along a row: for `x1 ≤ x2 ≤ x3`, the cell `(x2, y)` passes the test when `(x1, y)` and `(x3, y)` do. -/
theorem row_interval (K0 K1 L0 L1 N D T top x1 x2 x3 y : ℤ) (hD : 0 < D) (hN : 0 < N) (_hND : N < D)
    (hK0 : K1 ≤ K0 + N) (hK1 : K0 ≤ K1 + N) (hL0 : L1 ≤ L0 + (D + N)) (hL1 : L0 ≤ L1 + (D + N))
    (h12 : x1 ≤ x2) (h23 : x2 ≤ x3)
    (H1 : 2 * D - T - pk K0 K1 (x1 + y) ≤ N * x1 - D * y ∧ N * x1 - D * y ≤ pk K0 K1 (x1 + y) ∧
      pk L0 L1 (x1 + y) ≤ (D + N) * x1 + (D - N) * y ∧ (D + N) * x1 + (D - N) * y ≤ top - pk L0 L1 (x1 + y))
    (H3 : 2 * D - T - pk K0 K1 (x3 + y) ≤ N * x3 - D * y ∧ N * x3 - D * y ≤ pk K0 K1 (x3 + y) ∧
      pk L0 L1 (x3 + y) ≤ (D + N) * x3 + (D - N) * y ∧ (D + N) * x3 + (D - N) * y ≤ top - pk L0 L1 (x3 + y)) :
    2 * D - T - pk K0 K1 (x2 + y) ≤ N * x2 - D * y ∧ N * x2 - D * y ≤ pk K0 K1 (x2 + y) ∧
      pk L0 L1 (x2 + y) ≤ (D + N) * x2 + (D - N) * y ∧
        (D + N) * x2 + (D - N) * y ≤ top - pk L0 L1 (x2 + y) := by
  obtain ⟨a1, b1, c1, d1⟩ := H1
  obtain ⟨a3, b3, c3, d3⟩ := H3
  rcases eq_or_lt_of_le h23 with e23 | l23
  · subst e23
    exact ⟨a3, b3, c3, d3⟩
  rcases eq_or_lt_of_le h12 with e12 | l12
  · subst e12
    exact ⟨a1, b1, c1, d1⟩
  have p13 := pk_le K0 K1 N (x1 + y) (x2 + y) hK0 hK1
  have p32 := pk_le K0 K1 N (x3 + y) (x2 + y) hK0 hK1
  have q21 := pk_le L0 L1 (D + N) (x2 + y) (x1 + y) hL0 hL1
  have q23 := pk_le L0 L1 (D + N) (x2 + y) (x3 + y) hL0 hL1
  have A : N * x1 + N ≤ N * x2 := by nlinarith
  have B : N * x2 + N ≤ N * x3 := by nlinarith
  have A' : (D + N) * x1 + (D + N) ≤ (D + N) * x2 := by nlinarith
  have B' : (D + N) * x2 + (D + N) ≤ (D + N) * x3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

end FLatticePaper.Tiles.CellIntervals
