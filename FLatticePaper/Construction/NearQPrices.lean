/-! Nominal sections 2 and 3 of `ALL_PROPER_UNC_STANDARD_NOMINAL_PRICES.md`, the integer arithmetic of the near-q prices.

The archive writes each near-q price as a sum `H + 2k - l` (section 2) or `Ĥ + 2k + l` (section 3), with `l ∈ {0,1}` and
`k` the number of the dispatched source. The three inputs are the bounds that the archive proves (or cites) on the
gap function `H` and `Ĥ` over the whole of `E_Z`:

* saved3, section 2: `H ≥ 0` on `E_Z` (the whole-E_Z three-case theorem), with `k ≥ 1` for a dispatched saved3 odd;
* saved1, section 2: `H ≥ 1` on `E_Z` (the intrinsic-chain maximum), with `k ≥ 0`;
* saved3, section 3: `Ĥ ≥ -1` on `E_Z`, with `k ≥ 1`;
* saved1, section 3: `Ĥ ≥ 0` on `E_Z` (from `max_E Φ⁺ ≤ c0 + 2` and the birth identity `Ψ = c0 + 2 - Φ⁺`), with `k ≥ 0`.

The lemmas below state only this arithmetic. The bounds on `H` and `Ĥ` are hypotheses here; they are not proved in Lean. -/

namespace FLatticePaper.Construction.NearQPrices

/-- Section 2, saved3: the normalized competing gap `H + 2k - l` is nonnegative. -/
theorem w0_gap_saved3 {H k l : Int} (hl : l = 0 ∨ l = 1) (hH : 0 ≤ H) (hk : 1 ≤ k) :
    0 ≤ H + 2 * k - l := by
  rcases hl with rfl | rfl <;> omega

/-- Section 2, saved1: the normalized competing gap `H + 2k - l` is nonnegative, even for `k = 0`. -/
theorem w0_gap_saved1 {H k l : Int} (hl : l = 0 ∨ l = 1) (hH : 1 ≤ H) (hk : 0 ≤ k) :
    0 ≤ H + 2 * k - l := by
  rcases hl with rfl | rfl <;> omega

/-- Section 3, saved3: the W1 price `Ĥ + 2k + l` is at least one. -/
theorem w1_price_saved3 {H k l : Int} (hl : l = 0 ∨ l = 1) (hH : -1 ≤ H) (hk : 1 ≤ k) :
    1 ≤ H + 2 * k + l := by
  rcases hl with rfl | rfl <;> omega

/-- Section 3, saved1: the W1 price `Ĥ + 2k + l` is nonnegative. -/
theorem w1_price_saved1 {H k l : Int} (hl : l = 0 ∨ l = 1) (hH : 0 ≤ H) (hk : 0 ≤ k) :
    0 ≤ H + 2 * k + l := by
  rcases hl with rfl | rfl <;> omega

end FLatticePaper.Construction.NearQPrices
