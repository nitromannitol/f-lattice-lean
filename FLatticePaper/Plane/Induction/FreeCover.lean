import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.FreeRows

/-! # Row coverage up to the deck (task 113, step (d))

The V labels of the minus row (Q13) have indices `r, r−1, …, 1, 0, −1, …, r+1−L`, and those of the plus row (Q1 l.21–30) have indices
`−r−1, …, −1, 0, 1, …, L−r−2`. Each is a block of `L` consecutive integers, so each contains exactly one representative of every residue
class mod `L` (`minusVIdx_residue`, `plusVIdx_residue`). With the period law of `FreeEnum.vAt`, every free V site of the period is a deck
translate of a row entry: `minus_row_covers`. The H labels are the same with `d` in place of `L` and the H deck `U`, which has no Lean
definition yet (named). -/

namespace FLatticePaper.FreeCover

open FLatticePaper FLatticePaper.Induction FLatticePaper.FreeEnum

/-- The V indices of the minus row: `r, r−1, …, 1, 0, −1, …, r+1−L`. -/
def minusVIdx (r L : ℤ) : List ℤ :=
  ((List.range r.toNat).map fun i : ℕ => r - (i : ℤ)) ++ [0] ++
    ((List.range (L - r - 1).toNat).map fun i : ℕ => -1 - (i : ℤ))

/-- The V indices of the plus row: `−r−1, …, −1, 0, 1, …, L−r−2`. -/
def plusVIdx (r L : ℤ) : List ℤ :=
  ((List.range (r + 1).toNat).map fun i : ℕ => -r - 1 + (i : ℤ)) ++ [0] ++
    ((List.range (L - r - 2).toNat).map fun i : ℕ => 1 + (i : ℤ))

/-- The minus row's V indices are exactly the integers of `[r+1−L, r]`. -/
theorem minusVIdx_mem (r L j : ℤ) (hr : 0 ≤ r) (hrL : r < L) :
    j ∈ minusVIdx r L ↔ r + 1 - L ≤ j ∧ j ≤ r := by
  unfold minusVIdx
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | rfl) | ⟨i, hi, rfl⟩)
    · omega
    · omega
    · omega
  · intro h
    by_cases h0 : j = 0
    · exact Or.inl (Or.inr h0)
    by_cases hjpos : 1 ≤ j
    · exact Or.inl (Or.inl ⟨(r - j).toNat, by omega, by omega⟩)
    · exact Or.inr ⟨(-1 - j).toNat, by omega, by omega⟩

/-- The plus row's V indices are exactly the integers of `[−r−1, L−r−2]`. -/
theorem plusVIdx_mem (r L j : ℤ) (hr : 0 ≤ r) (hrL : r + 2 ≤ L) :
    j ∈ plusVIdx r L ↔ -r - 1 ≤ j ∧ j ≤ L - r - 2 := by
  unfold plusVIdx
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | rfl) | ⟨i, hi, rfl⟩)
    · omega
    · omega
    · omega
  · intro h
    by_cases h0 : j = 0
    · exact Or.inl (Or.inr h0)
    by_cases hjneg : j ≤ -1
    · exact Or.inl (Or.inl ⟨(j + r + 1).toNat, by omega, by omega⟩)
    · exact Or.inr ⟨(j - 1).toNat, by omega, by omega⟩

/-- **Residues, once each**: for any integer `j`, the block `[a, a + L)` contains exactly one `k` with `j ≡ k (mod L)`. -/
theorem block_residue (a L j : ℤ) (hL : 0 < L) :
    ∃ k : ℤ, a ≤ k ∧ k < a + L ∧ ∃ m : ℤ, j = k + m * L := by
  refine ⟨a + (j - a) % L, ?_, ?_, (j - a) / L, ?_⟩
  · have := Int.emod_nonneg (j - a) hL.ne'
    omega
  · have := Int.emod_lt_of_pos (j - a) hL
    omega
  · have := Int.emod_def (j - a) L
    linarith

/-- **Uniqueness in a block**: two members of a block `[a, a + L)` that are congruent mod `L` are equal. -/
theorem block_unique (a L k₁ k₂ m₁ m₂ : ℤ) (hL : 0 < L) (h₁ : a ≤ k₁ ∧ k₁ < a + L) (h₂ : a ≤ k₂ ∧ k₂ < a + L)
    (heq : k₁ + m₁ * L = k₂ + m₂ * L) : k₁ = k₂ := by
  have hd : (m₁ - m₂) * L = k₂ - k₁ := by linarith
  rcases lt_trichotomy (m₁ - m₂) 0 with h | h | h
  · have : (m₁ - m₂) * L ≤ -L := by nlinarith
    omega
  · rw [h, zero_mul] at hd
    omega
  · have : (m₁ - m₂) * L ≥ L := by nlinarith
    omega

/-- **The minus row covers every residue of the V cut once**: every `k` with `k` in the minus block is the unique representative. -/
theorem minusVIdx_residue (r L j : ℤ) (hr : 0 ≤ r) (hrL : r < L) :
    ∃ k : ℤ, k ∈ minusVIdx r L ∧ ∃ m : ℤ, j = k + m * L := by
  obtain ⟨k, hk1, hk2, m, hm⟩ := block_residue (r + 1 - L) L j (by omega)
  exact ⟨k, (minusVIdx_mem r L k hr hrL).2 ⟨by omega, by omega⟩, m, hm⟩

/-- **The period law by multiples**: `V_{j + mL} = V_j + m V`. -/
theorem vAt_add_mul_period (frame : ChildFrame) (base : ℤ → Site) (j m : ℤ) :
    vAt frame base (j + m * period frame) =
      ((vAt frame base j).1 + m * (Vdeck frame).1, (vAt frame base j).2 + m * (Vdeck frame).2) := by
  have hL : period frame ≠ 0 := (period_pos frame).ne'
  have h1 : (j + m * period frame) % period frame = j % period frame := by simp
  have h2 : (j + m * period frame) / period frame = j / period frame + m := Int.add_mul_ediv_right j m hL
  unfold vAt
  rw [h1, h2]
  ext
  · simp only
    ring
  · simp only
    ring

/-- **Minus-row coverage up to the deck.** A free V site of the period (`z ∈ freeV` with ordinate in `[0, L)`) is a deck translate of a
minus-row entry: `vAt base k = z + m V` for some `k` of the minus row and some `m`. -/
theorem minus_row_covers (frame : ChildFrame) (hcut : CutOnePerOrdinate frame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r) ∈ frame.freeV ∧ (base r).2 = r)
    {z : Site} (hz : z ∈ frame.freeV) (hord : 0 ≤ z.2 ∧ z.2 < period frame)
    (r : ℤ) (hr : 0 ≤ r) (hrL : r < period frame) :
    ∃ k : ℤ, k ∈ minusVIdx r (period frame) ∧ ∃ m : ℤ,
      vAt frame base k = (z.1 + (-m) * (Vdeck frame).1, z.2 + (-m) * (Vdeck frame).2) := by
  obtain ⟨k, hk, m, hm⟩ := minusVIdx_residue r (period frame) z.2 hr hrL
  refine ⟨k, hk, m, ?_⟩
  have hz' : z = base z.2 := freeV_eq_base frame hcut base hbase hz hord
  have hk' : k = z.2 + (-m) * period frame := by linarith
  have hvk : vAt frame base k = vAt frame base (z.2 + (-m) * period frame) := by rw [hk']
  rw [hvk, vAt_add_mul_period, vAt_eq_base frame base z.2 hord]
  rw [← hz']

end FLatticePaper.FreeCover
