import FLatticePaper.Construction.BaseRegisters
import FLatticePaper.Construction.RegisterFamily

/-! # The family of the pure-run base registers, for every run length (task 38, item 1)

A base register is the tile of a base mask `BaseMask.tile kind den` (trimmed). Its donor form is the centred tile, whose sites
are the raw sites shifted by the raw lower-left cell (`mem_llCenter_trim`). For each mask the lower-left cell is an explicit
cell `p`, and membership of the family vectors of the pure-run children is an explicit inequality in the mask parameter.
This file proves those characterisations for the masks used by the pure runs, parametric in the parameter.

Family values (the vector of the child, `2 K_f` for an odd child, `K_f` for an even child, `K_f = (den, num)`):
* `stairOdd M` (odd `M`): `(M+1, M-1)`; `ladderEven M` (even `M`): `(M+1, M-1)`;
* `stairEven M` (odd `M`): `(M, 1)`; `ladderOdd M` (even `M`): `(2M, 2)`;
* the alternate masks carry `K_f`: `stairOddAlt`, `ladderEvenAlt`, `ladderOddAlt`, `stairEvenAlt` (below). -/

namespace FLatticePaper.Construction

open HeightTile

/-- The donor form of a mask tile, once its raw lower-left cell is known. -/
theorem mem_tile_llCenter_of_lowerLeft (raw : HeightTile Site) (hne : raw.sites.Nonempty) (p : Site)
    (hl : raw.lowerLeft hne = p) (v : Site) :
    v ∈ ((raw.trim hne).llCenter (raw.trim_sites_nonempty hne)).sites ↔ v + p ∈ raw.sites := by
  rw [mem_llCenter_trim, hl]

/-- The lower-left cell of a raw mask is `p` when `p` is a site and every site is at or after it. -/
theorem lowerLeft_of_minimal (raw : HeightTile Site) (hne : raw.sites.Nonempty) (p : Site) (hp : p ∈ raw.sites)
    (hmin : ∀ q ∈ raw.sites, p.2 ≤ q.2 ∧ (p.2 = q.2 → p.1 ≤ q.1)) :
    raw.lowerLeft hne = p :=
  HeightTile.lowerLeft_eq_of_minimal raw hne hp hmin

/-- The centred donor of a mask tile contains `v` exactly when the raw mask contains `v + p`, for the lower-left cell `p`. -/
theorem tile_llCenter_iff (kind : BaseMask) (M : ℤ) (hM : BaseMask.Valid kind M) (p : Site)
    (hl : ∀ hne : (kind.raw M).sites.Nonempty, (kind.raw M).lowerLeft hne = p) (v : Site) :
    v ∈ ((kind.tile M hM).llCenter (kind.tile_nonempty M hM)).sites ↔ v + p ∈ (kind.raw M).sites := by
  unfold BaseMask.tile
  exact mem_tile_llCenter_of_lowerLeft _ _ p (hl _) v

/-! ### stairOdd (`(M+1, M-1)`, lower-left `(0,1)`) -/

theorem stairOdd_lowerLeft (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) (hne : (BaseMask.stairOdd.raw M).sites.Nonempty) :
    (BaseMask.stairOdd.raw M).lowerLeft hne = (0, 1) := by
  apply lowerLeft_of_minimal _ hne (0, 1)
  · rw [BaseMask.mem_stairOdd_raw_direct]
    omega
  · intro q hq
    rw [BaseMask.mem_stairOdd_raw_direct] at hq
    omega

theorem stairOdd_family (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) :
    ((M + 1, M - 1) : Site) ∈ ((BaseMask.stairOdd.tile M hM).llCenter (BaseMask.stairOdd.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.stairOdd.tile M hM).llCenter (BaseMask.stairOdd.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.stairOdd.tile M hM).llCenter (BaseMask.stairOdd.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.stairOdd M hM (0, 1) (fun hne => stairOdd_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairOdd M hM (0, 1) (fun hne => stairOdd_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairOdd M hM (0, 1) (fun hne => stairOdd_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [BaseMask.mem_stairOdd_raw_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### ladderEven (`(M+1, M-1)`, lower-left `(0,1)`) -/

theorem ladderEven_lowerLeft (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) (hne : (BaseMask.ladderEven.raw M).sites.Nonempty) :
    (BaseMask.ladderEven.raw M).lowerLeft hne = (0, 1) := by
  apply lowerLeft_of_minimal _ hne (0, 1)
  · rw [BaseMask.mem_ladderEven_raw_direct]
    omega
  · intro q hq
    rw [BaseMask.mem_ladderEven_raw_direct] at hq
    omega

theorem ladderEven_family (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((M + 1, M - 1) : Site) ∈ ((BaseMask.ladderEven.tile M hM).llCenter (BaseMask.ladderEven.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.ladderEven.tile M hM).llCenter (BaseMask.ladderEven.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.ladderEven.tile M hM).llCenter (BaseMask.ladderEven.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.ladderEven M hM (0, 1) (fun hne => ladderEven_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderEven M hM (0, 1) (fun hne => ladderEven_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderEven M hM (0, 1) (fun hne => ladderEven_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [BaseMask.mem_ladderEven_raw_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### stairOddAlt (`(k+1, k)` for `M = 2k+1`, lower-left `(0,1)`) -/

theorem stairOddAlt_lowerLeft (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) (hne : (BaseMask.stairOddAlt.raw M).sites.Nonempty) :
    (BaseMask.stairOddAlt.raw M).lowerLeft hne = (0, 1) := by
  apply lowerLeft_of_minimal _ hne (0, 1)
  · rw [BaseMask.mem_stairOddAlt_raw_direct]
    omega
  · intro q hq
    rw [BaseMask.mem_stairOddAlt_raw_direct] at hq
    omega

theorem stairOddAlt_family (k : ℤ) (hk : 1 ≤ k) :
    ((k + 1, k) : Site) ∈ ((BaseMask.stairOddAlt.tile (2 * k + 1) ⟨by omega, by omega⟩).llCenter
        (BaseMask.stairOddAlt.tile_nonempty _ _)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.stairOddAlt.tile (2 * k + 1) ⟨by omega, by omega⟩).llCenter
        (BaseMask.stairOddAlt.tile_nonempty _ _)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.stairOddAlt.tile (2 * k + 1) ⟨by omega, by omega⟩).llCenter
        (BaseMask.stairOddAlt.tile_nonempty _ _)).sites := by
  have hM : 3 ≤ 2 * k + 1 ∧ (2 * k + 1) % 2 = 1 := ⟨by omega, by omega⟩
  rw [tile_llCenter_iff BaseMask.stairOddAlt _ hM (0, 1) (fun hne => stairOddAlt_lowerLeft _ hM hne)]
  rw [tile_llCenter_iff BaseMask.stairOddAlt _ hM (0, 1) (fun hne => stairOddAlt_lowerLeft _ hM hne)]
  rw [tile_llCenter_iff BaseMask.stairOddAlt _ hM (0, 1) (fun hne => stairOddAlt_lowerLeft _ hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [BaseMask.mem_stairOddAlt_raw_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### ladderEvenAlt (`(M+1, M-1)`, lower-left `(0,1)`) -/

theorem ladderEvenAlt_lowerLeft (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) (hne : (BaseMask.ladderEvenAlt.raw M).sites.Nonempty) :
    (BaseMask.ladderEvenAlt.raw M).lowerLeft hne = (0, 1) := by
  apply lowerLeft_of_minimal _ hne (0, 1)
  · rw [BaseMask.mem_ladderEvenAlt_raw_direct]
    omega
  · intro q hq
    rw [BaseMask.mem_ladderEvenAlt_raw_direct] at hq
    omega

theorem ladderEvenAlt_family (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((M + 1, M - 1) : Site) ∈ ((BaseMask.ladderEvenAlt.tile M hM).llCenter (BaseMask.ladderEvenAlt.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.ladderEvenAlt.tile M hM).llCenter (BaseMask.ladderEvenAlt.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.ladderEvenAlt.tile M hM).llCenter (BaseMask.ladderEvenAlt.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.ladderEvenAlt M hM (0, 1) (fun hne => ladderEvenAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderEvenAlt M hM (0, 1) (fun hne => ladderEvenAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderEvenAlt M hM (0, 1) (fun hne => ladderEvenAlt_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [BaseMask.mem_ladderEvenAlt_raw_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### stairEven (`(M, 1)`, lower-left `(0,0)`), ladderOdd (`(2M, 2)`, lower-left `(0,0)`) -/

theorem mem_stairEven_direct (M : ℤ) (pt : Site) :
    pt ∈ (BaseMask.stairEven.raw M).sites ↔
      (2 - M ≤ pt.1 ∧ pt.1 ≤ M) ∧ (0 ≤ pt.2 ∧ pt.2 ≤ M + 1) ∧
        (((pt.1 = 0 ∧ pt.2 = 0) ∨ (pt.1 = 2 ∧ pt.2 = M + 1)) ∨ (1 ≤ pt.1 + pt.2 ∧ pt.1 + pt.2 ≤ M + 2)) := by
  rw [BaseMask.mem_stairEven_raw_iff]
  simp only [BaseMask.StairEvenCorner]

theorem stairEven_lowerLeft (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) (hne : (BaseMask.stairEven.raw M).sites.Nonempty) :
    (BaseMask.stairEven.raw M).lowerLeft hne = (0, 0) := by
  apply lowerLeft_of_minimal _ hne (0, 0)
  · rw [mem_stairEven_direct]
    omega
  · intro q hq
    rw [mem_stairEven_direct] at hq
    omega

theorem stairEven_family (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) :
    ((M, 1) : Site) ∈ ((BaseMask.stairEven.tile M hM).llCenter (BaseMask.stairEven.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.stairEven.tile M hM).llCenter (BaseMask.stairEven.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.stairEven.tile M hM).llCenter (BaseMask.stairEven.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.stairEven M hM (0, 0) (fun hne => stairEven_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairEven M hM (0, 0) (fun hne => stairEven_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairEven M hM (0, 0) (fun hne => stairEven_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_stairEven_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem mem_ladderOdd_direct (M : ℤ) (pt : Site) :
    pt ∈ (BaseMask.ladderOdd.raw M).sites ↔
      (2 - M ≤ pt.1 ∧ pt.1 ≤ 2 * M) ∧ (0 ≤ pt.2 ∧ pt.2 ≤ M + 2) ∧
        (((pt.1 = 0 ∧ pt.2 = 0) ∨ (pt.1 = M + 2 ∧ pt.2 = M + 2)) ∨
          (1 ≤ pt.1 + pt.2 ∧ pt.1 + pt.2 ≤ 2 * M + 3 ∧
            ¬ ((pt.2 = 0 ∧ M ≤ pt.1) ∨ (pt.2 = M + 2 ∧ pt.1 ≤ 2)))) := by
  rw [BaseMask.mem_ladderOdd_raw_iff]

theorem ladderOdd_lowerLeft (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) (hne : (BaseMask.ladderOdd.raw M).sites.Nonempty) :
    (BaseMask.ladderOdd.raw M).lowerLeft hne = (0, 0) := by
  apply lowerLeft_of_minimal _ hne (0, 0)
  · rw [mem_ladderOdd_direct]
    omega
  · intro q hq
    rw [mem_ladderOdd_direct] at hq
    omega

theorem ladderOdd_family (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((2 * M, 2) : Site) ∈ ((BaseMask.ladderOdd.tile M hM).llCenter (BaseMask.ladderOdd.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.ladderOdd.tile M hM).llCenter (BaseMask.ladderOdd.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.ladderOdd.tile M hM).llCenter (BaseMask.ladderOdd.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.ladderOdd M hM (0, 0) (fun hne => ladderOdd_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderOdd M hM (0, 0) (fun hne => ladderOdd_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderOdd M hM (0, 0) (fun hne => ladderOdd_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_ladderOdd_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### stairEvenAlt (`(M, 1)`, lower-left `(1-M, -1)`), ladderOddAlt (`(M, 1)`, lower-left `(-1,-1)`) -/

theorem stairEvenAlt_lowerLeft (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) (hne : (BaseMask.stairEvenAlt.raw M).sites.Nonempty) :
    (BaseMask.stairEvenAlt.raw M).lowerLeft hne = (1 - M, -1) := by
  apply lowerLeft_of_minimal _ hne (1 - M, -1)
  · rw [BaseMask.mem_stairEvenAlt_raw_iff]
    omega
  · intro q hq
    rw [BaseMask.mem_stairEvenAlt_raw_iff] at hq
    omega

theorem stairEvenAlt_family (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) :
    ((M, 1) : Site) ∈ ((BaseMask.stairEvenAlt.tile M hM).llCenter (BaseMask.stairEvenAlt.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.stairEvenAlt.tile M hM).llCenter (BaseMask.stairEvenAlt.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.stairEvenAlt.tile M hM).llCenter (BaseMask.stairEvenAlt.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.stairEvenAlt M hM (1 - M, -1) (fun hne => stairEvenAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairEvenAlt M hM (1 - M, -1) (fun hne => stairEvenAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.stairEvenAlt M hM (1 - M, -1) (fun hne => stairEvenAlt_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [BaseMask.mem_stairEvenAlt_raw_iff] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem mem_ladderOddAlt_direct (M : ℤ) (pt : Site) :
    pt ∈ (BaseMask.ladderOddAlt.raw M).sites ↔
      (1 - M ≤ pt.1 ∧ pt.1 ≤ 2 * M - 2) ∧ (-1 ≤ pt.2 ∧ pt.2 ≤ M + 2) ∧
        (((pt.1 = -1 ∧ pt.2 = -1) ∨ (pt.1 = M ∧ pt.2 = M + 2)) ∨
          (-1 ≤ pt.1 + pt.2 ∧ pt.1 + pt.2 ≤ 2 * M + 1 ∧
            ¬ ((-1 ≤ pt.2 ∧ pt.2 ≤ 0 ∧ M ≤ pt.1) ∨ (M + 1 ≤ pt.2 ∧ pt.2 ≤ M + 2 ∧ pt.1 ≤ -1)))) := by
  rw [BaseMask.mem_ladderOddAlt_raw_iff]

theorem ladderOddAlt_lowerLeft (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) (hne : (BaseMask.ladderOddAlt.raw M).sites.Nonempty) :
    (BaseMask.ladderOddAlt.raw M).lowerLeft hne = (-1, -1) := by
  apply lowerLeft_of_minimal _ hne (-1, -1)
  · rw [mem_ladderOddAlt_direct]
    omega
  · intro q hq
    rw [mem_ladderOddAlt_direct] at hq
    omega

theorem ladderOddAlt_family (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((M, 1) : Site) ∈ ((BaseMask.ladderOddAlt.tile M hM).llCenter (BaseMask.ladderOddAlt.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.ladderOddAlt.tile M hM).llCenter (BaseMask.ladderOddAlt.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.ladderOddAlt.tile M hM).llCenter (BaseMask.ladderOddAlt.tile_nonempty M hM)).sites := by
  rw [tile_llCenter_iff BaseMask.ladderOddAlt M hM (-1, -1) (fun hne => ladderOddAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderOddAlt M hM (-1, -1) (fun hne => ladderOddAlt_lowerLeft M hM hne)]
  rw [tile_llCenter_iff BaseMask.ladderOddAlt M hM (-1, -1) (fun hne => ladderOddAlt_lowerLeft M hM hne)]
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_ladderOddAlt_direct] <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- The alternate odd family, stated with the parameter in the form `M = 2k+1` of the pure runs. -/
theorem stairOddAlt_family_of_eq (M k : ℤ) (h : M = 2 * k + 1) (hk : 1 ≤ k) (hM : BaseMask.Valid BaseMask.stairOddAlt M) :
    ((k + 1, k) : Site) ∈ ((BaseMask.stairOddAlt.tile M hM).llCenter (BaseMask.stairOddAlt.tile_nonempty M hM)).sites ∧
      ((1, 0) : Site) ∈ ((BaseMask.stairOddAlt.tile M hM).llCenter (BaseMask.stairOddAlt.tile_nonempty M hM)).sites ∧
      ((0, 1) : Site) ∈ ((BaseMask.stairOddAlt.tile M hM).llCenter (BaseMask.stairOddAlt.tile_nonempty M hM)).sites := by
  subst h
  exact stairOddAlt_family k hk

/-! ### The pure-run registers, for every run length (the mask parameters as in `BaseRun.registers`) -/

/-- The standard registers of the run `2^(e+1)` (`BaseRun.twos e`), the current and retained odd and even parents. -/
theorem twos_std_odd_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 2 + 1, 2 * (e : ℤ) + 3 + 2 - 1) : Site) ∈
        ((BaseRun.registers (.twos e)).llCenter.standard.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.currentOdd).val.sites :=
  stairOdd_family (2 * (e : ℤ) + 3 + 2) ⟨by omega, by omega⟩

theorem twos_std_even_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 1 + 1, 2 * (e : ℤ) + 3 + 1 - 1) : Site) ∈
        ((BaseRun.registers (.twos e)).llCenter.standard.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.currentEven).val.sites :=
  ladderEven_family (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩

theorem twos_std_retOdd_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 1, 2 * (e : ℤ) + 3 - 1) : Site) ∈
        ((BaseRun.registers (.twos e)).llCenter.standard.retainedOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.retainedOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.standard.retainedOdd).val.sites :=
  stairOdd_family (2 * (e : ℤ) + 3) ⟨by omega, by omega⟩

theorem twos_alt_odd_family (e : ℕ) :
    (((e : ℤ) + 2 + 1, (e : ℤ) + 2) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.currentOdd).val.sites :=
  stairOddAlt_family_of_eq (2 * (e : ℤ) + 3 + 2) ((e : ℤ) + 2) (by ring) (by omega) ⟨by omega, by omega⟩

theorem twos_alt_even_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 1 + 1, 2 * (e : ℤ) + 3 + 1 - 1) : Site) ∈
        ((BaseRun.registers (.twos e)).llCenter.alternate.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.currentEven).val.sites :=
  ladderEvenAlt_family (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩

theorem twos_alt_retOdd_family (e : ℕ) :
    (((e : ℤ) + 1 + 1, (e : ℤ) + 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.retainedOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.retainedOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.twos e)).llCenter.alternate.retainedOdd).val.sites :=
  stairOddAlt_family_of_eq (2 * (e : ℤ) + 3) ((e : ℤ) + 1) (by ring) (by omega) ⟨by omega, by omega⟩

/-- The registers of the run `3^(e+1)` (`BaseRun.threes e`). -/
theorem threes_std_odd_family (e : ℕ) :
    ((2 * (2 * (e : ℤ) + 3 + 1), 2) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentOdd).val.sites :=
  ladderOdd_family (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩

theorem threes_std_even_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 2, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.currentEven).val.sites :=
  stairEven_family (2 * (e : ℤ) + 3 + 2) ⟨by omega, by omega⟩

theorem threes_std_retEven_family (e : ℕ) :
    ((2 * (e : ℤ) + 3, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.retainedEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.retainedEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.standard.retainedEven).val.sites :=
  stairEven_family (2 * (e : ℤ) + 3) ⟨by omega, by omega⟩

theorem threes_alt_odd_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 1, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentOdd).val.sites :=
  ladderOddAlt_family (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩

theorem threes_alt_even_family (e : ℕ) :
    ((2 * (e : ℤ) + 3 + 2, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.currentEven).val.sites :=
  stairEvenAlt_family (2 * (e : ℤ) + 3 + 2) ⟨by omega, by omega⟩

theorem threes_alt_retEven_family (e : ℕ) :
    ((2 * (e : ℤ) + 3, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.retainedEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.retainedEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers (.threes e)).llCenter.alternate.retainedEven).val.sites :=
  stairEvenAlt_family (2 * (e : ℤ) + 3) ⟨by omega, by omega⟩

/-- The registers of the empty word's initializer (`BaseRun.empty`), the children `1/2` and `1/3`. -/
theorem empty_std_odd_family :
    ((3 + 1, 3 - 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentOdd).val.sites :=
  stairOdd_family 3 ⟨by omega, by omega⟩

theorem empty_std_even_family :
    ((3, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.standard.currentEven).val.sites :=
  stairEven_family 3 ⟨by omega, by omega⟩

theorem empty_alt_odd_family :
    (((1 : ℤ) + 1, (1 : ℤ)) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentOdd).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentOdd).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentOdd).val.sites :=
  stairOddAlt_family_of_eq 3 1 (by norm_num) (by norm_num) ⟨by omega, by omega⟩

theorem empty_alt_even_family :
    ((3, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentEven).val.sites ∧
      ((1, 0) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentEven).val.sites ∧
      ((0, 1) : Site) ∈ ((BaseRun.registers .empty).llCenter.alternate.currentEven).val.sites :=
  stairEvenAlt_family 3 ⟨by omega, by omega⟩

end FLatticePaper.Construction
