import FLatticePaper.Plane.Induction.ThreesMidpoint
import FLatticePaper.Plane.Induction.EvenStep

/-! Task 53 (hbaseThree), step 2: the nine neighbour cases of the reciprocal second difference, the dispatcher
`threes_step`, and the base identity `threes_alternate` (the midpoint of the reciprocal field of `3^k` is the explicit base
alternate). Each case is a separate lemma so that every declaration stays within the default heartbeat budget. -/

namespace FLatticePaper.Induction.ThreesMidpoint

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

theorem mem_TS_iff' (d : ℤ) (p : Site) : p ∈ (BaseMask.stairEven.raw d).sites ↔
    (2 - d ≤ p.1 ∧ p.1 ≤ d) ∧ (0 ≤ p.2 ∧ p.2 ≤ d + 1) ∧
      (BaseMask.StairEvenCorner d p ∨ (1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ d + 2)) :=
  BaseMask.mem_stairEven_raw_iff

theorem leaf_K0L0 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1, y.2) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  clear hc
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (0) (0) (0) (y.1 + 1, y.2) (y.1 - 1, y.2) HK HL (by simp [thr]) (by simp [thr])
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1, y.2)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1, y.2)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K0L1 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1, y.2) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  clear hc
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (0) (-1) (0) (y.1 + 1, y.2) (y.1 - 1 + d, y.2 + 1) HK HL (by simp [thr]) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1, y.2)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1 + d, y.2 + 1)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K0L2 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1, y.2) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (0) (-1) (1) (y.1 + 1, y.2) (y.1 - 2 + 2 * d, y.2 - d) HK HL (by simp [thr]) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1, y.2)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 2 + 2 * d, y.2 - d)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K1L0 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1 - d, y.2 - 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  clear hc
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (1) (0) (0) (0) (y.1 + 1 - d, y.2 - 1) (y.1 - 1, y.2) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (by simp [thr])
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1 - d, y.2 - 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1, y.2)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K1L1 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1 - d, y.2 - 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  clear hc
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (1) (0) (-1) (0) (y.1 + 1 - d, y.2 - 1) (y.1 - 1 + d, y.2 + 1) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1 - d, y.2 - 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1 + d, y.2 + 1)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K1L2 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 1 - d, y.2 - 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (1) (0) (-1) (1) (y.1 + 1 - d, y.2 - 1) (y.1 - 2 + 2 * d, y.2 - d) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 1 - d, y.2 - 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 2 + 2 * d, y.2 - d)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K2L0 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 2 - d, y.2 + d + 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (-1) (0) (0) (y.1 + 2 - d, y.2 + d + 1) (y.1 - 1, y.2) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (by simp [thr])
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 2 - d, y.2 + d + 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1, y.2)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K2L1 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 2 - d, y.2 + d + 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (-1) (-1) (0) (y.1 + 2 - d, y.2 + d + 1) (y.1 - 1 + d, y.2 + 1) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 2 - d, y.2 + d + 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 1 + d, y.2 + 1)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem leaf_K2L2 (d c : ℤ) (hd : 3 ≤ d) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b : ℤ)
    (HK : (y.1 + 2 - d, y.2 + d + 1) ∈ (BaseMask.stairEven.raw d).sites)
    (HL : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites) :
    -1 ≤ RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ∧
      RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) ≤ 1 ∧
      (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b) = 1 ↔
        stairEvenAltMarker d (y + thr d a b + (1, 0)) = 1) := by
  obtain ⟨key, hmk⟩ := combo_identity d c RF hred y hy a b (0) (-1) (-1) (1) (y.1 + 2 - d, y.2 + d + 1) (y.1 - 2 + 2 * d, y.2 - d) HK HL (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring)) (Prod.ext (by simp only [thr, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_sub]; ring))
  rw [hmk, marker_tile d hd _ HK]
  generalize RF (y + thr d a b + (1, 0)) = A at key ⊢
  generalize RF (y + thr d a b - (1, 0)) = B at key ⊢
  generalize RF (y + thr d a b) = C at key ⊢
  rw [mem_TS_iff'] at hy HK HL
  simp only [Mt] at key
  simp only at key hy HK HL ⊢
  by_cases h1 : BaseMask.StairEvenCorner d (y.1 + 2 - d, y.2 + d + 1)
  <;> by_cases h2 : BaseMask.StairEvenCorner d (y.1 - 2 + 2 * d, y.2 - d)
  <;> by_cases h3 : BaseMask.StairEvenCorner d y
  <;> simp only [h1, h2, h3, true_or, false_or, and_true, if_true, if_false] at key hy HK HL ⊢
  <;> (try unfold BaseMask.StairEvenCorner at h1 h2 h3)
  <;> (try rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩)
  <;> (try rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩)
  <;> (try rcases h3 with ⟨h3a, h3b⟩ | ⟨h3a, h3b⟩)
  <;> (try clear h1 h2 h3)
  <;> (try ring_nf at key)
  <;> (try split_ifs at ⊢)
  <;> refine ⟨by omega, by omega, ?_⟩
  <;> constructor <;> intro h <;> omega

theorem threes_step (d c : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hc : 2 * c = -d ^ 2 - 3 * d) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (z : Site) :
    -1 ≤ RF (z + (1, 0)) + RF (z - (1, 0)) - 2 * RF z ∧
      RF (z + (1, 0)) + RF (z - (1, 0)) - 2 * RF z ≤ 1 ∧
      (RF (z + (1, 0)) + RF (z - (1, 0)) - 2 * RF z = 1 ↔ stairEvenAltMarker d (z + (1, 0)) = 1) := by
  obtain ⟨y, hy, a, b, rfl⟩ := stair_cover d hd hodd z
  by_cases hK0 : (y.1 + 1, y.2) ∈ (BaseMask.stairEven.raw d).sites
  · by_cases hL0 : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites
    · exact leaf_K0L0 d c hd hc RF hred y hy a b hK0 hL0
    · by_cases hL1 : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites
      · exact leaf_K0L1 d c hd hc RF hred y hy a b hK0 hL1
      · have hL2 : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites := by
          rcases minus_table d hd y hy with h | h | h
          · exact absurd h hL0
          · exact absurd h hL1
          · exact h
        exact leaf_K0L2 d c hd hc RF hred y hy a b hK0 hL2
  · by_cases hK1 : (y.1 + 1 - d, y.2 - 1) ∈ (BaseMask.stairEven.raw d).sites
    · by_cases hL0 : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites
      · exact leaf_K1L0 d c hd hc RF hred y hy a b hK1 hL0
      · by_cases hL1 : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites
        · exact leaf_K1L1 d c hd hc RF hred y hy a b hK1 hL1
        · have hL2 : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites := by
            rcases minus_table d hd y hy with h | h | h
            · exact absurd h hL0
            · exact absurd h hL1
            · exact h
          exact leaf_K1L2 d c hd hc RF hred y hy a b hK1 hL2
    · have hK2 : (y.1 + 2 - d, y.2 + d + 1) ∈ (BaseMask.stairEven.raw d).sites := by
        rcases plus_table d hd y hy with h | h | h
        · exact absurd h hK0
        · exact absurd h hK1
        · exact h
      by_cases hL0 : (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites
      · exact leaf_K2L0 d c hd hc RF hred y hy a b hK2 hL0
      · by_cases hL1 : (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites
        · exact leaf_K2L1 d c hd hc RF hred y hy a b hK2 hL1
        · have hL2 : (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites := by
            rcases minus_table d hd y hy with h | h | h
            · exact absurd h hL0
            · exact absurd h hL1
            · exact h
          exact leaf_K2L2 d c hd hc RF hred y hy a b hK2 hL2

theorem threes_shortShift (k : ℕ) : (frameAt (List.replicate k Digit.three)).shortShift = (-2, 0) := by
  have hp : (frameAt (List.replicate k Digit.three)).parents = ⟨⟨0, 1⟩, ⟨1, 2 * (k : ℤ) + 1⟩⟩ :=
    parentsAt_replicate_three k
  unfold ChildFrame.shortShift ChildFrame.eps
  rw [hp]
  simp [Fraction.det]

/-- The base identity at the even child `1/(2k+3)` of `3^k`: the midpoint is the explicit base alternate, with constant
zero. The second difference lemma `threes_step` gives the value of the rounded midpoint. -/
theorem threes_alternate (k : ℕ) (x : Site) :
    (frameAt (List.replicate k Digit.three)).alternate (standardField (List.replicate k Digit.three)) x =
      stairEvenAltField (2 * (k : ℤ) + 3) (standardField (List.replicate k Digit.three)) x := by
  rw [standardField_threes]
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  obtain ⟨z, rfl⟩ : ∃ z : Site, x = z + (1, 0) := ⟨x - (1, 0), by simp⟩
  obtain ⟨h1, h2, h3⟩ := threes_step (2 * (k : ℤ) + 3) (stairEvenConstantV (2 * (k : ℤ) + 3)) hd hodd
    (stairEvenConstantV_twice _ hodd) (reciprocalField k) (fun y i j hy => reciprocal_hred k y hy i j) z
  have hsh := threes_shortShift k
  have e2 : z + (1, 0) + (-2, 0) = z - (1, 0) := Prod.ext (by simp; ring) (by simp)
  have e1 : z + (1, 0) - (1, 0) = z := by simp
  simp only [ChildFrame.alternate, roundedMidpoint, hsh, e2, stairEvenAltField, e1]
  have hm : stairEvenAltMarker (2 * (k : ℤ) + 3) (z + (1, 0)) = 0 ∨
      stairEvenAltMarker (2 * (k : ℤ) + 3) (z + (1, 0)) = 1 := by
    unfold stairEvenAltMarker
    dsimp only
    split_ifs <;> simp
  rcases hm with hm | hm
  · have hne : reciprocalField k (z + (1, 0)) + reciprocalField k (z - (1, 0)) - 2 * reciprocalField k z ≠ 1 :=
      fun h => by
        have h' := h3.mp h
        omega
    rw [hm]
    omega
  · have heq := h3.mpr hm
    rw [hm]
    omega

end FLatticePaper.Induction.ThreesMidpoint
