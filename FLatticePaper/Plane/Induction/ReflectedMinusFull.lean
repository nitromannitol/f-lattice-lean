import FLatticePaper.Plane.Induction.ReflectedMinusStrict
import FLatticePaper.Plane.Induction.ReflectedMinusNonNative
import FLatticePaper.Plane.Induction.ReflectedFull
import FLatticePaper.Plane.Induction.ReflectedEdges

/-!
# Strictness of the reflected plus rank on all policy edges, eta = -1 (task 118, W1 base; bridge iv, part four)

`R0minus_edge_full`: for every edge `c → i` of `ePolicy` with `η = -1` (arbitrary centres, native or not),
`R0minus i < R0minus c`. The proof is the sign-`-1` analogue of `ReflectedFull`: reduction to the native representative
(`R0minus_add_combine`), the flag identity (`lap_black_iff`), and at a native centre `minus_core_full`. A native target is
`minus_core_native` (`ReflectedMinusStrict`); a non-native target is a white centre (`minus_white_cases`: the `selDisp d (-1)`
leaves) in one of the four triple cases (`ReflectedMinusNonNative`), or a black centre (whose targets are native,
`black_native`).
-/

namespace FLatticePaper.ReflectedMinusFull

open FLatticePaper FLatticePaper.Induction FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectWitness
  FLatticePaper.ReflectedStrict FLatticePaper.ReflectedRank FLatticePaper.ReflectedEdges FLatticePaper.ReflectedFull
  FLatticePaper.ReflectedRankPlus FLatticePaper.ReflectedMinusStrict FLatticePaper.ReflectedMinusNonNative
  FLatticePaper.Construction

set_option maxHeartbeats 400000 in
/-- Leaf: the special even centres `(2-d, d)`, `(2, d+1)` with `e = (-1, 0)`. -/
theorem minusS (d : ℤ) (hd3 : 3 ≤ d) (y1 y2 e1 e2 : ℤ)
    (hS : (y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)) (he : (e1, e2) = (-1, 0))
    (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at hS he
  obtain ⟨rfl, rfl⟩ := he
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, rfl, rfl⟩
  · exact (hT (by subst h1 h2; unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega)).elim

set_option maxHeartbeats 400000 in
/-- Leaf: the even region `y2 = 0 ∧ 2 ≤ y1` or the top-row segment, or `(0,0)`, or `(d,1)`, with `e = (1, 0)`. -/
theorem minusR (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ)
    (hyN : NativeP d (y1, y2)) (hev : (y1 + y2) % 2 = 0)
    (hR : (y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0))
    (he : (e1, e2) = (1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he hR
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  by_cases hD : y1 = d ∧ y2 = 1
  · exact Or.inr (Or.inl ⟨hD.1, hD.2, rfl, rfl⟩)
  · exact (hT (by unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega)).elim

set_option maxHeartbeats 400000 in
/-- Leaf: the even generic points with `y1 ≤ 0` and `e = (-1, 0)`: the target is native. -/
theorem minusL (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ)
    (hyN : NativeP d (y1, y2)) (hev : (y1 + y2) % 2 = 0)
    (hS : ¬ ((y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)))
    (hR : ¬ ((y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)))
    (hl : y1 ≤ 0) (he : (e1, e2) = (-1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he hS hR
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  exact (hT (by unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega)).elim

set_option maxHeartbeats 400000 in
/-- Leaf: the even generic points with `y1 ≥ 1` and `e = (1, 0)`: the target is native. -/
theorem minusX (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ)
    (hyN : NativeP d (y1, y2)) (hev : (y1 + y2) % 2 = 0)
    (hS : ¬ ((y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)))
    (hR : ¬ ((y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)))
    (hl : ¬ y1 ≤ 0) (he : (e1, e2) = (1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he hS hR
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  exact (hT (by unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega)).elim

set_option maxHeartbeats 400000 in
/-- Leaf: the odd centres, `e = (0, 1)`: the non-native targets are the top row and the anti-diagonal. -/
theorem minusO (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ)
    (hyN : NativeP d (y1, y2)) (hod : (y1 + y2) % 2 = 1) (he : (e1, e2) = (0, 1))
    (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  by_cases hC : y2 = d + 1
  · exact Or.inr (Or.inr (Or.inl ⟨hC, by omega, by omega, by omega, rfl, rfl⟩))
  · by_cases hD : y1 + y2 = d + 2
    · exact Or.inr (Or.inr (Or.inr ⟨hD, by omega, by omega, rfl, rfl⟩))
    · exact (hT (by unfold NativeP; dsimp only; simp only [Prod.mk.injEq]; omega)).elim

set_option maxHeartbeats 400000 in
/-- **The white classification for `eta = -1`.** A native white centre with a non-native target is in one of four cases. -/
theorem minus_white_cases (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ)
    (hyN : NativeP d (y1, y2)) (he : (e1, e2) = selDisp d (-1) (y1, y2))
    (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = 2 - d ∧ y2 = d ∧ e1 = -1 ∧ e2 = 0) ∨ (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 1 ∧ e1 = 0 ∧ e2 = 1) ∨
    (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d ∧ e1 = 0 ∧ e2 = 1) := by
  by_cases hev : (y1 + y2) % 2 = 0
  · have hE : FLatticePaper.EvenSite (y1, y2) := hev
    unfold selDisp at he
    rw [if_pos hE] at he
    try dsimp only at he
    by_cases hS : (y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)
    · rw [if_pos hS] at he
      exact minusS d hd3 y1 y2 e1 e2 hS he hT
    · rw [if_neg hS] at he
      by_cases hR : (y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨
          (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)
      · rw [if_pos hR] at he
        exact minusR d hd3 hdodd y1 y2 e1 e2 hyN hev hR he hT
      · rw [if_neg hR] at he
        by_cases hl : y1 ≤ 0
        · rw [if_pos hl] at he
          exact minusL d hd3 hdodd y1 y2 e1 e2 hyN hev hS hR hl he hT
        · rw [if_neg hl] at he
          exact minusX d hd3 hdodd y1 y2 e1 e2 hyN hev hS hR hl he hT
  · have hO : ¬ FLatticePaper.EvenSite (y1, y2) := hev
    have hod : (y1 + y2) % 2 = 1 := by omega
    have hsel : (e1, e2) = (0, 1) := by
      unfold selDisp at he
      rw [if_neg hO] at he
      split_ifs at he with hA
      · rw [he]; norm_num
      · exact he
    exact minusO d hd3 hdodd y1 y2 e1 e2 hyN hod hsel hT

set_option maxHeartbeats 400000 in
theorem minus_core_native (k : ℕ) (y1 y2 e1 e2 : ℤ) (hyN : NativeP (2 * (k : ℤ) + 3) (y1, y2))
    (hb : RetNat (2 * (k : ℤ) + 3) (-1) (laplacian (reciprocalField k) (y1, y2) = -1) (y1, y2)
      ((y1, y2) + (e1, e2)))
    (hT : NativeP (2 * (k : ℤ) + 3) ((y1, y2) + (e1, e2))) :
    R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1 + e1, y2 + e2) <
      R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1, y2) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  have hT' : NativeP (2 * (k : ℤ) + 3) (2 - (y1 + e1), 2 * (k : ℤ) + 3 + 1 - (y2 + e2)) := by
    have := (nativeP_refl (2 * (k : ℤ) + 3) (y1 + e1) (y2 + e2)).mpr hT
    simpa using this
  by_cases hl : laplacian (reciprocalField k) (y1, y2) = -1
  · have hB := (lap_black_iff k (y1, y2) hyN).mp hl
    rw [eq_true hl] at hb
    exact R0minus_edge_black_minus (2 * (k : ℤ) + 3) y1 y2 e1 e2 hd3 hdodd hden hyN hB hb hT'
  · have hW : WhiteN (2 * (k : ℤ) + 3) (y1, y2) := by
      by_contra hw
      exact hl ((lap_black_iff k (y1, y2) hyN).mpr hw)
    rw [eq_false hl] at hb
    exact R0minus_edge_white_minus (2 * (k : ℤ) + 3) y1 y2 e1 e2 hd3 hdodd hden hyN hW hb hT'

set_option maxHeartbeats 400000 in
theorem minus_core_full (k : ℕ) (y1 y2 e1 e2 : ℤ) (hyN : NativeP (2 * (k : ℤ) + 3) (y1, y2))
    (hb : RetNat (2 * (k : ℤ) + 3) (-1) (laplacian (reciprocalField k) (y1, y2) = -1) (y1, y2)
      ((y1, y2) + (e1, e2))) :
    R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1 + e1, y2 + e2) <
      R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1, y2) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  by_cases hT : NativeP (2 * (k : ℤ) + 3) (y1 + e1, y2 + e2)
  · exact minus_core_native k y1 y2 e1 e2 hyN hb hT
  · by_cases hl : laplacian (reciprocalField k) (y1, y2) = -1
    · exfalso
      rw [eq_true hl] at hb
      have hB := (lap_black_iff k (y1, y2) hyN).mp hl
      exact hT (black_native (2 * (k : ℤ) + 3) hd3 hdodd y1 y2 e1 e2 (-1) hyN hB hb)
    · rw [eq_false hl] at hb
      have hW : WhiteN (2 * (k : ℤ) + 3) (y1, y2) := by
        by_contra hw
        exact hl ((lap_black_iff k (y1, y2) hyN).mpr hw)
      have he := (retNat_white_pt hd3 hdodd (Or.inr rfl) hyN hW (e1, e2)).mp hb
      have hc := minus_white_cases (2 * (k : ℤ) + 3) hd3 hdodd y1 y2 e1 e2 hyN he hT
      rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5⟩
      · subst h1 h2 h3 h4
        exact minus_tri_A (2 * (k : ℤ) + 3) hd3 hdodd hden
      · subst h1 h2 h3 h4
        exact minus_tri_B (2 * (k : ℤ) + 3) hd3 hdodd hden
      · subst h1 h5 h6
        exact minus_tri_C (2 * (k : ℤ) + 3) hd3 hdodd hden y1 h3 h4 h2
      · subst h4 h5
        exact minus_tri_D (2 * (k : ℤ) + 3) hd3 hdodd hden y1 y2 h1 h2 h3

set_option maxHeartbeats 400000 in
theorem R0minus_edge_full (k : ℕ) (c i : Pt)
    (h : ePolicy (2 * (k : ℤ) + 3) (-1) (laplacian (reciprocalField k)) c i) :
    R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) i <
      R0minus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) c := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  obtain ⟨hyN, a, b, hc⟩ := nativeRep_spec hden c
  rw [combine_mk_one hdodd] at hc
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  simp only [Prod.fst_add, Prod.snd_add] at hc1 hc2
  unfold ePolicy at h
  rw [laplacian_reciprocal_rep k c] at h
  generalize hy : nativeRep (2 * (k : ℤ) + 3) c = y at h hyN hc1 hc2
  obtain ⟨y1, y2⟩ := y
  simp only at hc1 hc2
  obtain ⟨e1, he1⟩ : ∃ e1 : ℤ, e1 = i.1 - c.1 := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : ℤ, e2 = i.2 - c.2 := ⟨_, rfl⟩
  have hie : i - c = (e1, e2) := by
    ext <;> simp [he1, he2]
  rw [hie] at h
  have hcore := minus_core_full k y1 y2 e1 e2 hyN h
  have hI : i = (y1 + e1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + e2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  have hcpair : c = (y1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  rw [hI, hcpair]
  have h1 := R0minus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1 + e1, y2 + e2) a b
  have h2 := R0minus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1, y2) a b
  simp only at h1 h2
  linarith

end FLatticePaper.ReflectedMinusFull
