import FLatticePaper.Plane.Induction.ReflectedNonNative
import FLatticePaper.Plane.Induction.EPolicyLap

/-!
# Strictness of the reflected rank on all policy edges, eta = +1 (task 118, W1 base; bridge iv, part five)

`R0plus_edge_full`: for every edge `c → i` of `ePolicy` with `η = +1` (arbitrary centres, native or not),
`R0plus i < R0plus c`. The proof: reduction to the native representative (`R0plus_add_combine`), the flag identity
(`lap_black_iff`), and at a native centre `core_full`: a native target is `core_native`; a non-native target is a white
centre (`white_cases`: `selDisp` leaves) in one of the five triple cases (`tri_T1`..`tri_T5`), or a black centre (whose
targets are native, `black_native`).
-/

namespace FLatticePaper.ReflectedFull

open FLatticePaper FLatticePaper.Induction FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectWitness FLatticePaper.ReflectedStrict FLatticePaper.ReflectedRank FLatticePaper.ReflectedEdges FLatticePaper.ReflectedNonNative FLatticePaper.Construction

set_option maxHeartbeats 400000 in
theorem leafE1 (d : ℤ) (hd3 : 3 ≤ d) (y1 y2 e1 e2 : ℤ) (_hyN : NativeP d (y1, y2))
    (hS : (y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)) (he : (e1, e2) = (1, 0))
    (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he hS
  obtain ⟨rfl, rfl⟩ := he
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega
  · exact Or.inr (Or.inl ⟨h1, h2, rfl, rfl⟩)

set_option maxHeartbeats 400000 in
theorem leafE2 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (hev : (y1 + y2) % 2 = 0)
    (hR : (y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0))
    (he : (e1, e2) = (1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  rcases hR with ⟨h1, h2⟩ | hR0 | hR1 | ⟨h1, h2, h3⟩
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega
  · exfalso
    simp only [Prod.mk.injEq] at hR0
    obtain ⟨h1, h2⟩ := hR0
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega
  · simp only [Prod.mk.injEq] at hR1
    obtain ⟨h1, h2⟩ := hR1
    exact Or.inl ⟨h1, h2, rfl, rfl⟩
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega

set_option maxHeartbeats 400000 in
theorem leafE3 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (hev : (y1 + y2) % 2 = 0)
    (hS : ¬ ((y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)))
    (hR : ¬ ((y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)))
    (hl : y1 ≤ 0) (he : (e1, e2) = (-1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  simp only [Prod.mk.injEq, not_or, not_and] at hS hR
  exfalso
  apply hT
  unfold NativeP
  dsimp only
  simp only [Prod.mk.injEq]
  omega

set_option maxHeartbeats 400000 in
theorem leafE4 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (hev : (y1 + y2) % 2 = 0)
    (hS : ¬ ((y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)))
    (hR : ¬ ((y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨ (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)))
    (hl : ¬ y1 ≤ 0) (he : (e1, e2) = (1, 0)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  simp only [Prod.mk.injEq, not_or, not_and] at hS hR
  exfalso
  apply hT
  unfold NativeP
  dsimp only
  simp only [Prod.mk.injEq]
  omega

set_option maxHeartbeats 400000 in
theorem leafO1 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (hod : (y1 + y2) % 2 = 1)
    (hA : (y2 = 0 ∧ y1 = 1) ∨ (y1 + y2 = 1 ∧ 1 ≤ y2 ∧ y2 ≤ d - 1) ∨ (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d) ∨
      (y2 = d + 1 ∧ y1 = 2 - d))
    (he : (e1, e2) = (0, -1)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  have _hyNref := hyN
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h1, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by omega, by omega, rfl, rfl⟩)))
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega

set_option maxHeartbeats 400000 in
theorem leafO2 (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (hod : (y1 + y2) % 2 = 1)
    (hA : ¬ ((y2 = 0 ∧ y1 = 1) ∨ (y1 + y2 = 1 ∧ 1 ≤ y2 ∧ y2 ≤ d - 1) ∨ (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d) ∨
      (y2 = d + 1 ∧ y1 = 2 - d)))
    (he : (e1, e2) = (0, 1)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold NativeP at hyN
  dsimp only at hyN
  simp only [Prod.mk.injEq] at hyN
  simp only [not_or, not_and] at hA
  by_cases htop : y2 = d + 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨htop, by omega, by omega, by omega, rfl, rfl⟩)))
  · exfalso
    apply hT
    unfold NativeP
    dsimp only
    simp only [Prod.mk.injEq]
    omega

set_option maxHeartbeats 400000 in
theorem white_cases (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (hyN : NativeP d (y1, y2))
    (he : (e1, e2) = selDisp d 1 (y1, y2)) (hT : ¬ NativeP d (y1 + e1, y2 + e2)) :
    (y1 = d ∧ y2 = 1 ∧ e1 = 1 ∧ e2 = 0) ∨ (y1 = 2 ∧ y2 = d + 1 ∧ e1 = 1 ∧ e2 = 0) ∨
    (y1 = 1 ∧ y2 = 0 ∧ e1 = 0 ∧ e2 = -1) ∨ (y1 + y2 = 1 ∧ 2 - d ≤ y1 ∧ y1 ≤ 0 ∧ e1 = 0 ∧ e2 = -1) ∨
    (y2 = d + 1 ∧ (y1 + (d + 1)) % 2 = 1 ∧ y1 ≠ 2 - d ∧ y1 ≠ 2 ∧ e1 = 0 ∧ e2 = 1) := by
  by_cases hev : (y1 + y2) % 2 = 0
  · have hE : FLatticePaper.EvenSite (y1, y2) := hev
    unfold selDisp at he
    rw [if_pos hE] at he
    try dsimp only at he
    by_cases hS : (y1, y2) = (2 - d, d) ∨ (y1, y2) = (2, d + 1)
    · rw [if_pos hS] at he
      exact leafE1 d hd3 y1 y2 e1 e2 hyN hS he hT
    · rw [if_neg hS] at he
      by_cases hR : (y2 = 0 ∧ 2 ≤ y1) ∨ (y1, y2) = (0, 0) ∨ (y1, y2) = (d, 1) ∨
          (y2 = d + 1 ∧ 3 - d ≤ y1 ∧ y1 ≤ 0)
      · rw [if_pos hR] at he
        exact leafE2 d hd3 hdodd y1 y2 e1 e2 hyN hev hR he hT
      · rw [if_neg hR] at he
        by_cases hl : y1 ≤ 0
        · rw [if_pos hl] at he
          exact leafE3 d hd3 hdodd y1 y2 e1 e2 hyN hev hS hR hl he hT
        · rw [if_neg hl] at he
          exact leafE4 d hd3 hdodd y1 y2 e1 e2 hyN hev hS hR hl he hT
  · have hO : ¬ FLatticePaper.EvenSite (y1, y2) := hev
    have hod : (y1 + y2) % 2 = 1 := by omega
    unfold selDisp at he
    rw [if_neg hO] at he
    try dsimp only at he
    by_cases hA : (y2 = 0 ∧ y1 = 1) ∨ (y1 + y2 = 1 ∧ 1 ≤ y2 ∧ y2 ≤ d - 1) ∨
        (y1 + y2 = d + 2 ∧ 2 ≤ y1 ∧ y1 ≤ d) ∨ (y2 = d + 1 ∧ y1 = 2 - d)
    · rw [if_pos hA] at he
      exact leafO1 d hd3 hdodd y1 y2 e1 e2 hyN hod hA he hT
    · rw [if_neg hA] at he
      exact leafO2 d hd3 hdodd y1 y2 e1 e2 hyN hod hA he hT

set_option maxHeartbeats 400000 in
theorem black_native (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (y1 y2 e1 e2 : ℤ) (η : ℤ)
    (hN : NativeP d (y1, y2)) (hB : ¬ WhiteN d (y1, y2))
    (h : RetNat d η True (y1, y2) ((y1, y2) + (e1, e2))) :
    NativeP d (y1 + e1, y2 + e2) := by
  have hpar := edge_black d y1 y2 e1 e2 η hd3 hdodd hN hB h
  have hu := black_unit d η y1 y2 e1 e2 h
  unfold WhiteN at hB
  unfold FLatticePaper.EvenSite at hB
  dsimp only at hB
  unfold NativeP at hN ⊢
  dsimp only at hN ⊢
  simp only [Prod.mk.injEq] at hN hu ⊢
  simp only [not_or, not_and] at hB
  omega

set_option maxHeartbeats 400000 in
theorem core_full (k : ℕ) (y1 y2 e1 e2 : ℤ) (hyN : NativeP (2 * (k : ℤ) + 3) (y1, y2))
    (hb : RetNat (2 * (k : ℤ) + 3) 1 (laplacian (reciprocalField k) (y1, y2) = -1) (y1, y2)
      ((y1, y2) + (e1, e2))) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1 + e1, y2 + e2) <
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1, y2) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  by_cases hT : NativeP (2 * (k : ℤ) + 3) (y1 + e1, y2 + e2)
  · exact core_native k y1 y2 e1 e2 hyN hb hT
  · by_cases hl : laplacian (reciprocalField k) (y1, y2) = -1
    · exfalso
      rw [eq_true hl] at hb
      have hB := (lap_black_iff k (y1, y2) hyN).mp hl
      exact hT (black_native (2 * (k : ℤ) + 3) hd3 hdodd y1 y2 e1 e2 1 hyN hB hb)
    · rw [eq_false hl] at hb
      have hW : WhiteN (2 * (k : ℤ) + 3) (y1, y2) := by
        by_contra hw
        exact hl ((lap_black_iff k (y1, y2) hyN).mpr hw)
      have he := (retNat_white_pt hd3 hdodd (Or.inl rfl) hyN hW (e1, e2)).mp hb
      have hc := white_cases (2 * (k : ℤ) + 3) hd3 hdodd y1 y2 e1 e2 hyN he hT
      rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
      · subst h1 h2 h3 h4
        exact tri_T4 (2 * (k : ℤ) + 3) hd3 hdodd hden
      · subst h1 h2 h3 h4
        exact tri_T5 (2 * (k : ℤ) + 3) hd3 hdodd hden
      · subst h1 h2 h3 h4
        exact tri_T2 (2 * (k : ℤ) + 3) hd3 hdodd hden
      · subst h4 h5
        have hA : (2 - y1) + (2 * (k : ℤ) + 3 + 1 - y2) = 2 * (k : ℤ) + 3 + 2 := by omega
        have hA2 : 2 ≤ 2 - y1 := by omega
        have hA3 : 2 - y1 ≤ 2 * (k : ℤ) + 3 := by omega
        exact tri_T1 (2 * (k : ℤ) + 3) hd3 hdodd hden y1 y2 hyN hA hA2 hA3
      · subst h5 h6 h1
        exact tri_T3 (2 * (k : ℤ) + 3) hd3 hdodd hden y1 hyN h2 h3 h4

set_option maxHeartbeats 400000 in
theorem R0plus_edge_full (k : ℕ) (c i : Pt)
    (h : ePolicy (2 * (k : ℤ) + 3) 1 (laplacian (reciprocalField k)) c i) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) i <
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) c := by
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
  have hcore := core_full k y1 y2 e1 e2 hyN h
  have hI : i = (y1 + e1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + e2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  have hcpair : c = (y1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  rw [hI, hcpair]
  have h1 := R0plus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1 + e1, y2 + e2) a b
  have h2 := R0plus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1, y2) a b
  simp only at h1 h2
  linarith

end FLatticePaper.ReflectedFull
