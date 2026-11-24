import FLatticePaper.Plane.Induction.EPolicyPrescribed
import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.AndOrRank

/-!
# The unit square clauses of the signed policy e(-1, eta) on the reciprocal field (task 118, W1 base)

`SquareClauseSat F sel a b`: some corner of the unit square at `(a, b)` is not kept inside the square. The selection
`selF` is equivariant under the deck (`selF_deck`), the laplacian is deck invariant, so the clause at `(a, b)` follows from
the clause at a native lower-left corner (`squareClause_of_native`). The remaining statement is the case analysis of the
native lower-left squares (`squares_native`).
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey FLatticePaper.Induction
  FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The selection of a deck translate of a site is the selection of the site (the representatives are duplicates). -/
theorem selDisp_nativeRep_deck (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : ℤ × ℤ) (i0 j0 : ℤ) :
    selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)) =
      selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) c) := by
  have hden := stairEven_valid_reciprocal k
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hc1 : ∀ i j : ℤ, ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1 =
      i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)) := fun i j => by
    rw [combine_mk_one hd]
  have hc2 : ∀ i j : ℤ, ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2 =
      i + j * ((2 * (k : ℤ) + 3) + 1) := fun i j => by
    rw [combine_mk_one hd]
    ring
  obtain ⟨hy1, i1, j1, h1⟩ := nativeRep_spec hden c
  obtain ⟨hy2, i2, j2, h2⟩ := nativeRep_spec hden (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have f1 := congrArg Prod.fst h2
  have f2 := congrArg Prod.snd h2
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2 f1 f2
  rw [hc1 i1 j1] at e1
  rw [hc2 i1 j1] at e2
  rw [hc1 i0 j0, hc1 i2 j2] at f1
  rw [hc2 i0 j0, hc2 i2 j2] at f2
  have hq1 : (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)).1 =
      (nativeRep (2 * (k : ℤ) + 3) c).1 + (i0 + i1 - i2) * (2 * (k : ℤ) + 3) + (j0 + j1 - j2) * (1 - (2 * (k : ℤ) + 3)) := by
    linear_combination e1 - f1
  have hq2 : (nativeRep (2 * (k : ℤ) + 3) (c + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i0 j0)).2 =
      (nativeRep (2 * (k : ℤ) + 3) c).2 + (i0 + i1 - i2) + (j0 + j1 - j2) * ((2 * (k : ℤ) + 3) + 1) := by
    linear_combination e2 - f2
  exact (selDisp_dup (by omega) hd hη hy1 hy2 hq1 hq2).symm

/-- Translating a square translates its corners. -/
theorem mem_squareCorners_translate (a b : ℤ) (l c : ℤ × ℤ) :
    c ∈ squareCorners a b ↔ c + l ∈ squareCorners (a + l.1) (b + l.2) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨l1, l2⟩ := l
  unfold squareCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The unit square clause transfers across a deck translation: a non-kept corner of the square stays non-kept. -/
theorem squareClause_translate (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (a b : ℤ) (i j : ℤ)
    (h : SquareClauseSat (reciprocalField k) (selF k η) a b) :
    SquareClauseSat (reciprocalField k) (selF k η) (a + ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1)
      (b + ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2) := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hl0 : (((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1 +
      ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2) % 2 = 0 :=
    combine_sum_even hd i j
  set l := (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j with hl
  unfold SquareClauseSat at h ⊢
  intro hall
  apply h
  intro c hc
  have hc' := hall (c + l) ((mem_squareCorners_translate a b l c).1 hc)
  have hlap : laplacian (reciprocalField k) (c + l) = laplacian (reciprocalField k) c :=
    laplacian_reciprocal_deck k c i j
  have hsel : selF k η (c + l) = selF k η c + l := by
    unfold selF
    rw [selDisp_nativeRep_deck k η hη c i j]
    abel
  unfold keptInside at hc' ⊢
  rw [hlap, hsel] at hc'
  by_cases hb : laplacian (reciprocalField k) c = -1
  · rw [if_pos hb] at hc' ⊢
    rw [incomingNeg_add hl0, incomingPos_add hl0] at hc'
    rcases hc' with h1 | h1
    · exact Or.inl ((mem_squareCorners_translate a b l _).mpr h1)
    · exact Or.inr ((mem_squareCorners_translate a b l _).mpr h1)
  · rw [if_neg hb] at hc' ⊢
    exact (mem_squareCorners_translate a b l _).mpr hc'

/-- The clause at every square follows from the clause at the native lower-left squares. -/
theorem squareClause_all (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hnat : ∀ a b : ℤ, NativeP (2 * (k : ℤ) + 3) (a, b) →
      SquareClauseSat (reciprocalField k) (selF k η) a b) (a b : ℤ) :
    SquareClauseSat (reciprocalField k) (selF k η) a b := by
  obtain ⟨⟨y1, y2⟩, hyN, i, j, hab⟩ := exists_native_rep (stairEven_valid_reciprocal k) (a, b)
  have hy := squareClause_translate k η hη y1 y2 i j (hnat y1 y2 hyN)
  have h1 : y1 + ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).1 = a := by
    have := congrArg Prod.fst hab
    simp only [Prod.fst_add] at this
    linarith
  have h2 : y2 + ((Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j).2 = b := by
    have := congrArg Prod.snd hab
    simp only [Prod.snd_add] at this
    linarith
  rw [h1, h2] at hy
  exact hy

/-- The selection of a deck translate of a native site: `selF (r + l) = (r + l) + selDisp r` for a native `r`. -/
theorem selF_deck_native (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) {r : ℤ × ℤ} (hr : NativeP (2 * (k : ℤ) + 3) r) (i j : ℤ) :
    selF k η (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) =
      r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j + selDisp (2 * (k : ℤ) + 3) η r := by
  have h1 : selF k η (r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) =
      selF k η r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    unfold selF
    rw [selDisp_nativeRep_deck k η hη r i j]
    abel
  have h2 : selF k η r = r + selDisp (2 * (k : ℤ) + 3) η r := by
    unfold selF
    rw [selDisp_nativeRep k η hη hr]
  rw [h1, h2]
  abel

/-- A witness of the unit square clause: a corner `w = r + l` (`r` native, `l` a deck vector) that is white and whose selected
input `w + selDisp r` leaves the square. -/
theorem squareClause_of_rep (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (a b : ℤ) {w r : ℤ × ℤ}
    (hw : w ∈ squareCorners a b) (hr : NativeP (2 * (k : ℤ) + 3) r) (i j : ℤ)
    (hwr : w = r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j)
    (hlap : laplacian (reciprocalField k) r = 0)
    (hout : r + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j + selDisp (2 * (k : ℤ) + 3) η r ∉
      squareCorners a b) :
    SquareClauseSat (reciprocalField k) (selF k η) a b := by
  intro hall
  have hk := hall w hw
  unfold keptInside at hk
  have hwl : laplacian (reciprocalField k) w = 0 := by
    rw [hwr, laplacian_reciprocal_deck k r i j]
    exact hlap
  rw [if_neg (by rw [hwl]; norm_num)] at hk
  rw [hwr, selF_deck_native k η hη hr i j] at hk
  exact hout hk

/-- A native site whose laplacian is zero (a white site), from its even/odd and band conditions. -/
theorem lap_zero_of_native (k : ℕ) {r : ℤ × ℤ} (hr : NativeP (2 * (k : ℤ) + 3) r)
    (h : (EvenSite r → r.1 ≠ 1) ∧
      (¬ EvenSite r → ¬ (0 < r.2 ∧ r.2 < (2 * (k : ℤ) + 3) + 1 ∧ 1 < r.1 + r.2 ∧ r.1 + r.2 < (2 * (k : ℤ) + 3) + 2))) :
    laplacian (reciprocalField k) r = 0 := by
  rw [laplacian_reciprocal_native k hr]
  by_cases he : EvenSite r
  · rw [if_pos he, if_neg (h.1 he)]
  · rw [if_neg he, if_neg (h.2 he)]

/-- A witness rule for the native lower-left square `(a, b)`: the corner `(a + p, b + q)` equals the native site
`r = (a + p, b + q) - (i U + j V)` shifted by the deck vector `i U + j V`, with `r` white and the selected input outside. -/
theorem square_rule (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (a b p q i j : ℤ) (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1)
    (hr : NativeP (2 * (k : ℤ) + 3)
      (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))), b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))))
    (hwhite : ((EvenSite (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))),
          b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) →
          a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))) ≠ 1) ∧
        (¬ EvenSite (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))),
          b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) → ¬ (0 < b + q - (i + j * (1 + (2 * (k : ℤ) + 3))) ∧
          b + q - (i + j * (1 + (2 * (k : ℤ) + 3))) < (2 * (k : ℤ) + 3) + 1 ∧
          1 < (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)))) + (b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) ∧
          (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)))) + (b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) <
            (2 * (k : ℤ) + 3) + 2))))
    (hout : (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))), b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) +
        (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j +
        selDisp (2 * (k : ℤ) + 3) η (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))),
          b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) ∉ squareCorners a b) :
    SquareClauseSat (reciprocalField k) (selF k η) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hw : (a + p, b + q) ∈ squareCorners a b := by
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [squareCorners]
  have hwr : (a + p, b + q) = (a + p - (i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3))),
      b + q - (i + j * (1 + (2 * (k : ℤ) + 3)))) + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j := by
    rw [combine_mk_one hd]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  exact squareClause_of_rep k η hη a b hw hr i j hwr (lap_zero_of_native k hr hwhite) hout

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_1 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (_h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) (h4 : a ≤ (2 * (k : ℤ) + 3) - 1) (h5 : a + b ≤ (2 * (k : ℤ) + 3)) (h6 : a ≤ 0) (h7 : b ≤ 0) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_2 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (_h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) (h4 : a ≤ (2 * (k : ℤ) + 3) - 1) (h5 : a + b ≤ (2 * (k : ℤ) + 3)) (h6 : a ≤ 0) (h7 : ¬ (b ≤ 0)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 0 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_3 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (_h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) (h4 : a ≤ (2 * (k : ℤ) + 3) - 1) (h5 : a + b ≤ (2 * (k : ℤ) + 3)) (h6 : ¬ (a ≤ 0)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_4 (k : ℕ) (a b : ℤ) (_hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (_h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) (h4 : a ≤ (2 * (k : ℤ) + 3) - 1) (h5 : ¬ (a + b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  refine square_rule k 1 (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_5 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (_h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) (h4 : ¬ (a ≤ (2 * (k : ℤ) + 3) - 1)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 0 1 (-1) (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_6 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : ¬ (b ≤ (2 * (k : ℤ) + 3) - 1)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_7 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : ¬ (b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 1 0 1 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_8 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : a + b ≤ 1) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 0 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_9 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (_h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : b ≤ (2 * (k : ℤ) + 3) - 1) (h6 : a ≤ 0) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 0 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_10 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (_h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : b ≤ (2 * (k : ℤ) + 3) - 1) (h6 : ¬ (a ≤ 0)) (h7 : a ≤ (2 * (k : ℤ) + 3) - 1) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_11 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (_h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (_h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : b ≤ (2 * (k : ℤ) + 3) - 1) (h6 : ¬ (a ≤ 0)) (h7 : ¬ (a ≤ (2 * (k : ℤ) + 3) - 1)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 0 1 (-1) (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_12 (k : ℕ) (a b : ℤ) (_hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (_h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : ¬ (b ≤ (2 * (k : ℤ) + 3) - 1)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  refine square_rule k 1 (by norm_num) a b 1 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_13 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : ¬ (a + b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 0 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_14 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a + b ≤ 1)) (h3 : ¬ (b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_one_15 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : ¬ (a + b ≤ (2 * (k : ℤ) + 3) + 2)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k 1 (by norm_num) a b 1 1 1 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_1 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : a + b ≤ (2 * (k : ℤ) + 3)) (h4 : a ≤ 0) (h5 : b ≤ 0) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_2 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : a + b ≤ (2 * (k : ℤ) + 3)) (h4 : a ≤ 0) (h5 : ¬ (b ≤ 0)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_3 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : a + b ≤ (2 * (k : ℤ) + 3)) (h4 : ¬ (a ≤ 0)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_4 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : b ≤ (2 * (k : ℤ) + 3)) (h3 : ¬ (a + b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_5 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : (a + b) % 2 = 0) (h2 : ¬ (b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 1 0 1 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_6 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : a ≤ 0) (h3 : b ≤ (2 * (k : ℤ) + 3) - 1) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_7 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (_h1 : ¬ ((a + b) % 2 = 0)) (h2 : a ≤ 0) (h3 : ¬ (b ≤ (2 * (k : ℤ) + 3) - 1)) (h4 : b ≤ (2 * (k : ℤ) + 3)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 1 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_8 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : a ≤ 0) (_h3 : ¬ (b ≤ (2 * (k : ℤ) + 3) - 1)) (h4 : ¬ (b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_9 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a ≤ 0)) (h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : a ≤ (2 * (k : ℤ) + 3) - 2) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_10 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (_h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (_h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a ≤ 0)) (h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : a + b ≤ (2 * (k : ℤ) + 3)) (h5 : ¬ (a ≤ (2 * (k : ℤ) + 3) - 2)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 1 1 1 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_11 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a ≤ 0)) (h3 : b ≤ (2 * (k : ℤ) + 3)) (h4 : ¬ (a + b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 1 1 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_12 (k : ℕ) (a b : ℤ) (_hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2) (_h1 : ¬ ((a + b) % 2 = 0)) (h2 : ¬ (a ≤ 0)) (h3 : ¬ (b ≤ (2 * (k : ℤ) + 3))) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  refine square_rule k (-1) (by norm_num) a b 1 1 1 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem sq_leaf_neg_13 (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) (h0 : ¬ (a + b ≤ (2 * (k : ℤ) + 3) + 2)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  simp only [NativeP, Prod.mk.injEq] at hN
  refine square_rule k (-1) (by norm_num) a b 0 0 0 0 (by norm_num) (by norm_num) ?_ ?_ ?_
  · simp only [NativeP, Prod.mk.injEq]; omega
  · unfold EvenSite; dsimp only; omega
  · rw [combine_mk_one hd]; unfold selDisp squareCorners; split_ifs <;>
      (try simp only [EvenSite, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk_add_mk, not_or, not_and] at *) <;> omega

set_option maxHeartbeats 400000 in
theorem squares_native_one (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) :
    SquareClauseSat (reciprocalField k) (selF k 1) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  by_cases h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2
  ·
    by_cases h1 : (a + b) % 2 = 0
    ·
      by_cases h2 : b ≤ (2 * (k : ℤ) + 3)
      ·
        by_cases h3 : b ≤ (2 * (k : ℤ) + 3) - 1
        ·
          by_cases h4 : a ≤ (2 * (k : ℤ) + 3) - 1
          ·
            by_cases h5 : a + b ≤ (2 * (k : ℤ) + 3)
            ·
              by_cases h6 : a ≤ 0
              ·
                by_cases h7 : b ≤ 0
                ·
                  exact sq_leaf_one_1 k a b hN h0 h1 h2 h3 h4 h5 h6 h7
                ·
                  exact sq_leaf_one_2 k a b hN h0 h1 h2 h3 h4 h5 h6 h7
              ·
                exact sq_leaf_one_3 k a b hN h0 h1 h2 h3 h4 h5 h6
            ·
              exact sq_leaf_one_4 k a b hN h0 h1 h2 h3 h4 h5
          ·
            exact sq_leaf_one_5 k a b hN h0 h1 h2 h3 h4
        ·
          exact sq_leaf_one_6 k a b hN h0 h1 h2 h3
      ·
        exact sq_leaf_one_7 k a b hN h0 h1 h2
    ·
      by_cases h2 : a + b ≤ 1
      ·
        exact sq_leaf_one_8 k a b hN h0 h1 h2
      ·
        by_cases h3 : b ≤ (2 * (k : ℤ) + 3)
        ·
          by_cases h4 : a + b ≤ (2 * (k : ℤ) + 3)
          ·
            by_cases h5 : b ≤ (2 * (k : ℤ) + 3) - 1
            ·
              by_cases h6 : a ≤ 0
              ·
                exact sq_leaf_one_9 k a b hN h0 h1 h2 h3 h4 h5 h6
              ·
                by_cases h7 : a ≤ (2 * (k : ℤ) + 3) - 1
                ·
                  exact sq_leaf_one_10 k a b hN h0 h1 h2 h3 h4 h5 h6 h7
                ·
                  exact sq_leaf_one_11 k a b hN h0 h1 h2 h3 h4 h5 h6 h7
            ·
              exact sq_leaf_one_12 k a b hN h0 h1 h2 h3 h4 h5
          ·
            exact sq_leaf_one_13 k a b hN h0 h1 h2 h3 h4
        ·
          exact sq_leaf_one_14 k a b hN h0 h1 h2 h3
  ·
    exact sq_leaf_one_15 k a b hN h0

set_option maxHeartbeats 400000 in
theorem squares_native_neg (k : ℕ) (a b : ℤ) (hN : NativeP (2 * (k : ℤ) + 3) (a, b)) :
    SquareClauseSat (reciprocalField k) (selF k (-1)) a b := by
  have hd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  by_cases h0 : a + b ≤ (2 * (k : ℤ) + 3) + 2
  ·
    by_cases h1 : (a + b) % 2 = 0
    ·
      by_cases h2 : b ≤ (2 * (k : ℤ) + 3)
      ·
        by_cases h3 : a + b ≤ (2 * (k : ℤ) + 3)
        ·
          by_cases h4 : a ≤ 0
          ·
            by_cases h5 : b ≤ 0
            ·
              exact sq_leaf_neg_1 k a b hN h0 h1 h2 h3 h4 h5
            ·
              exact sq_leaf_neg_2 k a b hN h0 h1 h2 h3 h4 h5
          ·
            exact sq_leaf_neg_3 k a b hN h0 h1 h2 h3 h4
        ·
          exact sq_leaf_neg_4 k a b hN h0 h1 h2 h3
      ·
        exact sq_leaf_neg_5 k a b hN h0 h1 h2
    ·
      by_cases h2 : a ≤ 0
      ·
        by_cases h3 : b ≤ (2 * (k : ℤ) + 3) - 1
        ·
          exact sq_leaf_neg_6 k a b hN h0 h1 h2 h3
        ·
          by_cases h4 : b ≤ (2 * (k : ℤ) + 3)
          ·
            exact sq_leaf_neg_7 k a b hN h0 h1 h2 h3 h4
          ·
            exact sq_leaf_neg_8 k a b hN h0 h1 h2 h3 h4
      ·
        by_cases h3 : b ≤ (2 * (k : ℤ) + 3)
        ·
          by_cases h4 : a + b ≤ (2 * (k : ℤ) + 3)
          ·
            by_cases h5 : a ≤ (2 * (k : ℤ) + 3) - 2
            ·
              exact sq_leaf_neg_9 k a b hN h0 h1 h2 h3 h4 h5
            ·
              exact sq_leaf_neg_10 k a b hN h0 h1 h2 h3 h4 h5
          ·
            exact sq_leaf_neg_11 k a b hN h0 h1 h2 h3 h4
        ·
          exact sq_leaf_neg_12 k a b hN h0 h1 h2 h3
  ·
    exact sq_leaf_neg_13 k a b hN h0

/-- The unit square clauses of the signed policy e(-1, eta) on the reciprocal field at every square. -/
theorem squares_reciprocal (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (a b : ℤ) :
    SquareClauseSat (reciprocalField k) (selF k η) a b := by
  have hnat : ∀ a' b' : ℤ, NativeP (2 * (k : ℤ) + 3) (a', b') → SquareClauseSat (reciprocalField k) (selF k η) a' b' := by
    rcases hη with rfl | rfl
    · exact fun a' b' hN => squares_native_one k a' b' hN
    · exact fun a' b' hN => squares_native_neg k a' b' hN
  exact squareClause_all k η hη hnat a b

end FLatticePaper.EPolicy
