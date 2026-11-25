import FLatticePaper.Tiles.WalkCover
import FLatticePaper.Tiles.RegionBoundary
import FLatticePaper.Tiles.FourWalks

/-! Task Q25 (completeness of the seam), the lines of a walk: how many edges of a walk cross each column and each row.

For words `w1` (letters `one`, `i`) and `w2` (letters `i`, `negOne`) the walk `V = edgesFrom 0 (w1 ++ w2)` has its east starts at the
columns `0, …, n1 − 1` (`n1` the number of `one` letters of `w1`), its west starts at the columns `z1.1 − j` for `j < n2` (`n2` the number
of `negOne` letters of `w2`), its north starts at the rows `0, …, ni − 1` (`ni` the number of `i` letters). The four classes of the
walk `W = V ++ V.map (halfE z)` of `boundaryWordOf w1 w2` then meet each column of `[−n2, n1 − 1]` once in each of the east and
west kinds, and each row of `[0, ni − 1]` once in each of the north and south kinds (`lines_of_walk`). -/

namespace FLatticePaper.Tiles.WalkLines

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.WalkCover FLatticePaper.Tiles.FourWalks

/-- The east start predicate of a column `x`. -/
def Ep (x : ℤ) (g : GInt × GInt) : Bool := decide (g.2 = g.1 + gOne) && decide (g.1.1 = x)

/-- The west start predicate of a column `u`. -/
def Wp (u : ℤ) (g : GInt × GInt) : Bool := decide (g.2 = g.1 - gOne) && decide (g.1.1 = u)

/-- The north start predicate of a row `y`. -/
def Np (y : ℤ) (g : GInt × GInt) : Bool := decide (g.2 = g.1 + gI) && decide (g.1.2 = y)

theorem vec_one_eq' : Unit4.vec Unit4.one = gOne := rfl

theorem vec_i_eq' : Unit4.vec Unit4.i = gI := rfl

theorem vec_negOne_eq' : Unit4.vec Unit4.negOne = -gOne := rfl

theorem vec_negI_eq' : Unit4.vec Unit4.negI = -gI := rfl

theorem count_one_cons_one (u : F2Word) : List.count Unit4.one (Unit4.one :: u) = List.count Unit4.one u + 1 := by
  simp

theorem count_one_cons_i (u : F2Word) : List.count Unit4.one (Unit4.i :: u) = List.count Unit4.one u := by
  simp

theorem Ep_head_one (c : GInt) (v : ℤ) : Ep v (c, c + gOne) = decide (c.1 = v) := by
  simp [Ep]

theorem Ep_head_i (c : GInt) (v : ℤ) : Ep v (c, c + gI) = false := by
  have hne : decide (c + gI = c + gOne) = false := by
    apply decide_eq_false
    intro h
    have := congrArg Prod.fst h
    simp [gI, gOne] at this
  simp only [Ep, hne, Bool.false_and]

/-- The east starts of a walk on `one` and `i` letters: the columns `c.1, …, c.1 + n − 1`, each once. -/
theorem Ep_edgesFrom (u : F2Word) (hu : ∀ z ∈ u, z = .one ∨ z = .i) (c : GInt) (v : ℤ) :
    (edgesFrom c u).countP (Ep v) = if c.1 ≤ v ∧ v < c.1 + (List.count Unit4.one u : ℤ) then 1 else 0 := by
  induction u generalizing c with
  | nil => simp [edgesFrom]
  | cons z u ih =>
    have hz : z = .one ∨ z = .i := hu z (by simp)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (by simp [hy])
    rcases hz with rfl | rfl
    · have hrest := ih hu' (c + gOne)
      have e1 : (c + gOne).1 = c.1 + 1 := by simp [gOne]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.one :: u) = (c, c + Unit4.vec Unit4.one) :: edgesFrom (c + Unit4.vec Unit4.one) u
        from rfl, List.countP_cons, vec_one_eq', hrest, Ep_head_one, count_one_cons_one]
      simp only [decide_eq_true_eq]
      push_cast
      split_ifs <;> omega
    · have hrest := ih hu' (c + gI)
      have e1 : (c + gI).1 = c.1 := by simp [gI]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.i :: u) = (c, c + Unit4.vec Unit4.i) :: edgesFrom (c + Unit4.vec Unit4.i) u
        from rfl, List.countP_cons, vec_i_eq', hrest, Ep_head_i, count_one_cons_i]
      simp

theorem count_negOne_cons_negOne (u : F2Word) :
    List.count Unit4.negOne (Unit4.negOne :: u) = List.count Unit4.negOne u + 1 := by
  simp

theorem count_negOne_cons_i (u : F2Word) :
    List.count Unit4.negOne (Unit4.i :: u) = List.count Unit4.negOne u := by
  simp

theorem count_i_cons_i (u : F2Word) : List.count Unit4.i (Unit4.i :: u) = List.count Unit4.i u + 1 := by
  simp

theorem count_i_cons_one (u : F2Word) : List.count Unit4.i (Unit4.one :: u) = List.count Unit4.i u := by
  simp

theorem count_i_cons_negOne (u : F2Word) : List.count Unit4.i (Unit4.negOne :: u) = List.count Unit4.i u := by
  simp

theorem neq_of_fst {a b : GInt} (h : a.1 ≠ b.1) : a ≠ b := fun e => h (congrArg Prod.fst e)

/-- The west start predicate is false on the edge `(c, c + gI)`. -/
theorem Wp_head_i (c : GInt) (v : ℤ) : Wp v (c, c + gI) = false := by
  have hne : decide (c + gI = c - gOne) = false := by
    apply decide_eq_false
    apply neq_of_fst
    simp [gI, gOne]
    omega
  simp only [Wp, hne, Bool.false_and]

theorem Wp_head_negOne (c : GInt) (v : ℤ) : Wp v (c, c + Unit4.vec Unit4.negOne) = decide (c.1 = v) := by
  have e : c + Unit4.vec Unit4.negOne = c - gOne := by
    rw [vec_negOne_eq', sub_eq_add_neg]
  rw [e]
  simp [Wp]

/-- The west starts of a walk on `i` and `negOne` letters: the columns `c.1 − j` for `j < n`, each once. -/
theorem Wp_edgesFrom (u : F2Word) (hu : ∀ z ∈ u, z = .i ∨ z = .negOne) (c : GInt) (v : ℤ) :
    (edgesFrom c u).countP (Wp v) =
      if c.1 - (List.count Unit4.negOne u : ℤ) < v ∧ v ≤ c.1 then 1 else 0 := by
  induction u generalizing c with
  | nil =>
    simp only [edgesFrom, List.countP_nil, List.count_nil]
    split_ifs <;> omega
  | cons z u ih =>
    have hz : z = .i ∨ z = .negOne := hu z (by simp)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (by simp [hy])
    rcases hz with rfl | rfl
    · have hrest := ih hu' (c + gI)
      have e1 : (c + gI).1 = c.1 := by simp [gI]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.i :: u) = (c, c + Unit4.vec Unit4.i) :: edgesFrom (c + Unit4.vec Unit4.i) u
        from rfl, List.countP_cons, vec_i_eq', hrest, Wp_head_i, count_negOne_cons_i]
      simp
    · have hrest := ih hu' (c + Unit4.vec Unit4.negOne)
      have e1 : (c + Unit4.vec Unit4.negOne).1 = c.1 - 1 := by
        rw [vec_negOne_eq']
        simp [gOne]
        omega
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.negOne :: u) = (c, c + Unit4.vec Unit4.negOne) ::
          edgesFrom (c + Unit4.vec Unit4.negOne) u from rfl, List.countP_cons, Wp_head_negOne, hrest,
        count_negOne_cons_negOne]
      simp only [decide_eq_true_eq]
      push_cast
      split_ifs <;> omega

/-- The north starts of a walk without `negI` letters: the rows `c.2, …, c.2 + n − 1`, each once. -/
theorem Np_edgesFrom (u : F2Word) (hu : ∀ z ∈ u, z ≠ .negI) (c : GInt) (v : ℤ) :
    (edgesFrom c u).countP (Np v) = if c.2 ≤ v ∧ v < c.2 + (List.count Unit4.i u : ℤ) then 1 else 0 := by
  induction u generalizing c with
  | nil =>
    simp only [edgesFrom, List.countP_nil, List.count_nil]
    split_ifs <;> omega
  | cons z u ih =>
    have hz : z ≠ .negI := hu z (by simp)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (by simp [hy])
    rcases (show z = .one ∨ z = .i ∨ z = .negOne by cases z <;> simp_all) with rfl | rfl | rfl
    · have hrest := ih hu' (c + gOne)
      have e1 : (c + gOne).2 = c.2 := by simp [gOne]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.one :: u) = (c, c + Unit4.vec Unit4.one) :: edgesFrom (c + Unit4.vec Unit4.one) u
        from rfl, List.countP_cons, vec_one_eq', hrest, count_i_cons_one]
      have hne : decide (c + gOne = c + gI) = false := by
        apply decide_eq_false
        apply neq_of_fst
        simp [gI, gOne]
      have h0 : Np v (c, c + gOne) = false := by
        simp only [Np, hne, Bool.false_and]
      simp [h0]
    · have hrest := ih hu' (c + gI)
      have e1 : (c + gI).2 = c.2 + 1 := by simp [gI]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.i :: u) = (c, c + Unit4.vec Unit4.i) :: edgesFrom (c + Unit4.vec Unit4.i) u
        from rfl, List.countP_cons, vec_i_eq', hrest, count_i_cons_i]
      have hh : Np v (c, c + gI) = decide (c.2 = v) := by
        simp [Np]
      rw [hh]
      simp only [decide_eq_true_eq]
      push_cast
      split_ifs <;> omega
    · have hrest := ih hu' (c + Unit4.vec Unit4.negOne)
      have e1 : (c + Unit4.vec Unit4.negOne).2 = c.2 := by
        rw [vec_negOne_eq']
        simp [gOne]
      rw [e1] at hrest
      rw [show edgesFrom c (Unit4.negOne :: u) = (c, c + Unit4.vec Unit4.negOne) ::
          edgesFrom (c + Unit4.vec Unit4.negOne) u from rfl, List.countP_cons, hrest, count_i_cons_negOne]
      have hne : decide (c + Unit4.vec Unit4.negOne = c + gI) = false := by
        apply decide_eq_false
        apply neq_of_fst
        rw [vec_negOne_eq']
        simp [gI, gOne]
      have h0 : Np v (c, c + Unit4.vec Unit4.negOne) = false := by
        simp only [Np, hne, Bool.false_and]
      simp [h0]

/-- A walk without `one` letters has no east starts. -/
theorem Ep_zero (u : F2Word) (hu : ∀ z ∈ u, z ≠ .one) (c : GInt) (v : ℤ) :
    (edgesFrom c u).countP (Ep v) = 0 := by
  induction u generalizing c with
  | nil => simp [edgesFrom]
  | cons z u ih =>
    have hz : z ≠ .one := hu z (by simp)
    have hu' : ∀ y ∈ u, y ≠ .one := fun y hy => hu y (by simp [hy])
    have hne : decide (c + Unit4.vec z = c + gOne) = false := by
      apply decide_eq_false
      apply neq_of_fst
      cases z <;> simp_all [gOne, Unit4.vec]
    have hfalse : Ep v (c, c + Unit4.vec z) = false := by
      simp only [Ep, hne, Bool.false_and]
    rw [show edgesFrom c (z :: u) = (c, c + Unit4.vec z) :: edgesFrom (c + Unit4.vec z) u from rfl,
      List.countP_cons, hfalse, ih hu']
    simp

/-- A walk without `negOne` letters has no west starts. -/
theorem Wp_zero (u : F2Word) (hu : ∀ z ∈ u, z ≠ .negOne) (c : GInt) (v : ℤ) :
    (edgesFrom c u).countP (Wp v) = 0 := by
  induction u generalizing c with
  | nil => simp [edgesFrom]
  | cons z u ih =>
    have hz : z ≠ .negOne := hu z (by simp)
    have hu' : ∀ y ∈ u, y ≠ .negOne := fun y hy => hu y (by simp [hy])
    have hne : decide (c + Unit4.vec z = c - gOne) = false := by
      apply decide_eq_false
      apply neq_of_fst
      cases z <;> simp_all [gOne, Unit4.vec] <;> omega
    have hfalse : Wp v (c, c + Unit4.vec z) = false := by
      simp only [Wp, hne, Bool.false_and]
    rw [show edgesFrom c (z :: u) = (c, c + Unit4.vec z) :: edgesFrom (c + Unit4.vec z) u from rfl,
      List.countP_cons, hfalse, ih hu']
    simp

/-- The x-coordinate of the sum of a word: the count of `one` minus the count of `negOne`. -/
theorem sum_fst (w : F2Word) (hw : ∀ z ∈ w, z ≠ .negI) :
    (F2Word.sum w).1 = (List.count Unit4.one w : ℤ) - List.count Unit4.negOne w := by
  induction w with
  | nil => simp [F2Word.sum]
  | cons z w ih =>
    have hz : z ≠ .negI := hw z (by simp)
    have hw' : ∀ y ∈ w, y ≠ .negI := fun y hy => hw y (by simp [hy])
    have ih' := ih hw'
    unfold F2Word.sum at ih' ⊢
    rw [List.map_cons, List.sum_cons]
    rcases (show z = .one ∨ z = .i ∨ z = .negOne by cases z <;> simp_all) with rfl | rfl | rfl
    · simp [Unit4.vec] at ih' ⊢
      omega
    · simp [Unit4.vec] at ih' ⊢
      omega
    · simp [Unit4.vec] at ih' ⊢
      omega

/-- The y-coordinate of the sum of a word: the count of `i`. -/
theorem sum_snd (w : F2Word) (hw : ∀ z ∈ w, z ≠ .negI) :
    (F2Word.sum w).2 = (List.count Unit4.i w : ℤ) := by
  induction w with
  | nil => simp [F2Word.sum]
  | cons z w ih =>
    have hz : z ≠ .negI := hw z (by simp)
    have hw' : ∀ y ∈ w, y ≠ .negI := fun y hy => hw y (by simp [hy])
    have ih' := ih hw'
    unfold F2Word.sum at ih' ⊢
    rw [List.map_cons, List.sum_cons]
    rcases (show z = .one ∨ z = .i ∨ z = .negOne by cases z <;> simp_all) with rfl | rfl | rfl
    · simp [Unit4.vec] at ih' ⊢
      omega
    · simp [Unit4.vec] at ih' ⊢
      omega
    · simp [Unit4.vec] at ih' ⊢
      omega

/-! ### The half-turn and the four kinds of starts -/

/-- The west end predicate of a column `x` (the cell column of a west edge). -/
def WE (x : ℤ) (g : GInt × GInt) : Bool := decide (g.2 = g.1 - gOne) && decide (g.2.1 = x)

/-- The south end predicate of a row `y` (the cell row of a south edge). -/
def SE (y : ℤ) (g : GInt × GInt) : Bool := decide (g.2 = g.1 - gI) && decide (g.2.2 = y)

theorem neq_of_snd {a b : GInt} (h : a.2 ≠ b.2) : a ≠ b := fun e => h (congrArg Prod.snd e)

/-- A half-turn sends the west edges of `V` to the east edges, at the mirrored column. -/
theorem Ep_halfE (z : GInt) (x : ℤ) (g : GInt × GInt) : Ep x (halfE z g) = Wp (z.1 - x) g := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨z1, z2⟩ := z
  simp only [Ep, Wp, halfE, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

/-- A half-turn sends the east edges of `V` to the west edges, at the mirrored end column. -/
theorem WE_halfE (z : GInt) (x : ℤ) (g : GInt × GInt) : WE x (halfE z g) = Ep (z.1 - 1 - x) g := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨z1, z2⟩ := z
  simp only [WE, Ep, halfE, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gOne]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

/-- The west end predicate equals the west start predicate one column further, pointwise. -/
theorem WE_eq_Wp (x : ℤ) (g : GInt × GInt) : WE x g = Wp (x + 1) g := by
  obtain ⟨g1, g2⟩ := g
  simp only [WE, Wp, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, gOne]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

/-- The west end predicate equals the west start predicate one column further, as functions. -/
theorem WE_eq_Wp' (x : ℤ) : WE x = Wp (x + 1) := funext (fun g => WE_eq_Wp x g)

/-- The south end predicate of a half-turn is the north start predicate at the mirrored row. -/
theorem SE_halfE (z : GInt) (y : ℤ) (g : GInt × GInt) : SE y (halfE z g) = Np (z.2 - 1 - y) g := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨z1, z2⟩ := z
  simp only [SE, Np, halfE, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, gI]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

/-- A walk without `negI` letters has no south edges `(c, c − N)`. -/
theorem S_zero (u : F2Word) (hu : ∀ z ∈ u, z ≠ .negI) (c : GInt) :
    (edgesFrom c u).countP (fun g => decide (g.2 = g.1 - gI)) = 0 := by
  induction u generalizing c with
  | nil => simp [edgesFrom]
  | cons z u ih =>
    have hz : z ≠ .negI := hu z (by simp)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (by simp [hy])
    have hfalse : decide ((c, c + Unit4.vec z).2 = (c, c + Unit4.vec z).1 - gI) = false := by
      apply decide_eq_false
      rcases (show z = .one ∨ z = .i ∨ z = .negOne by cases z <;> simp_all) with rfl | rfl | rfl
      · apply neq_of_fst
        simp [Unit4.vec, gI]
      · apply neq_of_snd
        simp [Unit4.vec, gI]
        omega
      · apply neq_of_fst
        simp [Unit4.vec, gI]
    rw [show edgesFrom c (z :: u) = (c, c + Unit4.vec z) :: edgesFrom (c + Unit4.vec z) u from rfl,
      List.countP_cons, hfalse, ih hu']
    simp

/-! ### The starts of the walk `V = edgesFrom (0,0) (w1 ++ w2)` -/

theorem hu_no_one (w2 : F2Word) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) : ∀ z ∈ w2, z ≠ .one := by
  intro z hz h
  rcases hw2 z hz with h' | h' <;> simp_all

theorem hu_no_negOne (w1 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) : ∀ z ∈ w1, z ≠ .negOne := by
  intro z hz h
  rcases hw1 z hz with h' | h' <;> simp_all

theorem hn_no_negI (w : F2Word) (hw : ∀ z ∈ w, z = .one ∨ z = .i ∨ z = .negOne) : ∀ z ∈ w, z ≠ .negI := by
  intro z hz h
  rcases hw z hz with h' | h' | h' <;> simp_all

theorem sum_first (w : F2Word) (hw : ∀ z ∈ w, z = .one ∨ z = .i) : (F2Word.sum w).1 = (List.count Unit4.one w : ℤ) := by
  rw [sum_fst w (hn_no_negI w (fun z hz => by rcases hw z hz with h | h <;> simp [h]))]
  have : List.count Unit4.negOne w = 0 := List.count_eq_zero.mpr (fun hm => by
    rcases hw _ hm with h | h <;> simp_all)
  simp [this]

theorem Ep_V (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) (x : ℤ) :
    (edgesFrom (0, 0) (w1 ++ w2)).countP (Ep x) = if 0 ≤ x ∧ x < (List.count Unit4.one w1 : ℤ) then 1 else 0 := by
  rw [edgesFrom_append, List.countP_append, Ep_edgesFrom w1 hw1, Ep_zero w2 (hu_no_one w2 hw2)]
  simp

theorem Wp_V (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) (u : ℤ) :
    (edgesFrom (0, 0) (w1 ++ w2)).countP (Wp u) =
      if (List.count Unit4.one w1 : ℤ) - List.count Unit4.negOne w2 < u ∧ u ≤ (List.count Unit4.one w1 : ℤ) then 1 else 0 := by
  rw [edgesFrom_append, List.countP_append, Wp_zero w1 (hu_no_negOne w1 hw1), Wp_edgesFrom w2 hw2]
  have hs : ((0, 0) + F2Word.sum w1 : GInt).1 = (List.count Unit4.one w1 : ℤ) := by
    rw [Prod.fst_add]
    simp only [zero_add]
    exact sum_first w1 hw1
  rw [hs, zero_add]

theorem Np_V (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) (y : ℤ) :
    (edgesFrom (0, 0) (w1 ++ w2)).countP (Np y) =
      (if 0 ≤ y ∧ y < (List.count Unit4.i w1 : ℤ) then 1 else 0) +
        (if (List.count Unit4.i w1 : ℤ) ≤ y ∧ y < (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 then 1 else 0) := by
  have hn1 : ∀ z ∈ w1, z ≠ .negI := hn_no_negI w1 (fun z hz => by rcases hw1 z hz with h | h <;> simp [h])
  have hn2 : ∀ z ∈ w2, z ≠ .negI := hn_no_negI w2 (fun z hz => by rcases hw2 z hz with h | h <;> simp [h])
  rw [edgesFrom_append, List.countP_append, Np_edgesFrom w1 hn1 (0, 0), Np_edgesFrom w2 hn2 ((0, 0) + F2Word.sum w1)]
  have hs : ((0, 0) + F2Word.sum w1 : GInt).2 = (List.count Unit4.i w1 : ℤ) := by
    rw [Prod.snd_add]
    simp only [zero_add]
    exact sum_snd w1 hn1
  rw [hs]
  simp

theorem S_V (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) :
    (edgesFrom (0, 0) (w1 ++ w2)).countP (fun g => decide (g.2 = g.1 - gI)) = 0 := by
  have hn1 : ∀ z ∈ w1, z ≠ .negI := hn_no_negI w1 (fun z hz => by rcases hw1 z hz with h | h <;> simp [h])
  have hn2 : ∀ z ∈ w2, z ≠ .negI := hn_no_negI w2 (fun z hz => by rcases hw2 z hz with h | h <;> simp [h])
  rw [edgesFrom_append, List.countP_append, S_zero w1 hn1 (0, 0), S_zero w2 hn2]

/-- A half-turn of a south edge is not a north start: a north start of the half-turn is a south edge of the walk. -/
theorem Np_halfE_S (z : GInt) (y : ℤ) (g : GInt × GInt) (h : Np y (halfE z g) = true) :
    decide (g.2 = g.1 - gI) = true := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨z1, z2⟩ := z
  simp only [Np, halfE, Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, gI] at h ⊢
  omega

/-! ### The four line counts of the boundary walk -/

theorem sum_z (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) :
    (F2Word.sum (w1 ++ w2)).1 = (List.count Unit4.one w1 : ℤ) - List.count Unit4.negOne w2 ∧
      (F2Word.sum (w1 ++ w2)).2 = (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 := by
  have hn2 : ∀ z ∈ w2, z ≠ .negI := hn_no_negI w2 (fun z hz => by rcases hw2 z hz with h | h <;> simp [h])
  have hn1 : ∀ z ∈ w1, z ≠ .negI := hn_no_negI w1 (fun z hz => by rcases hw1 z hz with h | h <;> simp [h])
  have hone2 : List.count Unit4.one w2 = 0 := List.count_eq_zero.mpr (fun hm => by
    rcases hw2 _ hm with h | h <;> simp_all)
  rw [sum_append']
  constructor
  · rw [Prod.fst_add, sum_first w1 hw1, sum_fst w2 hn2, hone2]
    push_cast
    ring
  · rw [Prod.snd_add, sum_snd w1 hn1, sum_snd w2 hn2]

theorem lines_of_walk (w1 w2 : F2Word) (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne) :
    (∀ x : ℤ, WalkCover.cntE (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x =
        (if 0 ≤ x ∧ x < (List.count Unit4.one w1 : ℤ) then 1 else 0) +
          (if -(List.count Unit4.negOne w2 : ℤ) ≤ x ∧ x < 0 then 1 else 0)) ∧
    (∀ x : ℤ, WalkCover.cntW (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x =
        if -(List.count Unit4.negOne w2 : ℤ) ≤ x ∧ x < (List.count Unit4.one w1 : ℤ) then 1 else 0) ∧
    (∀ y : ℤ, WalkCover.cntN (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y =
        if 0 ≤ y ∧ y < (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 then 1 else 0) ∧
    (∀ y : ℤ, WalkCover.cntS (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y =
        if 0 ≤ y ∧ y < (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 then 1 else 0) := by
  obtain ⟨hz1, hz2⟩ := sum_z w1 w2 hw1 hw2
  rw [RegionBoundary.walk_split]
  refine ⟨fun x => ?_, fun x => ?_, fun y => ?_, fun y => ?_⟩
  · unfold WalkCover.cntE
    show List.countP (Ep x) _ = _
    rw [List.countP_append, List.countP_map]
    simp only [Function.comp_def, Ep_halfE]
    rw [Ep_V w1 w2 hw1 hw2 x, Wp_V w1 w2 hw1 hw2, hz1]
    split_ifs <;> omega
  · unfold WalkCover.cntW
    show List.countP (WE x) _ = _
    rw [List.countP_append, List.countP_map]
    simp only [Function.comp_def, WE_halfE]
    rw [WE_eq_Wp', Wp_V w1 w2 hw1 hw2, Ep_V w1 w2 hw1 hw2, hz1]
    split_ifs <;> omega
  · unfold WalkCover.cntN
    show List.countP (Np y) _ = _
    rw [List.countP_append, List.countP_map]
    have hS0 : List.countP (Np y ∘ halfE (F2Word.sum (w1 ++ w2)))
        (edgesFrom (0, 0) (w1 ++ w2)) = 0 := by
      have hle := List.countP_mono_left (p := Np y ∘ halfE (F2Word.sum (w1 ++ w2)))
        (q := fun g => decide (g.2 = g.1 - gI)) (l := edgesFrom (0, 0) (w1 ++ w2))
        (fun g _ hg => Np_halfE_S (F2Word.sum (w1 ++ w2)) y g hg)
      rw [S_V w1 w2 hw1 hw2] at hle
      omega
    rw [hS0, add_zero, Np_V w1 w2 hw1 hw2 y]
    split_ifs <;> omega
  · unfold WalkCover.cntS
    show List.countP (SE y) _ = _
    rw [List.countP_append, List.countP_map]
    have hS0 : List.countP (SE y) (edgesFrom (0, 0) (w1 ++ w2)) = 0 := by
      have hle := List.countP_mono_left (p := SE y) (q := fun g => decide (g.2 = g.1 - gI))
        (l := edgesFrom (0, 0) (w1 ++ w2)) (fun g _ hg => by
          simp only [SE, Bool.and_eq_true] at hg
          exact hg.1)
      rw [S_V w1 w2 hw1 hw2] at hle
      omega
    simp only [Function.comp_def, SE_halfE]
    rw [hS0, zero_add, Np_V w1 w2 hw1 hw2, hz2]
    split_ifs <;> omega

end FLatticePaper.Tiles.WalkLines
