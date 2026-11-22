import FLatticePaper.Tiles.AlmostTiling

/-! Task 32, part 1: the directed edges of a walk in `F_2`, and how they behave under concatenation, translation, reversal
and the inverse `hat`. For the boundary word `w₁ * w₂ * ŵ₁ * ŵ₂` of `prop:tiling_criteria` the edge list splits into four
pieces, two of them translates of the walks of `w₁`, `w₂` and two of them reversed translates. This is the algebraic core of
the tiling argument (the cancellation of the boundary edges of the translates in pairs). -/

namespace FLatticePaper.Tiles

/-- The directed edges of the walk of `w` from `c`: consecutive pairs of its vertices (the boundary edges of
`IsBoundaryWordAt` are exactly these pairs). -/
def F2Word.edges (c : GInt) (w : F2Word) : List (GInt × GInt) :=
  (F2Word.walk c w).zip (F2Word.walk c w).tail

/-- Translation of a directed edge by `d`. -/
def edgeShift (d : GInt) (e : GInt × GInt) : GInt × GInt := (e.1 + d, e.2 + d)

/-- Reversal of a directed edge. -/
def edgeRev (e : GInt × GInt) : GInt × GInt := (e.2, e.1)

theorem F2Word.walk_cons (c : GInt) (a : Unit4) (u : F2Word) :
    F2Word.walk c (a :: u) = c :: F2Word.walk (c + a.vec) u := by
  simp [F2Word.walk]

theorem F2Word.walk_head (d : GInt) (u : F2Word) : ∃ t, F2Word.walk d u = d :: t := by
  cases u with
  | nil => exact ⟨[], by simp [F2Word.walk]⟩
  | cons a u => exact ⟨_, F2Word.walk_cons d a u⟩

theorem F2Word.sum_cons (a : Unit4) (u : F2Word) :
    F2Word.sum (a :: u) = a.vec + F2Word.sum u := by
  simp [F2Word.sum]

theorem F2Word.sum_append (u v : F2Word) : F2Word.sum (u ++ v) = F2Word.sum u + F2Word.sum v := by
  simp [F2Word.sum, List.map_append, List.sum_append]

theorem F2Word.edges_nil (c : GInt) : F2Word.edges c [] = [] := by
  simp [F2Word.edges, F2Word.walk]

theorem F2Word.edges_cons (c : GInt) (a : Unit4) (u : F2Word) :
    F2Word.edges c (a :: u) = (c, c + a.vec) :: F2Word.edges (c + a.vec) u := by
  obtain ⟨t, ht⟩ := F2Word.walk_head (c + a.vec) u
  unfold F2Word.edges
  rw [F2Word.walk_cons, ht]
  simp

theorem F2Word.edges_single (d : GInt) (b : Unit4) : F2Word.edges d [b] = [(d, d + b.vec)] := by
  rw [F2Word.edges_cons, F2Word.edges_nil]

/-- Concatenation: the edges of `u ++ v` are those of `u`, then those of `v` translated by the sum of `u`. -/
theorem F2Word.edges_append (c : GInt) (u v : F2Word) :
    F2Word.edges c (u ++ v) = F2Word.edges c u ++ F2Word.edges (c + F2Word.sum u) v := by
  induction u generalizing c with
  | nil => simp [F2Word.edges_nil, F2Word.sum]
  | cons a u ih =>
    rw [List.cons_append, F2Word.edges_cons, ih, F2Word.edges_cons, F2Word.sum_cons, List.cons_append]
    simp only [add_assoc]

/-- Translation: the edges of the walk from `c + d` are the edges from `c`, translated by `d`. -/
theorem F2Word.edges_shift (c d : GInt) (u : F2Word) :
    F2Word.edges (c + d) u = (F2Word.edges c u).map (edgeShift d) := by
  induction u generalizing c with
  | nil => simp [F2Word.edges_nil]
  | cons a u ih =>
    rw [F2Word.edges_cons, F2Word.edges_cons, List.map_cons,
      show c + d + a.vec = (c + a.vec) + d by abel, ih]
    simp [edgeShift]

theorem F2Word.sum_hat_cons (a : Unit4) (u : F2Word) :
    F2Word.hat (a :: u) = F2Word.hat u ++ [a.neg] := by
  simp [F2Word.hat, List.reverse_cons]

theorem Unit4.vec_neg (a : Unit4) : a.neg.vec = -a.vec := by
  cases a <;> simp [Unit4.neg, Unit4.vec]

theorem F2Word.sum_hat (u : F2Word) : F2Word.sum (F2Word.hat u) = -F2Word.sum u := by
  induction u with
  | nil => simp [F2Word.sum, F2Word.hat]
  | cons a u ih =>
    rw [F2Word.sum_hat_cons, F2Word.sum_append, ih, F2Word.sum_cons]
    simp only [F2Word.sum, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at *
    rw [Unit4.vec_neg]
    abel

/-- Inverse: the edges of `ŵ` from `c` are the reversed, reflected edges of `w` from `c - Σw`. -/
theorem F2Word.edges_hat (c : GInt) (u : F2Word) :
    F2Word.edges c (F2Word.hat u) =
      ((F2Word.edges (c - F2Word.sum u) u).reverse).map edgeRev := by
  induction u generalizing c with
  | nil => simp [F2Word.edges_nil, F2Word.hat, F2Word.sum]
  | cons a u ih =>
    rw [F2Word.sum_hat_cons, F2Word.edges_append, F2Word.edges_single, ih, F2Word.sum_hat,
      F2Word.sum_cons, F2Word.edges_cons]
    have hd : c - (a.vec + F2Word.sum u) + a.vec = c - F2Word.sum u := by abel
    rw [hd, List.reverse_cons, List.map_append]
    simp only [List.map_cons, List.map_nil, edgeRev, Unit4.vec_neg]
    abel_nf

/-- The edges of the boundary word `w₁ * w₂ * ŵ₁ * ŵ₂` from `c`: four pieces, the walks of `w₁` and `w₂`, and the
reversed walks of `w₁` and `w₂` translated by the lattice vectors `Σw₂` and `Σw₁`. -/
theorem F2Word.edges_boundary (c : GInt) (w₁ w₂ : F2Word) :
    F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂) =
      F2Word.edges c w₁ ++ (F2Word.edges c w₂).map (edgeShift (F2Word.sum w₁)) ++
        ((F2Word.edges c w₁).map (edgeShift (F2Word.sum w₂))).reverse.map edgeRev ++
        (F2Word.edges c w₂).reverse.map edgeRev := by
  rw [F2Word.edges_append, F2Word.edges_append, F2Word.edges_append, F2Word.edges_hat, F2Word.edges_hat]
  have hb1 : c + F2Word.sum (w₁ ++ w₂) - F2Word.sum w₁ = c + F2Word.sum w₂ := by
    rw [F2Word.sum_append]; abel
  have hb2 : c + F2Word.sum (w₁ ++ w₂ ++ F2Word.hat w₁) - F2Word.sum w₂ = c := by
    simp only [F2Word.sum_append, F2Word.sum_hat]; abel
  rw [hb1, hb2]
  simp only [F2Word.edges_shift, List.append_assoc]

/-- The shoelace form of a directed edge: twice the contribution `x dy` of the edge (real part times imaginary
increment, symmetrized). -/
def omegaE (e : GInt × GInt) : ℤ := (e.1.1 + e.2.1) * (e.2.2 - e.1.2)

/-- The vertical increment of a directed edge. -/
def dyE (e : GInt × GInt) : ℤ := e.2.2 - e.1.2

theorem omegaE_rev (e : GInt × GInt) : omegaE (edgeRev e) = -omegaE e := by
  simp only [omegaE, edgeRev]; ring

theorem omegaE_shift (d : GInt) (e : GInt × GInt) :
    omegaE (edgeShift d e) = omegaE e + 2 * d.1 * dyE e := by
  simp only [omegaE, dyE, edgeShift, Prod.fst_add, Prod.snd_add]; ring

theorem F2Word.dy_sum (c : GInt) (u : F2Word) :
    ((F2Word.edges c u).map dyE).sum = (c + F2Word.sum u).2 - c.2 := by
  induction u generalizing c with
  | nil => simp [F2Word.edges_nil, F2Word.sum]
  | cons a u ih =>
    rw [F2Word.edges_cons, List.map_cons, List.sum_cons, ih, F2Word.sum_cons]
    simp only [dyE, add_assoc, Prod.snd_add]
    ring

theorem omega_sum_shift (X : List (GInt × GInt)) (d : GInt) :
    ((X.map (edgeShift d)).map omegaE).sum = (X.map omegaE).sum + 2 * d.1 * (X.map dyE).sum := by
  induction X with
  | nil => simp
  | cons e X ih => simp only [List.map_cons, List.sum_cons, omegaE_shift, ih]; ring

theorem omega_sum_reverse (Y : List (GInt × GInt)) :
    ((Y.reverse.map edgeRev).map omegaE).sum = -(Y.map omegaE).sum := by
  induction Y with
  | nil => simp
  | cons y Y ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, omegaE_rev] at ih ⊢
    rw [ih]; ring

/-- The determinant of two Gaussian integers `g₁ = (a, b)`, `g₂ = (c, d)`: `ad - bc`. -/
def detG (g₁ g₂ : GInt) : ℤ := g₁.1 * g₂.2 - g₁.2 * g₂.1

/-- The shoelace sum of the boundary word: twice the determinant of `(Σw₁, Σw₂)`. -/
theorem omega_sum_boundary (c : GInt) (w₁ w₂ : F2Word) :
    ((F2Word.edges c (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)).map omegaE).sum =
      2 * detG (F2Word.sum w₁) (F2Word.sum w₂) := by
  rw [F2Word.edges_boundary]
  simp only [List.map_append, List.sum_append, omega_sum_reverse, omega_sum_shift, F2Word.dy_sum]
  simp only [Prod.snd_add, detG]
  ring

end FLatticePaper.Tiles
