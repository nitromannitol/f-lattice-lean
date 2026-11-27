import FLatticePaper.Tiles.Gluing

/-! # Closed paths around the unit squares (`lemma:common-extension-pseudo-square`, item (ii))

The overlap graph of the translates `T_{i,j}` of a tile is a graph on `ℤ²`. Its walks have offset sums that vanish
once two conditions hold: every step is a unit step of `ℤ²`, the offsets are antisymmetric, and the offset sum around each
unit square `(i,j), (i+1,j), (i+1,j+1), (i,j+1)` is zero. Then the offsets are the increments of a potential, and every
closed walk sums to zero. The square condition is the one checked in the proof of the lemma (`a_{n/d,1} = 0`,
`a_{n/d,2} ⟂ v_{n/d,1}`, see `square_algebra`); the statement that overlaps are unit steps is a geometric input. -/

namespace FLatticePaper.Tiles

open SimpleGraph

/-- The integer sum of `f` over `[0, n)` for `n ≥ 0` and minus the sum over `[n, 0)` for `n < 0`. -/
def sumTo (f : ℤ → ℤ) (n : ℤ) : ℤ :=
  if 0 ≤ n then ∑ k ∈ Finset.range n.toNat, f k
  else -∑ k ∈ Finset.range (-n).toNat, f (n + k)

theorem sumTo_zero (f : ℤ → ℤ) : sumTo f 0 = 0 := by
  simp [sumTo]

theorem sumTo_succ (f : ℤ → ℤ) (n : ℤ) : sumTo f (n + 1) - sumTo f n = f n := by
  by_cases h0 : 0 ≤ n
  · have h1 : 0 ≤ n + 1 := by omega
    have e : (n + 1).toNat = n.toNat + 1 := by omega
    have e2 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
    simp only [sumTo, if_pos h0, if_pos h1, e, Finset.sum_range_succ, e2]
    ring
  · by_cases h1 : n + 1 = 0
    · have hn : n = -1 := by omega
      subst hn
      simp [sumTo]
    · have e : (-n).toNat = (-(n + 1)).toNat + 1 := by omega
      simp only [sumTo, if_neg h0, if_neg (show ¬ 0 ≤ n + 1 by omega), e, Finset.sum_range_succ']
      have hs : ∑ k ∈ Finset.range (-(n + 1)).toNat, f (n + ((k + 1 : ℕ) : ℤ)) =
          ∑ k ∈ Finset.range (-(n + 1)).toNat, f (n + 1 + (k : ℤ)) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      rw [hs]
      simp

/-- The horizontal and vertical offsets of the family, as functions of the lower-left index. -/
def hEdge (offset : ℤ × ℤ → ℤ × ℤ → ℤ) (i j : ℤ) : ℤ := offset (i, j) (i + 1, j)

def vEdge (offset : ℤ × ℤ → ℤ × ℤ → ℤ) (i j : ℤ) : ℤ := offset (i, j) (i, j + 1)

/-- The potential whose increments are the horizontal and vertical offsets. -/
def potG (offset : ℤ × ℤ → ℤ × ℤ → ℤ) (i j : ℤ) : ℤ :=
  sumTo (fun k => hEdge offset k 0) i + sumTo (fun l => vEdge offset i l) j

/-- The square condition, in the form of the proof: the offset sum around `(i,j),(i+1,j),(i+1,j+1),(i,j+1)` is zero. -/
theorem hEdge_step (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1)) (i j : ℤ) :
    hEdge offset i (j + 1) - hEdge offset i j = vEdge offset (i + 1) j - vEdge offset i j := by
  unfold hEdge vEdge
  linarith [hsq i j]

theorem hEdge_row (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1)) (i : ℤ) (j : ℤ) :
    hEdge offset i j - hEdge offset i 0 =
      sumTo (fun l => vEdge offset (i + 1) l) j - sumTo (fun l => vEdge offset i l) j := by
  set D : ℤ → ℤ := fun j => (hEdge offset i j - hEdge offset i 0) -
    (sumTo (fun l => vEdge offset (i + 1) l) j - sumTo (fun l => vEdge offset i l) j) with hDdef
  have hD : ∀ m : ℤ, D (m + 1) = D m := by
    intro m
    have h1 := hEdge_step offset hsq i m
    have h2 := sumTo_succ (fun l => vEdge offset (i + 1) l) m
    have h3 := sumTo_succ (fun l => vEdge offset i l) m
    simp only [hDdef]
    linarith
  have hD0 : ∀ m : ℤ, D m = 0 := by
    intro m
    induction m using Int.induction_on with
    | zero => simp [hDdef, sumTo_zero]
    | succ k ih => rw [hD k]; exact ih
    | pred k ih =>
      have h := hD (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at h
      rw [← h]
      exact ih
  have := hD0 j
  simp only [hDdef] at this
  linarith

theorem potG_h (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1)) (i j : ℤ) :
    potG offset (i + 1) j - potG offset i j = hEdge offset i j := by
  unfold potG
  have hr := hEdge_row offset hsq i j
  have s1 : sumTo (fun k => hEdge offset k 0) (i + 1) - sumTo (fun k => hEdge offset k 0) i =
      hEdge offset i 0 := sumTo_succ _ i
  linarith

theorem potG_v (offset : ℤ × ℤ → ℤ × ℤ → ℤ) (i j : ℤ) :
    potG offset i (j + 1) - potG offset i j = vEdge offset i j := by
  unfold potG
  have s := sumTo_succ (fun l => vEdge offset i l) j
  linarith

/-- Every dart of a unit step has the potential difference as its offset, in both directions. -/
theorem offset_eq_potG (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1))
    (hanti : ∀ i j : ℤ, offset (i + 1, j) (i, j) = -offset (i, j) (i + 1, j) ∧
      offset (i, j + 1) (i, j) = -offset (i, j) (i, j + 1))
    (x y : ℤ × ℤ)
    (hxy : (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
      (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1)) :
    offset x y = potG offset y.1 y.2 - potG offset x.1 x.2 := by
  obtain ⟨i, j⟩ := x
  obtain ⟨i', j'⟩ := y
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    simp only [h1, h2]
    have hp := potG_h offset hsq i j
    simp only [hEdge] at hp
    linarith
  · simp only at h1 h2
    simp only [h1, h2]
    have h := (hanti (i - 1) j).1
    have hp := potG_h offset hsq (i - 1) j
    simp only [hEdge, sub_add_cancel] at h hp
    linarith
  · simp only at h1 h2
    simp only [h1, h2]
    have hp := potG_v offset i j
    simp only [vEdge] at hp
    linarith
  · simp only at h1 h2
    simp only [h1, h2]
    have h := (hanti i (j - 1)).2
    have hp := potG_v offset i (j - 1)
    simp only [vEdge, sub_add_cancel] at h hp
    linarith

/-- The walk sums telescope to the potential difference of the endpoints. -/
theorem walkSum_eq_potG {α : Type*} {domain : ℤ × ℤ → Set α} (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hunit : ∀ x y : ℤ × ℤ, (overlapGraph domain).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1))
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1))
    (hanti : ∀ i j : ℤ, offset (i + 1, j) (i, j) = -offset (i, j) (i + 1, j) ∧
      offset (i, j + 1) (i, j) = -offset (i, j) (i, j + 1))
    {u v : ℤ × ℤ} (w : (overlapGraph domain).Walk u v) :
    walkSum offset w = potG offset v.1 v.2 - potG offset u.1 u.2 := by
  induction w with
  | nil => simp [walkSum_nil]
  | @cons x y z h p ih =>
    rw [walkSum_cons offset h p, ih]
    have hd := offset_eq_potG offset hsq hanti x y (hunit x y h)
    rw [hd]
    ring

/-- `lemma:common-extension-pseudo-square`, item (ii): every closed walk of the overlap graph has offset sum zero. -/
theorem closed_walk_sum_zero {α : Type*} {domain : ℤ × ℤ → Set α} (offset : ℤ × ℤ → ℤ × ℤ → ℤ)
    (hunit : ∀ x y : ℤ × ℤ, (overlapGraph domain).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1))
    (hsq : ∀ i j : ℤ, offset (i, j) (i + 1, j) + offset (i + 1, j) (i + 1, j + 1) =
      offset (i, j) (i, j + 1) + offset (i, j + 1) (i + 1, j + 1))
    (hanti : ∀ i j : ℤ, offset (i + 1, j) (i, j) = -offset (i, j) (i + 1, j) ∧
      offset (i, j + 1) (i, j) = -offset (i, j) (i, j + 1))
    (u : ℤ × ℤ) (w : (overlapGraph domain).Walk u u) :
    walkSum offset w = 0 := by
  rw [walkSum_eq_potG offset hunit hsq hanti w, sub_self]

/-- The square identity of the proof: with `a_{n/d,1} = 0`, `a_{n/d,2} = (n,-d)` and `v_{n/d,1}` a multiple of `(d,n)`,
the offset sum around a square, `a_1 · v_2 - a_2 · v_1`, vanishes. -/
theorem square_algebra (n d : ℤ) (a1 a2 v1 v2 : ℤ × ℤ) (ha1 : a1 = (0, 0)) (ha2 : a2 = (n, -d))
    (hv1 : v1 = (d, n) ∨ v1 = (2 * d, 2 * n)) :
    (a1.1 * v2.1 + a1.2 * v2.2) - (a2.1 * v1.1 + a2.2 * v1.2) = 0 := by
  subst ha1 ha2
  rcases hv1 with rfl | rfl <;> ring

end FLatticePaper.Tiles
