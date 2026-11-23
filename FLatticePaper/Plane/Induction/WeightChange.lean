import FLatticePaper.Graph
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-! Task 42: the weight change on a fixed graph (fix Q4-I3, "External facts").

A deck basis `U, V` with determinant `D ≠ 0` generates the lattice `L = {i U + j V}` (the deck). A relation `retained c i` lists
the retained inputs of a site. Suppose two deck-affine functions `P, J` (increments `(−1, 0)` and `(0, η)`) do not increase along
retained edges, and one old strict rank `r0` (increments `lam0 (−a0)`, `lam0 (c0 η)`) strictly decreases along them. Then for all
integers `a, c > 0` there is a rank with increments `lam (−a, c η)`, `lam > 0`, strictly decreasing along the retained edges.

Construction. The lift `w` (integer, with increments `(−a, c η)`) is `w z = ⌊(A z₁ + B z₂)/D⌋`. The walk value `M (w e − w z) + n` of a
retained walk of length `n` from `z` to `e`, with `M = lam0 (a0 + c0)`, is bounded: `n ≤ r0 z − r0 e` along a walk, so the value is at most
`g e − g z` with `g = M w − r0`; and `g` is bounded above on the sites `e` with `P e ≤ P z`, `J e ≤ J z`, by the monotonicity of `g`
along `U` and `V` (its increments have the right signs). The rank is `M w + R`, where `R z` is the supremum of the walk values from `z`. -/

namespace FLatticePaper.WeightChange

open FLatticePaper

/-- The deck point `i U + j V`. -/
def latPt (U V : Site) (i j : ℤ) : Site := (i * U.1 + j * V.1, i * U.2 + j * V.2)

/-- The determinant of the deck basis. -/
def detUV (U V : Site) : ℤ := U.1 * V.2 - U.2 * V.1

theorem latPt_zero (U V : Site) : latPt U V 0 0 = (0, 0) := by
  unfold latPt
  simp

theorem latPt_succ_fst (U V : Site) (n : ℤ) : latPt U V (n + 1) 0 = latPt U V n 0 + U := by
  unfold latPt
  ext <;> simp <;> ring

theorem latPt_succ_snd (U V : Site) (n : ℤ) : latPt U V 0 (n + 1) = latPt U V 0 n + V := by
  unfold latPt
  ext <;> simp <;> ring

theorem latPt_split (U V : Site) (i j : ℤ) : latPt U V i j = latPt U V i 0 + latPt U V 0 j := by
  unfold latPt
  ext <;> simp

/-- Adding the zero site does nothing. -/
theorem site_add_zero' (z : Site) : z + (0 : Site) = z := by
  ext <;> simp

/-- An affine sequence: `F (z + T n) = F z + n c` when `T` steps by `step` and `F` increases by `c` along `step`. -/
theorem affine_seq {F : Site → ℤ} {step : Site} {c : ℤ} (hstep : ∀ z, F (z + step) = F z + c)
    (T : ℤ → Site) (hT0 : T 0 = 0) (hTs : ∀ n, T (n + 1) = T n + step) (z : Site) (n : ℤ) :
    F (z + T n) = F z + n * c := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [hT0, site_add_zero', zero_mul, add_zero]
  · intro k ih
    have key : z + T ((k : ℤ) + 1) = (z + T k) + step := by
      rw [hTs]
      ext <;> simp <;> ring
    rw [key, hstep, ih]
    ring
  · intro k ih
    have h1 := hstep (z + T (-(k : ℤ) - 1))
    have h2 := hTs (-(k : ℤ) - 1)
    have e : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [e] at h2
    have h3 : z + T (-(k : ℤ)) = (z + T (-(k : ℤ) - 1)) + step := by
      rw [h2]
      ext <;> simp <;> ring
    have ih' : F (z + T (-(k : ℤ) - 1) + step) = F z + (-(k : ℤ)) * c := by
      rw [← h3]
      exact ih
    linear_combination ih' - h1

/-- A function with increments `p` along `U` and `q` along `V` has increment `i p + j q` along the deck point `i U + j V`. -/
theorem affine_lattice {F : Site → ℤ} {U V : Site} {p q : ℤ} (hU : ∀ z, F (z + U) = F z + p)
    (hV : ∀ z, F (z + V) = F z + q) (z : Site) (i j : ℤ) :
    F (z + latPt U V i j) = F z + i * p + j * q := by
  have hsplit' : z + latPt U V i j = (z + latPt U V i 0) + latPt U V 0 j := by
    rw [latPt_split]
    ext <;> simp <;> ring
  rw [hsplit']
  have hA : F (z + latPt U V i 0) = F z + i * p :=
    affine_seq hU (fun n => latPt U V n 0) (latPt_zero U V) (latPt_succ_fst U V) z i
  have hB : F (z + latPt U V i 0 + latPt U V 0 j) = F (z + latPt U V i 0) + j * q :=
    affine_seq hV (fun n => latPt U V 0 n) (latPt_zero U V) (latPt_succ_snd U V) (z + latPt U V i 0) j
  rw [hB, hA]

/-- The deck point of the determinant: `D x = i U + j V` with explicit integers. -/
theorem detUV_mul_lat (U V : Site) (x1 x2 : ℤ) :
    latPt U V (x1 * V.2 - x2 * V.1) (U.1 * x2 - U.2 * x1) = (detUV U V * x1, detUV U V * x2) := by
  unfold latPt detUV
  ext <;> simp <;> ring


/-! Walks and the Bellman rank. `RetWalk ret z e n`: a chain of `n` retained steps from `z` to `e`. -/

inductive RetWalk (ret : Site → Site → Prop) : Site → Site → ℕ → Prop
  | nil (z : Site) : RetWalk ret z z 0
  | cons {z i e : Site} {n : ℕ} : ret z i → RetWalk ret i e n → RetWalk ret z e (n + 1)

/-- The values `n + lam (w e − w z)` of the retained walks from `z`. -/
def retVal (ret : Site → Site → Prop) (w : Site → ℤ) (lam : ℤ) (z : Site) : Set ℤ :=
  {v | ∃ e : Site, ∃ n : ℕ, RetWalk ret z e n ∧ v = (n : ℤ) + lam * (w e - w z)}

/-- The Bellman rank `lam · w z + sup of the walk values from z`. -/
noncomputable def bellmanRank (ret : Site → Site → Prop) (w : Site → ℤ) (lam : ℤ) (z : Site) : ℤ :=
  lam * w z + sSup (retVal ret w lam z)

theorem retVal_nonempty (ret : Site → Site → Prop) (w : Site → ℤ) (lam : ℤ) (z : Site) :
    (retVal ret w lam z).Nonempty :=
  ⟨((0 : ℕ) : ℤ) + lam * (w z - w z), z, 0, RetWalk.nil z, rfl⟩

theorem retVal_cons {ret : Site → Site → Prop} {w : Site → ℤ} {lam : ℤ} {c i : Site} (hc : ret c i)
    {v : ℤ} (hv : v ∈ retVal ret w lam i) :
    1 + lam * (w i - w c) + v ∈ retVal ret w lam c := by
  obtain ⟨e, n, hW, rfl⟩ := hv
  refine ⟨e, n + 1, RetWalk.cons hc hW, ?_⟩
  push_cast
  ring

/-- Along a retained step the Bellman rank strictly drops, provided the walk values are bounded above. -/
theorem bellmanRank_lt {ret : Site → Site → Prop} {w : Site → ℤ} {lam : ℤ}
    (hb : ∀ z, BddAbove (retVal ret w lam z)) {c i : Site} (hc : ret c i) :
    bellmanRank ret w lam i < bellmanRank ret w lam c := by
  have e : lam * (w i - w c) = lam * w i - lam * w c := by ring
  have key : sSup (retVal ret w lam i) ≤ sSup (retVal ret w lam c) - (1 + lam * (w i - w c)) :=
    csSup_le (retVal_nonempty ret w lam i) (fun v hv => by
      have h := le_csSup (hb c) (retVal_cons hc hv)
      linarith)
  unfold bellmanRank
  linarith

/-- Retained walks are carried by a step-preserving translation. -/
theorem retWalk_translate {ret : Site → Site → Prop} (d : Site)
    (hstep : ∀ c i, ret c i → ret (c + d) (i + d)) {z e : Site} {n : ℕ} (h : RetWalk ret z e n) :
    RetWalk ret (z + d) (e + d) n := by
  induction h with
  | nil z => exact RetWalk.nil (z + d)
  | cons hr _ ih => exact RetWalk.cons (hstep _ _ hr) ih


/-- Deck translation cancels on the right, `c − d + d = c`. -/
theorem site_sub_add' (c d : Site) : c + -d + d = c := by
  ext <;> simp

/-- Deck translation cancels on the left, `c + d − d = c`. -/
theorem site_add_sub' (c d : Site) : c + d + -d = c := by
  ext <;> simp

/-- Deck invariance of the walk values: if the retained relation and `w` are invariant under the deck vector `d` (with
`w` shifting by `kd`), the value set at `z + d` equals the one at `z`. -/
theorem retVal_add_eq {ret : Site → Site → Prop} {w : Site → ℤ} {lam : ℤ} {d : Site} {kd : ℤ}
    (hiff : ∀ c i, ret c i ↔ ret (c + d) (i + d)) (hw : ∀ x, w (x + d) = w x + kd) (z : Site) :
    retVal ret w lam (z + d) = retVal ret w lam z := by
  ext v
  constructor
  · rintro ⟨e, n, hW, rfl⟩
    have hstep : ∀ c i, ret c i → ret (c + -d) (i + -d) := fun c i h =>
      (hiff (c + -d) (i + -d)).mpr (by rw [site_sub_add', site_sub_add']; exact h)
    have h2 := retWalk_translate (-d) hstep hW
    have hz : z + d + -d = z := site_add_sub' z d
    have he : e + -d + d = e := site_sub_add' e d
    have hwe : w e = w (e + -d) + kd := by
      have := hw (e + -d)
      rw [he] at this
      exact this
    rw [hz] at h2
    refine ⟨e + -d, n, h2, ?_⟩
    rw [hwe, hw z]
    ring
  · rintro ⟨e, n, hW, rfl⟩
    have hstep : ∀ c i, ret c i → ret (c + d) (i + d) := fun c i h => (hiff c i).mp h
    refine ⟨e + d, n, retWalk_translate d hstep hW, ?_⟩
    rw [hw e, hw z]
    ring

/-- The Bellman rank shifts by `lam kd` under the deck vector `d`. -/
theorem bellmanRank_add {ret : Site → Site → Prop} {w : Site → ℤ} {lam : ℤ} {d : Site} {kd : ℤ}
    (hiff : ∀ c i, ret c i ↔ ret (c + d) (i + d)) (hw : ∀ x, w (x + d) = w x + kd) (z : Site) :
    bellmanRank ret w lam (z + d) = bellmanRank ret w lam z + lam * kd := by
  unfold bellmanRank
  rw [retVal_add_eq hiff hw z, hw z]
  ring


/-! Finite representatives of the deck: every site is a deck translate of a site in a fixed finite box. -/

/-- The integer identity behind the decomposition: `D (e − (i U + j V)) = p U + q V` for the remainders `p, q`. -/
theorem deck_rep_identity (U V e : Site) (i j x y p q : ℤ)
    (hx : (U.1 * V.2 - U.2 * V.1) * i + p = x) (hy : (U.1 * V.2 - U.2 * V.1) * j + q = y)
    (hxd : x = e.1 * V.2 - e.2 * V.1) (hyd : y = U.1 * e.2 - U.2 * e.1) :
    (U.1 * V.2 - U.2 * V.1) * (e.1 - (i * U.1 + j * V.1)) = p * U.1 + q * V.1 ∧
      (U.1 * V.2 - U.2 * V.1) * (e.2 - (i * U.2 + j * V.2)) = p * U.2 + q * V.2 := by
  constructor
  · linear_combination (-U.1) * hx + (-V.1) * hy - U.1 * hxd - V.1 * hyd
  · linear_combination (-U.2) * hx + (-V.2) * hy - U.2 * hxd - V.2 * hyd

/-- A bound on a coordinate: if `D r = p a + q b` with remainders `0 ≤ p, q < |D|`, then `|r| ≤ |a| + |b|`. -/
theorem abs_le_of_det_eq {D r p q a b : ℤ} (hD : D ≠ 0) (hp0 : 0 ≤ p) (hpD : p < |D|) (hq0 : 0 ≤ q)
    (hqD : q < |D|) (h : D * r = p * a + q * b) : |r| ≤ |a| + |b| := by
  have hpos : 0 < |D| := abs_pos.mpr hD
  have e1 : |D * r| = |D| * |r| := abs_mul D r
  have e2 : |p * a + q * b| ≤ |p * a| + |q * b| := abs_add_le _ _
  have e3 : |p * a| = p * |a| := by rw [abs_mul, abs_of_nonneg hp0]
  have e4 : |q * b| = q * |b| := by rw [abs_mul, abs_of_nonneg hq0]
  rw [h] at e1
  have key : |D| * |r| ≤ |D| * (|a| + |b|) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpD.le) (abs_nonneg a),
      mul_nonneg (sub_nonneg.2 hqD.le) (abs_nonneg b)]
  exact le_of_mul_le_mul_left key hpos

/-- **Finite deck representatives.** For a nondegenerate deck basis `U, V`, the sites are covered by finitely many deck
translates: every `e` equals `r + i U + j V` with `r` in a fixed finite box. -/
theorem exists_deck_box (U V : Site) (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) :
    ∃ S : Finset Site, ∀ e : Site, ∃ r ∈ S, ∃ i j : ℤ, e = r + latPt U V i j := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = |U.1| + |V.1| + |U.2| + |V.2| := ⟨_, rfl⟩
  refine ⟨Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B, fun e => ?_⟩
  obtain ⟨x, hxd⟩ : ∃ x : ℤ, x = e.1 * V.2 - e.2 * V.1 := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y : ℤ, y = U.1 * e.2 - U.2 * e.1 := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : ℤ, i = x / (U.1 * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = y / (U.1 * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p = x % (U.1 * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = y % (U.1 * V.2 - U.2 * V.1) := ⟨_, rfl⟩
  have hx : (U.1 * V.2 - U.2 * V.1) * i + p = x := by
    rw [hi, hp]
    linarith [Int.emod_def x (U.1 * V.2 - U.2 * V.1)]
  have hy : (U.1 * V.2 - U.2 * V.1) * j + q = y := by
    rw [hj, hq]
    linarith [Int.emod_def y (U.1 * V.2 - U.2 * V.1)]
  have hp0 : 0 ≤ p := by
    rw [hp]
    exact Int.emod_nonneg _ hD
  have hpD : p < |U.1 * V.2 - U.2 * V.1| := by
    rw [hp, Int.abs_eq_natAbs]
    exact_mod_cast Int.emod_lt x hD
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Int.emod_nonneg _ hD
  have hqD : q < |U.1 * V.2 - U.2 * V.1| := by
    rw [hq, Int.abs_eq_natAbs]
    exact_mod_cast Int.emod_lt y hD
  obtain ⟨h1, h2⟩ := deck_rep_identity U V e i j x y p q hx hy hxd hyd
  have hb1 := abs_le_of_det_eq hD hp0 hpD hq0 hqD h1
  have hb2 := abs_le_of_det_eq hD hp0 hpD hq0 hqD h2
  have hB1 : |e.1 - (i * U.1 + j * V.1)| ≤ B := by
    rw [hB]
    linarith [abs_nonneg U.2, abs_nonneg V.2]
  have hB2 : |e.2 - (i * U.2 + j * V.2)| ≤ B := by
    rw [hB]
    linarith [abs_nonneg U.1, abs_nonneg V.1]
  refine ⟨(e.1 - (i * U.1 + j * V.1), e.2 - (i * U.2 + j * V.2)), ?_, i, j, ?_⟩
  · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨abs_le.mp hB1, abs_le.mp hB2⟩
  · ext <;> simp [latPt]

end FLatticePaper.WeightChange
