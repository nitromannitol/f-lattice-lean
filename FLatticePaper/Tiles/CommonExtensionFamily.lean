import FLatticePaper.Tiles.CommonExtensionClosedWalks

/-! # The square-sum condition for the translated odometers (`lemma:common-extension-pseudo-square`, item (ii), step (B))

For a partial odometer `o` on a tile `T` and the lattice vectors `v_1, v_2` with affine factors `a_1, a_2`, the family
`o_p(x) = o(x - v_p) + a_p · x` is indexed by `p ∈ ℤ²`, with `v_p = p_1 v_1 + p_2 v_2` and `a_p = p_1 a_1 + p_2 a_2`
(the translations of the paper). Its domains are `T + v_p`. If the offsets of overlapping members are constant, then the
offset `o_p - o_q` on the overlap is `κ(q-p) - a_{q-p} · v_p`, and the offset sum around a unit square is
`a_1 · v_2 - a_2 · v_1`. With `a_1 = 0`, `a_2 = (n,-d)` and `v_1 ∈ {(d,n), 2(d,n)}` this vanishes, which is the square
condition of `CommonExtensionClosedWalks`. -/

namespace FLatticePaper.Tiles.CommonExtFamily

/-- The lattice vector `p_1 v_1 + p_2 v_2`. -/
def vP (v1 v2 p : ℤ × ℤ) : ℤ × ℤ := (p.1 * v1.1 + p.2 * v2.1, p.1 * v1.2 + p.2 * v2.2)

/-- The affine factor `p_1 a_1 + p_2 a_2`. -/
def aP (a1 a2 p : ℤ × ℤ) : ℤ × ℤ := (p.1 * a1.1 + p.2 * a2.1, p.1 * a1.2 + p.2 * a2.2)

/-- The pairing `a · x`. -/
def dotZ (a x : ℤ × ℤ) : ℤ := a.1 * x.1 + a.2 * x.2

/-- The domain `T + v_p` of the translated odometer. -/
def dom (T : Set (ℤ × ℤ)) (v1 v2 p : ℤ × ℤ) : Set (ℤ × ℤ) := {x | x - vP v1 v2 p ∈ T}

/-- The translated odometer `o_p(x) = o(x - v_p) + a_p · x`. -/
def famOf (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 p x : ℤ × ℤ) : ℤ :=
  o (x - vP v1 v2 p) + dotZ (aP a1 a2 p) x

/-- The offset `κ(q-p) - a_{q-p} · v_p` between the translates `p` and `q`. -/
def offFam (κ : ℤ × ℤ → ℤ) (v1 v2 a1 a2 p q : ℤ × ℤ) : ℤ :=
  κ (q - p) - dotZ (aP a1 a2 (q - p)) (vP v1 v2 p)

theorem vP_add (v1 v2 p d : ℤ × ℤ) : vP v1 v2 (p + d) = vP v1 v2 p + vP v1 v2 d := by
  refine Prod.ext ?_ ?_
  · simp only [vP, Prod.fst_add, Prod.snd_add]
    ring
  · simp only [vP, Prod.fst_add, Prod.snd_add]
    ring

theorem aP_add (a1 a2 p d : ℤ × ℤ) : aP a1 a2 (p + d) = aP a1 a2 p + aP a1 a2 d := by
  refine Prod.ext ?_ ?_
  · simp only [aP, Prod.fst_add, Prod.snd_add]
    ring
  · simp only [aP, Prod.fst_add, Prod.snd_add]
    ring

theorem dotZ_add_right (a x y : ℤ × ℤ) : dotZ a (x + y) = dotZ a x + dotZ a y := by
  unfold dotZ
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem dotZ_add_left (a b x : ℤ × ℤ) : dotZ (a + b) x = dotZ a x + dotZ b x := by
  unfold dotZ
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem dotZ_sub_right (a x y : ℤ × ℤ) : dotZ a (x - y) = dotZ a x - dotZ a y := by
  unfold dotZ
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The difference of two translates at a point, written through `o`. -/
theorem famOf_diff (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 p d x : ℤ × ℤ) :
    famOf o v1 v2 a1 a2 p x - famOf o v1 v2 a1 a2 (p + d) x =
      (o (x - vP v1 v2 p) - (o (x - vP v1 v2 p - vP v1 v2 d) + dotZ (aP a1 a2 d) (x - vP v1 v2 p))) -
        dotZ (aP a1 a2 d) (vP v1 v2 p) := by
  unfold famOf
  rw [vP_add, aP_add, dotZ_add_left, dotZ_sub_right]
  have e : x - (vP v1 v2 p + vP v1 v2 d) = x - vP v1 v2 p - vP v1 v2 d := sub_add_eq_sub_sub _ _ _
  rw [e]
  ring

theorem offFam_eq (κ : ℤ × ℤ → ℤ) (v1 v2 a1 a2 p d : ℤ × ℤ) :
    offFam κ v1 v2 a1 a2 p (p + d) = κ d - dotZ (aP a1 a2 d) (vP v1 v2 p) := by
  unfold offFam
  rw [show p + d - p = d from Prod.ext (by simp) (by simp)]

/-- The offsets of overlapping translates are constant: `o_p - o_q = offFam κ p q` on the overlap, once the
constants `κ` describe the overlaps of `o` with its translates (the compatibility of `lemma:stacked_zero_one_string`). -/
theorem famOf_sub_eq_offFam (T : Set (ℤ × ℤ)) (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 : ℤ × ℤ) (κ : ℤ × ℤ → ℤ)
    (hκ : ∀ d y : ℤ × ℤ, y ∈ T → y - vP v1 v2 d ∈ T →
      o y - (o (y - vP v1 v2 d) + dotZ (aP a1 a2 d) y) = κ d)
    (p q x : ℤ × ℤ) (hx : x ∈ dom T v1 v2 p) (hq : x ∈ dom T v1 v2 q) :
    famOf o v1 v2 a1 a2 p x - famOf o v1 v2 a1 a2 q x = offFam κ v1 v2 a1 a2 p q := by
  have hqd : p + (q - p) = q := Prod.ext (by simp) (by simp)
  have hx' : x ∈ dom T v1 v2 (p + (q - p)) := by rw [hqd]; exact hq
  have key := hκ (q - p) (x - vP v1 v2 p) hx (by
    have h := hx'
    unfold dom at h
    simp only [Set.mem_setOf_eq] at h
    rw [vP_add] at h
    rw [sub_sub]
    exact h)
  have e := famOf_diff o v1 v2 a1 a2 p (q - p) x
  rw [hqd] at e
  rw [e, key]
  unfold offFam
  rfl

/-- The offsets of overlapping translates are antisymmetric. -/
theorem offFam_anti (T : Set (ℤ × ℤ)) (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 : ℤ × ℤ) (κ : ℤ × ℤ → ℤ)
    (hκ : ∀ d y : ℤ × ℤ, y ∈ T → y - vP v1 v2 d ∈ T →
      o y - (o (y - vP v1 v2 d) + dotZ (aP a1 a2 d) y) = κ d)
    (p q x : ℤ × ℤ) (hp : x ∈ dom T v1 v2 p) (hq : x ∈ dom T v1 v2 q) :
    offFam κ v1 v2 a1 a2 q p = -offFam κ v1 v2 a1 a2 p q := by
  have h1 := famOf_sub_eq_offFam T o v1 v2 a1 a2 κ hκ p q x hp hq
  have h2 := famOf_sub_eq_offFam T o v1 v2 a1 a2 κ hκ q p x hq hp
  linarith

theorem vP_shift1 (v1 v2 : ℤ × ℤ) (i j : ℤ) :
    vP v1 v2 (i + 1, j) = vP v1 v2 (i, j) + v1 := by
  refine Prod.ext ?_ ?_
  · simp only [vP, Prod.fst_add]
    ring
  · simp only [vP, Prod.snd_add]
    ring

theorem vP_shift2 (v1 v2 : ℤ × ℤ) (i j : ℤ) :
    vP v1 v2 (i, j + 1) = vP v1 v2 (i, j) + v2 := by
  refine Prod.ext ?_ ?_
  · simp only [vP, Prod.fst_add]
    ring
  · simp only [vP, Prod.snd_add]
    ring

theorem aP_e1 (a1 a2 : ℤ × ℤ) : aP a1 a2 (1, 0) = a1 :=
  Prod.ext (by simp [aP]) (by simp [aP])

theorem aP_e2 (a1 a2 : ℤ × ℤ) : aP a1 a2 (0, 1) = a2 :=
  Prod.ext (by simp [aP]) (by simp [aP])

/-- The square identity of the proof: the offset sum around `(i,j),(i+1,j),(i+1,j+1),(i,j+1)` is `a_1·v_2 - a_2·v_1`
(the two `κ`-terms cancel, and `vP` is additive). -/
theorem offFam_square (κ : ℤ × ℤ → ℤ) (v1 v2 a1 a2 : ℤ × ℤ) (i j : ℤ) :
    offFam κ v1 v2 a1 a2 (i, j) (i + 1, j) + offFam κ v1 v2 a1 a2 (i + 1, j) (i + 1, j + 1) =
      offFam κ v1 v2 a1 a2 (i, j) (i, j + 1) + offFam κ v1 v2 a1 a2 (i, j + 1) (i + 1, j + 1) +
        (dotZ a1 v2 - dotZ a2 v1) := by
  have d1 : (i + 1, j) - (i, j) = (1, 0) := Prod.ext (by simp) (by simp)
  have d2 : (i + 1, j + 1) - (i + 1, j) = (0, 1) := Prod.ext (by simp) (by simp)
  have d3 : (i, j + 1) - (i, j) = (0, 1) := Prod.ext (by simp) (by simp)
  have d4 : (i + 1, j + 1) - (i, j + 1) = (1, 0) := Prod.ext (by simp) (by simp)
  unfold offFam
  rw [d1, d2, d3, d4, aP_e1, aP_e2, vP_shift1, vP_shift2]
  simp only [dotZ, vP, Prod.fst_add, Prod.snd_add]
  ring

/-- The closed walks of the translated family have zero offset sum, under the three inputs of the proof:
overlaps of unit neighbours (`hA1`), overlaps only between neighbours (`hA2`), and the square identity `a_1·v_2 = a_2·v_1`
(`halg`). The offsets are the constants of the overlaps, `hκ`. -/
theorem family_closed_walks_zero (T : Set (ℤ × ℤ)) (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 : ℤ × ℤ)
    (κ : ℤ × ℤ → ℤ)
    (hκ : ∀ d y : ℤ × ℤ, y ∈ T → y - vP v1 v2 d ∈ T →
      o y - (o (y - vP v1 v2 d) + dotZ (aP a1 a2 d) y) = κ d)
    (hA1h : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i + 1, j))
    (hA1v : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i, j + 1))
    (hA2 : ∀ x y : ℤ × ℤ, (overlapGraph (dom T v1 v2)).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1))
    (halg : dotZ a1 v2 - dotZ a2 v1 = 0)
    (u : ℤ × ℤ) (w : (overlapGraph (dom T v1 v2)).Walk u u) :
    walkSum (offFam κ v1 v2 a1 a2) w = 0 := by
  have hsq : ∀ i j : ℤ, offFam κ v1 v2 a1 a2 (i, j) (i + 1, j) + offFam κ v1 v2 a1 a2 (i + 1, j) (i + 1, j + 1) =
      offFam κ v1 v2 a1 a2 (i, j) (i, j + 1) + offFam κ v1 v2 a1 a2 (i, j + 1) (i + 1, j + 1) := by
    intro i j
    rw [offFam_square, halg, add_zero]
  have hanti : ∀ i j : ℤ, offFam κ v1 v2 a1 a2 (i + 1, j) (i, j) = -offFam κ v1 v2 a1 a2 (i, j) (i + 1, j) ∧
      offFam κ v1 v2 a1 a2 (i, j + 1) (i, j) = -offFam κ v1 v2 a1 a2 (i, j) (i, j + 1) := by
    intro i j
    obtain ⟨x, hx1, hx2⟩ := hA1h i j
    obtain ⟨y, hy1, hy2⟩ := hA1v i j
    exact ⟨offFam_anti T o v1 v2 a1 a2 κ hκ (i, j) (i + 1, j) x hx1 hx2,
      offFam_anti T o v1 v2 a1 a2 κ hκ (i, j) (i, j + 1) y hy1 hy2⟩
  exact closed_walk_sum_zero (offFam κ v1 v2 a1 a2) hA2 hsq hanti u w

/-- The paper's data: `a_1 = 0`, `a_2 = (n,-d)` and `v_1` a multiple of `(d,n)` (eqs. affine_terms, translation_terms). -/
theorem family_closed_walks_zero_paper (T : Set (ℤ × ℤ)) (o : ℤ × ℤ → ℤ) (n d : ℤ)
    (v1 v2 a1 a2 : ℤ × ℤ) (κ : ℤ × ℤ → ℤ)
    (hκ : ∀ d' y : ℤ × ℤ, y ∈ T → y - vP v1 v2 d' ∈ T →
      o y - (o (y - vP v1 v2 d') + dotZ (aP a1 a2 d') y) = κ d')
    (hA1h : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i + 1, j))
    (hA1v : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i, j + 1))
    (hA2 : ∀ x y : ℤ × ℤ, (overlapGraph (dom T v1 v2)).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1))
    (ha1 : a1 = (0, 0)) (ha2 : a2 = (n, -d)) (hv1 : v1 = (d, n) ∨ v1 = (2 * d, 2 * n))
    (u : ℤ × ℤ) (w : (overlapGraph (dom T v1 v2)).Walk u u) :
    walkSum (offFam κ v1 v2 a1 a2) w = 0 := by
  refine family_closed_walks_zero T o v1 v2 a1 a2 κ hκ hA1h hA1v hA2 ?_ u w
  unfold dotZ
  rw [ha1, ha2]
  rcases hv1 with rfl | rfl <;> simp <;> ring

end FLatticePaper.Tiles.CommonExtFamily
