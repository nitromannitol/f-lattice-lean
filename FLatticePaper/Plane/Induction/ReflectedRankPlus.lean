import FLatticePaper.Plane.Induction.QRankPlusDeck
import FLatticePaper.Plane.Induction.ReflectedRank
import FLatticePaper.Plane.Induction.ReflectWitness

/-!
# The deck-invariant plus rank and the reflected plus rank `R0minus` (task 118, W1 base; eta = -1, part one)

The plus analogue of `ReflectedRank`: `QdeckP w = qRankP n + 2d i + 2(d+1) j` for any decomposition `w = n + iU + jV` with `n`
native (`qdeckP_wd` from the plus shift identities; `QdeckP_eq`, `QdeckP_native`, `QdeckP_add_combine`). `R0minus z =
QdeckP (2 - z.1, d + 1 - z.2)` is the reflected rank for `eta = -1`, with characters `-2d` (U) and `-2(d+1)` (V)
(`R0minus_U`, `R0minus_V`). `strict_native_minus` is the strictness at native targets (`qplus_gate` at `Rc - y`).
-/

namespace FLatticePaper.ReflectedRankPlus

open FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRank FLatticePaper.QRankPlusDeck FLatticePaper.ReflectWitness FLatticePaper.Construction

set_option maxHeartbeats 400000 in
theorem qdeckP_wd (d : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (a b a' b' c e : ℤ)
    (hn : NativeP d (a, b)) (hn' : NativeP d (a', b'))
    (h1 : a' = a + c * d + e * (1 - d)) (h2 : b' = b + c + e * (d + 1)) :
    qRankP d (a', b') = qRankP d (a, b) + 2 * d * c + 2 * (d + 1) * e := by
  rcases native_pair_cases hd3 hn hn' h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha : a' = a := by linarith
    have hb : b' = b := by linarith
    subst ha hb
    ring
  · have ha : a' = a + d := by linarith
    have hb : b' = b + 1 := by linarith
    subst ha hb
    rw [qRankP_shift_U d a b hd3 hdodd hn hn']
    ring
  · have ha : a' = a - d := by linarith
    have hb : b' = b - 1 := by linarith
    subst ha hb
    rw [qRankP_shift_negU d a b hd3 hdodd hn hn']
    ring
  · have ha : a' = a + 1 - d := by linarith
    have hb : b' = b + 1 + d := by linarith
    subst ha hb
    rw [qRankP_shift_V d a b hd3 hdodd hn hn']
    ring
  · have ha : a' = a - 1 + d := by linarith
    have hb : b' = b - 1 - d := by linarith
    subst ha hb
    rw [qRankP_shift_negV d a b hd3 hdodd hn hn']
    ring

noncomputable def QdeckP (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) : ℤ :=
  qRankP d (Classical.choose (decomp_triple d hd hden w)).1 +
    2 * d * (Classical.choose (decomp_triple d hd hden w)).2.1 +
    2 * (d + 1) * (Classical.choose (decomp_triple d hd hden w)).2.2

set_option maxHeartbeats 400000 in
theorem QdeckP_eq (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt)
    (p : Pt × ℤ × ℤ) (hp : NativeP d p.1 ∧ w.1 = p.1.1 + p.2.1 * d + p.2.2 * (1 - d) ∧
      w.2 = p.1.2 + p.2.1 + p.2.2 * (d + 1)) :
    QdeckP d hd hden w = qRankP d p.1 + 2 * d * p.2.1 + 2 * (d + 1) * p.2.2 := by
  have hq := Classical.choose_spec (decomp_triple d hd hden w)
  obtain ⟨hn0, h10, h20⟩ := hq
  obtain ⟨hn, h1, h2⟩ := hp
  unfold QdeckP
  have key := qdeckP_wd d hd3 hd p.1.1 p.1.2 (Classical.choose (decomp_triple d hd hden w)).1.1
    (Classical.choose (decomp_triple d hd hden w)).1.2 (p.2.1 - (Classical.choose (decomp_triple d hd hden w)).2.1)
    (p.2.2 - (Classical.choose (decomp_triple d hd hden w)).2.2) hn hn0
    (by linear_combination h1 - h10) (by linear_combination h2 - h20)
  rw [key]
  ring

set_option maxHeartbeats 400000 in
theorem QdeckP_native (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt)
    (hw : NativeP d w) : QdeckP d hd hden w = qRankP d w := by
  rw [QdeckP_eq d hd3 hd hden w (w, 0, 0) ⟨hw, by simp, by simp⟩]
  ring

theorem QdeckP_spec (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) :
    ∃ p : Pt × ℤ × ℤ, (NativeP d p.1 ∧ w.1 = p.1.1 + p.2.1 * d + p.2.2 * (1 - d) ∧
      w.2 = p.1.2 + p.2.1 + p.2.2 * (d + 1)) ∧
      QdeckP d hd hden w = qRankP d p.1 + 2 * d * p.2.1 + 2 * (d + 1) * p.2.2 :=
  ⟨_, Classical.choose_spec (decomp_triple d hd hden w), rfl⟩

set_option maxHeartbeats 400000 in
theorem QdeckP_add_combine (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (w : Pt) (a b : ℤ) :
    QdeckP d hd hden (w.1 + a * d + b * (1 - d), w.2 + a + b * (d + 1)) =
      QdeckP d hd hden w + 2 * d * a + 2 * (d + 1) * b := by
  obtain ⟨p, ⟨hn, h1, h2⟩, hQ⟩ := QdeckP_spec d hd hden w
  have hq' := QdeckP_eq d hd3 hd hden (w.1 + a * d + b * (1 - d), w.2 + a + b * (d + 1))
    (p.1, p.2.1 + a, p.2.2 + b) ⟨hn, by simp only; linear_combination h1, by simp only; linear_combination h2⟩
  rw [hq', hQ]
  ring

/-- The reflected plus rank, for `η = -1`: `R0minus z = QdeckP (Rc - z)`, `Rc = (2, d+1)`. -/
noncomputable def R0minus (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) : ℤ :=
  QdeckP d hd hden (2 - z.1, d + 1 - z.2)

set_option maxHeartbeats 400000 in
theorem R0minus_add_combine (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (z : Pt) (a b : ℤ) :
    R0minus d hd hden (z.1 + a * d + b * (1 - d), z.2 + a + b * (d + 1)) =
      R0minus d hd hden z - 2 * d * a - 2 * (d + 1) * b := by
  unfold R0minus
  have h := QdeckP_add_combine d hd3 hd hden (2 - z.1, d + 1 - z.2) (-a) (-b)
  have e : (2 - (z.1 + a * d + b * (1 - d)), d + 1 - (z.2 + a + b * (d + 1))) =
      ((2 - z.1, d + 1 - z.2).1 + (-a) * d + (-b) * (1 - d), (2 - z.1, d + 1 - z.2).2 + (-a) + (-b) * (d + 1)) := by
    ext <;> simp only <;> ring
  rw [e, h]
  ring

set_option maxHeartbeats 400000 in
theorem R0minus_U (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) :
    R0minus d hd hden (z.1 + d, z.2 + 1) = R0minus d hd hden z - 2 * d := by
  have h := R0minus_add_combine d hd3 hd hden z 1 0
  have e : (z.1 + 1 * d + 0 * (1 - d), z.2 + 1 + 0 * (d + 1)) = (z.1 + d, z.2 + 1) := by
    ext <;> simp only <;> ring
  rw [e] at h
  rw [h]
  ring

set_option maxHeartbeats 400000 in
theorem R0minus_V (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) :
    R0minus d hd hden (z.1 + (1 - d), z.2 + (1 + d)) = R0minus d hd hden z - 2 * (d + 1) := by
  have h := R0minus_add_combine d hd3 hd hden z 0 1
  have e : (z.1 + 0 * d + 1 * (1 - d), z.2 + 0 + 1 * (d + 1)) = (z.1 + (1 - d), z.2 + (1 + d)) := by
    ext <;> simp only <;> ring
  rw [e] at h
  rw [h]
  ring

set_option maxHeartbeats 400000 in
theorem strict_native_minus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hR : RetainedP d (2 - x) (d + 1 - y) (-e1) (-e2))
    (hunit : (-e1, -e2) = (1, 0) ∨ (-e1, -e2) = (-1, 0) ∨ (-e1, -e2) = (0, 1) ∨ (-e1, -e2) = (0, -1))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    qRankP d (2 - (x + e1), d + 1 - (y + e2)) < qRankP d (2 - x, d + 1 - y) := by
  have hs : NativeP d (2 - x, d + 1 - y) := (nativeP_refl d x y).mpr hN
  have hr := rankOfP_qRankP d hd3 (2 - (x + e1)) (d + 1 - (y + e2)) hT
  have e : (2 - x + -e1, d + 1 - y + -e2) = (2 - (x + e1), d + 1 - (y + e2)) := by
    ext <;> simp only <;> ring
  have hr' : RankOfP d (2 - x + -e1, d + 1 - y + -e2) (qRankP d (2 - (x + e1), d + 1 - (y + e2))) := by
    rw [e]; exact hr
  exact qplus_gate d (2 - x) (d + 1 - y) (-e1) (-e2) hd3 hdodd hs hunit hR _ hr'

end FLatticePaper.ReflectedRankPlus
