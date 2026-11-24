import FLatticePaper.Plane.Induction.QRankDeck
import FLatticePaper.Plane.Induction.EPolicyFields

/-!
# The deck-invariant rank `Qdeck` on `ℤ²` and the reflected rank `R0plus` (task 118, W1 base; bridge (iv), part one)

`Qdeck w` is `qRank n + 2d i - 2(d+1) j` for any decomposition `w = n + iU + jV` with `n` native. Independence of the
decomposition is `Qdeck_eq`, from the native-pair identities of `QRankDeck` (`qdeck_wd`, via `native_pair_cases`).
`Qdeck` agrees with `qRank` on native points (`Qdeck_native`) and has the exact deck characters `+2d` (U) and
`-2(d+1)` (V) (`Qdeck_add_U`, `Qdeck_add_V`).

`R0plus z = Qdeck (2 - z.1, d + 1 - z.2)` is the reflected rank for `η = +1`, with characters `-2d` (U) and `+2(d+1)` (V)
(`R0plus_U`, `R0plus_V`). Strictness along the policy edges is the remaining step.
-/

namespace FLatticePaper.ReflectedRank

open FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.QRankDeck FLatticePaper.Construction

theorem decomp_exists (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (x y : ℤ) :
    ∃ a b i j : ℤ, NativeP d (a, b) ∧ x = a + i * d + j * (1 - d) ∧ y = b + i + j * (d + 1) := by
  obtain ⟨n, hn, i, j, hw⟩ := exists_native_rep hden (x, y)
  rw [combine_mk_one hd] at hw
  have h1 := congrArg Prod.fst hw
  have h2 := congrArg Prod.snd hw
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  exact ⟨n.1, n.2, i, j, by simpa using hn, by linarith, by linarith⟩

set_option maxHeartbeats 400000 in
theorem qdeck_wd (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (a b a' b' c e : ℤ)
    (hn : NativeP d (a, b)) (hn' : NativeP d (a', b'))
    (h1 : a' = a + c * d + e * (1 - d)) (h2 : b' = b + c + e * (d + 1)) :
    qRank d (a', b') = qRank d (a, b) + 2 * d * c - 2 * (d + 1) * e := by
  rcases native_pair_cases hd hn hn' h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ha : a' = a := by linarith
    have hb : b' = b := by linarith
    subst ha hb
    ring
  · have ha : a' = a + d := by linarith
    have hb : b' = b + 1 := by linarith
    subst ha hb
    rw [qRank_shift_U d a b hd hdodd hn hn']
    ring
  · have ha : a' = a - d := by linarith
    have hb : b' = b - 1 := by linarith
    subst ha hb
    rw [qRank_shift_negU d a b hd hdodd hn hn']
    ring
  · have ha : a' = a + 1 - d := by linarith
    have hb : b' = b + 1 + d := by linarith
    subst ha hb
    rw [qRank_shift_V d a b hd hdodd hn hn']
    ring
  · have ha : a' = a - 1 + d := by linarith
    have hb : b' = b - 1 - d := by linarith
    subst ha hb
    rw [qRank_shift_negV d a b hd hdodd hn hn']
    ring

theorem decomp_triple (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) :
    ∃ p : Pt × ℤ × ℤ, NativeP d p.1 ∧ w.1 = p.1.1 + p.2.1 * d + p.2.2 * (1 - d) ∧
      w.2 = p.1.2 + p.2.1 + p.2.2 * (d + 1) := by
  obtain ⟨a, b, i, j, hn, h1, h2⟩ := decomp_exists d hd hden w.1 w.2
  exact ⟨((a, b), i, j), hn, h1, h2⟩

noncomputable def Qdeck (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) : ℤ :=
  qRank d (Classical.choose (decomp_triple d hd hden w)).1 +
    2 * d * (Classical.choose (decomp_triple d hd hden w)).2.1 -
    2 * (d + 1) * (Classical.choose (decomp_triple d hd hden w)).2.2

set_option maxHeartbeats 400000 in
theorem Qdeck_eq (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt)
    (p : Pt × ℤ × ℤ) (hp : NativeP d p.1 ∧ w.1 = p.1.1 + p.2.1 * d + p.2.2 * (1 - d) ∧
      w.2 = p.1.2 + p.2.1 + p.2.2 * (d + 1)) :
    Qdeck d hd hden w = qRank d p.1 + 2 * d * p.2.1 - 2 * (d + 1) * p.2.2 := by
  have hq := Classical.choose_spec (decomp_triple d hd hden w)
  obtain ⟨hn0, h10, h20⟩ := hq
  obtain ⟨hn, h1, h2⟩ := hp
  unfold Qdeck
  have key := qdeck_wd d hd3 hd p.1.1 p.1.2 (Classical.choose (decomp_triple d hd hden w)).1.1
    (Classical.choose (decomp_triple d hd hden w)).1.2 (p.2.1 - (Classical.choose (decomp_triple d hd hden w)).2.1)
    (p.2.2 - (Classical.choose (decomp_triple d hd hden w)).2.2) hn hn0
    (by linear_combination h1 - h10) (by linear_combination h2 - h20)
  rw [key]
  ring

theorem Qdeck_spec (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) :
    ∃ p : Pt × ℤ × ℤ, (NativeP d p.1 ∧ w.1 = p.1.1 + p.2.1 * d + p.2.2 * (1 - d) ∧
      w.2 = p.1.2 + p.2.1 + p.2.2 * (d + 1)) ∧
      Qdeck d hd hden w = qRank d p.1 + 2 * d * p.2.1 - 2 * (d + 1) * p.2.2 :=
  ⟨_, Classical.choose_spec (decomp_triple d hd hden w), rfl⟩

set_option maxHeartbeats 400000 in
theorem Qdeck_add_U (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) :
    Qdeck d hd hden (w.1 + d, w.2 + 1) = Qdeck d hd hden w + 2 * d := by
  obtain ⟨p, ⟨hn, h1, h2⟩, hQ⟩ := Qdeck_spec d hd hden w
  have hq' := Qdeck_eq d hd3 hd hden (w.1 + d, w.2 + 1) (p.1, p.2.1 + 1, p.2.2)
    ⟨hn, by simp only; linear_combination h1, by simp only; linear_combination h2⟩
  rw [hq', hQ]
  ring

set_option maxHeartbeats 400000 in
theorem Qdeck_add_V (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt) :
    Qdeck d hd hden (w.1 + (1 - d), w.2 + (1 + d)) = Qdeck d hd hden w - 2 * (d + 1) := by
  obtain ⟨p, ⟨hn, h1, h2⟩, hQ⟩ := Qdeck_spec d hd hden w
  have hq' := Qdeck_eq d hd3 hd hden (w.1 + (1 - d), w.2 + (1 + d)) (p.1, p.2.1, p.2.2 + 1)
    ⟨hn, by simp only; linear_combination h1, by simp only; linear_combination h2⟩
  rw [hq', hQ]
  ring

/-- The reflected rank of the reciprocal policy, for `η = +1`: `R0 z = Qdeck (Rc - z)`, `Rc = (2, d+1)`. -/
noncomputable def R0plus (d : ℤ) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) : ℤ :=
  Qdeck d hd hden (2 - z.1, d + 1 - z.2)

set_option maxHeartbeats 400000 in
theorem R0plus_U (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) :
    R0plus d hd hden (z.1 + d, z.2 + 1) = R0plus d hd hden z - 2 * d := by
  unfold R0plus
  have h := Qdeck_add_U d hd3 hd hden (2 - (z.1 + d), d + 1 - (z.2 + 1) )
  have e : (2 - (z.1 + d) + d, d + 1 - (z.2 + 1) + 1) = (2 - z.1, d + 1 - z.2) := by
    ext <;> simp only <;> ring
  have e2 : (2 - (z.1 + d), d + 1 - (z.2 + 1)) = (2 - (z.1 + d), d + 1 - (z.2 + 1)) := rfl
  rw [e] at h
  have e3 : (2 - (z.1 + d), d + 1 - (z.2 + 1)) = (2 - (z.1 + d), d + 1 - (z.2 + 1)) := rfl
  linarith

set_option maxHeartbeats 400000 in
theorem R0plus_V (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (z : Pt) :
    R0plus d hd hden (z.1 + (1 - d), z.2 + (1 + d)) = R0plus d hd hden z + 2 * (d + 1) := by
  unfold R0plus
  have h := Qdeck_add_V d hd3 hd hden (2 - z.1 + (d - 1), d + 1 - z.2 - (1 + d))
  have e : (2 - z.1 + (d - 1) + (1 - d), d + 1 - z.2 - (1 + d) + (1 + d)) = (2 - z.1, d + 1 - z.2) := by
    ext <;> simp only <;> ring
  rw [e] at h
  have e4 : (2 - (z.1 + (1 - d)), d + 1 - (z.2 + (1 + d))) = (2 - z.1 + (d - 1), d + 1 - z.2 - (1 + d)) := by
    ext <;> simp only <;> ring
  rw [e4]
  linarith

set_option maxHeartbeats 400000 in
theorem Qdeck_native (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (w : Pt)
    (hw : NativeP d w) : Qdeck d hd hden w = qRank d w := by
  rw [Qdeck_eq d hd3 hd hden w (w, 0, 0) ⟨hw, by simp, by simp⟩]
  ring

end FLatticePaper.ReflectedRank
