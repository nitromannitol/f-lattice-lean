import FLatticePaper.Plane.Induction.ReflectedRank
import FLatticePaper.Plane.Induction.ReflectWitness

/-!
# Strictness of the reflected rank along the policy edges with native targets (task 118, W1 base; bridge iv, part two)

For a native centre `y` and a policy edge `y → y + e` (`RetNat` with `η = +1`) whose target `y + e` is native, the reflected
rank `R0plus` strictly decreases. The proof is the qminus gate (`qminus_gate`) applied at the reflected source `Rc - y`, with
the retained direction given by the witnesses (`edge_white_plus`, `edge_black_plus`) and the rank at the native target by
`rankOf_qRank`; the values of `R0plus` at native points are `qRank` (`Qdeck_native`).

Non-native targets are not covered here.
-/

namespace FLatticePaper.ReflectedStrict

open FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRank FLatticePaper.ReflectWitness FLatticePaper.Construction

theorem strict_native_plus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1) (hN : NativeP d (x, y))
    (hR : Retained d (2 - x) (d + 1 - y) (-e1) (-e2))
    (hunit : (-e1, -e2) = (1, 0) ∨ (-e1, -e2) = (-1, 0) ∨ (-e1, -e2) = (0, 1) ∨ (-e1, -e2) = (0, -1))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    qRank d (2 - (x + e1), d + 1 - (y + e2)) < qRank d (2 - x, d + 1 - y) := by
  have hs : NativeP d (2 - x, d + 1 - y) := (nativeP_refl d x y).mpr hN
  have hr := rankOf_qRank d hd3 (2 - (x + e1)) (d + 1 - (y + e2)) hT
  have e : (2 - x + -e1, d + 1 - y + -e2) = (2 - (x + e1), d + 1 - (y + e2)) := by
    ext <;> simp only <;> ring
  have hr' : RankOf d (2 - x + -e1, d + 1 - y + -e2) (qRank d (2 - (x + e1), d + 1 - (y + e2))) := by
    rw [e]; exact hr
  exact qminus_gate d (2 - x) (d + 1 - y) (-e1) (-e2) hd3 hdodd hs hunit hR _ hr'

theorem R0plus_strict_native (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y))
    (hR : Retained d (2 - x) (d + 1 - y) (-e1) (-e2))
    (hunit : (-e1, -e2) = (1, 0) ∨ (-e1, -e2) = (-1, 0) ∨ (-e1, -e2) = (0, 1) ∨ (-e1, -e2) = (0, -1))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0plus d hdodd hden (x + e1, y + e2) < R0plus d hdodd hden (x, y) := by
  have hs : NativeP d (2 - x, d + 1 - y) := (nativeP_refl d x y).mpr hN
  unfold R0plus
  dsimp only
  rw [Qdeck_native d hd3 hdodd hden _ hT, Qdeck_native d hd3 hdodd hden _ hs]
  exact strict_native_plus d x y e1 e2 hd3 hdodd hN hR hunit hT

theorem selDisp_unit (d η : ℤ) (hη : η = 1 ∨ η = -1) (p : Pt) :
    selDisp d η p = (1, 0) ∨ selDisp d η p = (-1, 0) ∨ selDisp d η p = (0, 1) ∨ selDisp d η p = (0, -1) := by
  unfold selDisp
  split_ifs <;> rcases hη with rfl | rfl <;> simp

theorem black_unit (d η x y e1 e2 : ℤ) (h : RetNat d η True (x, y) ((x, y) + (e1, e2))) :
    (e1, e2) = (1, 0) ∨ (e1, e2) = (-1, 0) ∨ (e1, e2) = (0, 1) ∨ (e1, e2) = (0, -1) := by
  obtain ⟨h1, -⟩ := h
  by_cases hev : (x + y) % 2 = 0
  · have hE : FLatticePaper.EvenSite (x, y) := hev
    rcases h1 with h1 | h1
    · rw [incomingNeg_even hE] at h1
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at h1
      right; left; ext <;> simp <;> omega
    · rw [incomingPos_even hE] at h1
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at h1
      left; ext <;> simp <;> omega
  · have hO : ¬ FLatticePaper.EvenSite (x, y) := hev
    rcases h1 with h1 | h1
    · rw [incomingNeg_odd hO] at h1
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at h1
      right; right; right; ext <;> simp <;> omega
    · rw [incomingPos_odd hO] at h1
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at h1
      right; right; left; ext <;> simp <;> omega

theorem neg_unit (e1 e2 : ℤ)
    (h : (e1, e2) = (1, 0) ∨ (e1, e2) = (-1, 0) ∨ (e1, e2) = (0, 1) ∨ (e1, e2) = (0, -1)) :
    (-e1, -e2) = (1, 0) ∨ (-e1, -e2) = (-1, 0) ∨ (-e1, -e2) = (0, 1) ∨ (-e1, -e2) = (0, -1) := by
  rcases h with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

theorem R0plus_edge_white_plus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y)) (hW : WhiteN d (x, y))
    (h : RetNat d 1 False (x, y) ((x, y) + (e1, e2)))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0plus d hdodd hden (x + e1, y + e2) < R0plus d hdodd hden (x, y) := by
  have he := (retNat_white_pt hd3 hdodd (Or.inl rfl) hN hW (e1, e2)).mp h
  have hR := edge_white_plus d x y e1 e2 hd3 hdodd hN hW h
  have hu : (e1, e2) = (1, 0) ∨ (e1, e2) = (-1, 0) ∨ (e1, e2) = (0, 1) ∨ (e1, e2) = (0, -1) := by
    rw [he]
    rcases selDisp_unit d 1 (Or.inl rfl) (x, y) with h' | h' | h' | h' <;> simp [h']
  exact R0plus_strict_native d x y e1 e2 hd3 hdodd hden hN hR (neg_unit e1 e2 hu) hT

theorem R0plus_edge_black_plus (d x y e1 e2 : ℤ) (hd3 : 3 ≤ d) (hdodd : d % 2 = 1)
    (hden : BaseMask.stairEven.Valid d) (hN : NativeP d (x, y)) (hB : ¬ WhiteN d (x, y))
    (h : RetNat d 1 True (x, y) ((x, y) + (e1, e2)))
    (hT : NativeP d (2 - (x + e1), d + 1 - (y + e2))) :
    R0plus d hdodd hden (x + e1, y + e2) < R0plus d hdodd hden (x, y) :=
  R0plus_strict_native d x y e1 e2 hd3 hdodd hden hN (edge_black_plus d x y e1 e2 hd3 hdodd hN hB h)
    (neg_unit e1 e2 (black_unit d 1 x y e1 e2 h)) hT

end FLatticePaper.ReflectedStrict
