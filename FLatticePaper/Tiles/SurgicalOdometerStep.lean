import FLatticePaper.Tiles.SurgicalOdometers
import FLatticePaper.Tiles.SurgicalDict

/-! # One decomposition step of the weak standard odometers (surgical `def:weak_standard_odometers`, eq:std_odometer_decomposition)

For the odd standard tile `T(p_0)`, the decomposition `T(p_0) = T(p_1)^+ ∪ T(p_1)^- ∪ T^d(q_1)^+ ∪ T^d(q_1)^-` (SurgicalDict,
`placeP0`) carries the odometer decomposition `o_{p_0} = o_{p_1}^+ ∪ o_{p_1}^- ∪ d(o)_{q_1}^+ ∪ d(o)_{q_1}^-`. A piece of
`o_{p_0}` is a translate of its subodometer: its domain is the placed copy of the subodometer's domain, and on it the values are
those of the subodometer shifted by the placement offset, with the affine correction `a_{n/d,i} ^T x` of `RespectTileTranslations`
and an integer constant. This file states that one step (for `T(p_0)`, both parities; the `T(q_0)` step is the same with the
roles of `p` and `q` exchanged). The subodometers of the doubled pieces are weak doubled odometers; they are parameters here. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Tiles.SurgicalDict

/-- The piece `child` (a weak subodometer with domain `D_child`) is placed at offset `off` inside `parent`: the parent's
domain contains the translated domain of `child`, and on it the parent's values are the translated values of `child` with the
affine correction `a^T x` (with `a = a_{n/d,i}`, the slope offset of the respect relation) and an integer constant `b`. -/
def PlacedPiece (parent child : PartialOdometer) (off a : Site) : Prop :=
  ∃ b : ℤ, (child.dom.image (· + off)) ⊆ parent.dom ∧
    ∀ x ∈ child.dom.image (· + off),
      parent.val x = child.val (x - off) + (a.1 * x.1 + a.2 * x.2) + b

/-- The decomposition step of the odd standard tile `T(p_0)` (`eq:std_odometer_decomposition`, first line). The four
subodometers are `o_{p_1}^±` (`p1Plus`, `p1Minus`) and `d(o)_{q_1}^±` (`q1DPlus`, `q1DMinus`), placed by the offsets of
`offsetP0` (SurgicalDict). Each piece carries its affine correction `a_x` as an explicit parameter: the rule that fixes `a_x` for a
composite placement offset is an open question for the text (see the report), so it is not chosen here. The parent domain is
the union of the four placed domains. -/
def IsStdStepP0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site)
    (opz op1p op1m dqp dqm : PartialOdometer) (ap am aqp aqm : Site) : Prop :=
  PlacedPiece opz op1p (offsetP0 odd vp1 vp2 vq1 vq2 .p1Plus) ap ∧
  PlacedPiece opz op1m (offsetP0 odd vp1 vp2 vq1 vq2 .p1Minus) am ∧
  PlacedPiece opz dqp (offsetP0 odd vp1 vp2 vq1 vq2 .q1DPlus) aqp ∧
  PlacedPiece opz dqm (offsetP0 odd vp1 vp2 vq1 vq2 .q1DMinus) aqm

/-- The affine factor of a translation by `c₁ v_{r,1} + c₂ v_{r,2}` (operator rule, eq:periodicity): `c₁ a_{r,1} + c₂ a_{r,2}`
with `a_{r,1} = 0` and `a_{r,2} = (n_r, −d_r)` (`offsetA`). -/
def pairAffine (n d c1 c2 : ℤ) : Site :=
  (c1 * (offsetA n d false).1 + c2 * (offsetA n d true).1, c1 * (offsetA n d false).2 + c2 * (offsetA n d true).2)

/-- The step with `W_1` odd (the table `eq:offsets_w1_odd`) and the operator's rule: the placement offsets of `offsetP0` (odd) are `0` for `p1Plus`,
`2 v_{q1,1} + v_{q1,2}` for `p1Minus`, `v_{p1,1}` for `q1DPlus` and `v_{p1,2}` for `q1DMinus`; their affine factors are
`0`, `a_{q1,2}`, `0` and `a_{p1,2}`. -/
def IsStdStepP0W1Odd (vp1 vp2 vq1 vq2 : Site) (np dp nq dq : ℤ)
    (opz op1p op1m dqp dqm : PartialOdometer) : Prop :=
  IsStdStepP0 true vp1 vp2 vq1 vq2 opz op1p op1m dqp dqm
    (pairAffine nq dq 0 0) (pairAffine nq dq 2 1) (pairAffine np dp 1 0) (pairAffine np dp 0 1)

/-- The step with `W_1` even (the table `eq:offsets_w1_even`) and the operator's rule: the placement offsets of `offsetP0` (even) are `2 v_{q1,1}` for `p1Plus`,
`v_{q1,2}` for `p1Minus`, `0` for `q1DPlus` and `v_{p1,1} + v_{p1,2}` for `q1DMinus`; their affine factors are `0`, `a_{q1,2}`,
`0` and `a_{p1,2}`. -/
def IsStdStepP0W1Even (vp1 vp2 vq1 vq2 : Site) (np dp nq dq : ℤ)
    (opz op1p op1m dqp dqm : PartialOdometer) : Prop :=
  IsStdStepP0 false vp1 vp2 vq1 vq2 opz op1p op1m dqp dqm
    (pairAffine nq dq 2 0) (pairAffine nq dq 0 1) (pairAffine np dp 0 0) (pairAffine np dp 1 1)

end FLatticePaper.Tiles
