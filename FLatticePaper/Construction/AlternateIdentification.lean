import FLatticePaper.Construction.PlaneIdentification
import FLatticePaper.Tiles.AlternateAgreement
import FLatticePaper.Plane.AlternateMidpoint

/-! # The plane target of the ordinary even alternate and its branches (task 46, Lean)

The plane alternate field of a word is the rounded midpoint of the standard even field `F` of the word and its translate
`G(s) = F(s + σ)`, with `σ = 2 ε (D, N)` for the even child `N/D` of the word and `ε` the frame sign (`-1` for even phase).
The numerical check (scripts/alt_plane_check.py, scripts/alt_copy_check.py) finds that the ordinary even alternate outputs of
words of length at most three, and all their copies, agree with this target at zero translation; on every copy the gap
`F(s) - F(s + σ)` lies in `[0, 2]`.

On that window the rounded midpoint is the minimum `min(F, G + 1)` (`roundedMidpoint_eq_min_of_slip` at level zero). So a
tile agrees with the alternate target as soon as each of its heights is `F + g` on the sites where `F ≤ G + 1`, and
`G + 1 + g` on the sites where `G + 1 < F`: these are the two branches, and the copies of the output are sheets of the
standard field, attained on the branch of their sites. -/

namespace FLatticePaper.Construction

open Farey FLatticePaper FLatticePaper.Induction HeightTile

/-- The shift of the alternate midpoint: `σ = 2 ε (D, N)`, with `N / D` the odd parent of the word (the left parent of its
Farey pair, as `parents(w)[0]` in scripts/proto2.py) and `ε` the frame sign. -/
def alternateSigma (word : Word) : Site :=
  (2 * (frameAt word).eps * (parentsAt word).odd.den, 2 * (frameAt word).eps * (parentsAt word).odd.num)

/-- The plane alternate field of a word: the rounded midpoint of the standard even field and its `σ`-translate. -/
noncomputable def alternateTarget (word : Word) : Field :=
  roundedMidpoint (standardField word) (fun s => standardField word (s + alternateSigma word))

/-- On the window `0 ≤ F(s) − G(s) ≤ 2`, the alternate target is the minimum `min(F, G + 1)`. -/
theorem alternateTarget_eq_min {word : Word} (s : Site)
    (hlo : 0 ≤ standardField word s - standardField word (s + alternateSigma word))
    (hhi : standardField word s - standardField word (s + alternateSigma word) ≤ 2) :
    alternateTarget word s =
      min (standardField word s) (standardField word (s + alternateSigma word) + 1) := by
  have h1 : 2 * (0 : ℤ) ≤ standardField word s - standardField word (s + alternateSigma word) := by
    rw [mul_zero]
    exact hlo
  have h2 : standardField word s - standardField word (s + alternateSigma word) ≤ 2 * (0 : ℤ) + 2 := by
    rw [mul_zero, zero_add]
    exact hhi
  have h := roundedMidpoint_eq_min_of_slip (standardField word)
    (fun t => standardField word (t + alternateSigma word)) s 0 h1 h2
  unfold alternateTarget
  rw [h]
  simp

/-- Agreement with a target transfers to a pointwise equal target on the sites of the tile. -/
theorem HeightTile.Agrees.congr_target {α : Type*} {tile : HeightTile α} {target target' : α → ℤ} {gauge : ℤ}
    (h : tile.Agrees target gauge) (hT : ∀ s ∈ tile.sites, target' s = target s) :
    tile.Agrees target' gauge := by
  intro site
  rw [h site, hT site.1 site.2]

/-- **The branch criterion.** A tile on the window `0 ≤ F − G ≤ 2` agrees with the alternate target, with the constant `g`,
when its height is `F + g` on the sites where `F − G ≤ 1` and `G + 1 + g` on the sites where `F − G ≥ 2`. -/
theorem HeightTile.Agrees.alternateTarget_of_branches {word : Word} {tile : HeightTile Site} {gauge : ℤ}
    (hwin : ∀ s ∈ tile.sites, 0 ≤ standardField word s - standardField word (s + alternateSigma word) ∧
      standardField word s - standardField word (s + alternateSigma word) ≤ 2)
    (hF : ∀ s : tile.sites, standardField word s.1 - standardField word (s.1 + alternateSigma word) ≤ 1 →
      tile.height s = standardField word s.1 + gauge)
    (hG : ∀ s : tile.sites, 1 < standardField word s.1 - standardField word (s.1 + alternateSigma word) →
      tile.height s = standardField word (s.1 + alternateSigma word) + 1 + gauge) :
    tile.Agrees (alternateTarget word) gauge := by
  intro s
  have hw := hwin s.1 s.2
  rw [alternateTarget_eq_min s.1 hw.1 hw.2]
  by_cases hgap : standardField word s.1 - standardField word (s.1 + alternateSigma word) ≤ 1
  · have hle : standardField word s.1 ≤ standardField word (s.1 + alternateSigma word) + 1 := by omega
    rw [min_eq_left hle, hF s hgap]
  · have hlt : standardField word (s.1 + alternateSigma word) + 1 ≤ standardField word s.1 := by omega
    rw [min_eq_right hlt, hG s (by omega)]

end FLatticePaper.Construction
