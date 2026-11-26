import FLatticePaper.Plane.Induction.BottomTopEmpty
import FLatticePaper.Plane.Induction.AlignedClassSite

/-! # No site has a bottom witness and a top-type witness (site level, step (4), bottom case)

If a site `c` has a free H point `v` within one pixel and a free H point `w - V` (with `w` within one pixel) then the grades give
`BottomTopEmpty.bot_top_empty`, a contradiction. This needs no strictness of `c`. -/

namespace FLatticePaper.BottomExcl

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CrossingLattice
  FLatticePaper.AlignedClassGrade FLatticePaper.AlignedClassSite FLatticePaper.BottomTopEmpty

theorem no_bottom_top {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (c : Site)
    (hB : ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeHn n d v)
    (hT : ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧ freeHn n d (w.1 - (n - d), w.2 - (n + d))) :
    False := by
  have hT3 := period_ge n d (w1T n d) hn1 hnd (w1T_eq n d)
  obtain ⟨v, hv1, hv2, hvF⟩ := hB
  obtain ⟨w, hw1, hw2, hwF⟩ := hT
  have hb1 := abs_le.mp hv1
  have hb2 := abs_le.mp hv2
  have hb3 := abs_le.mp hw1
  have hb4 := abs_le.mp hw2
  -- the bottom witness: a closed site with `hSp` in the grades of `v`
  have hvC := (closedRect_iff_ClG hn hd v).mp hvF.1
  have hvS := hvF.2.2
  rw [w1t_diff n d c v, w1s_diff n d c v] at hvC
  rw [w1t_diff n d c v] at hvS
  -- the top witness: `w - V` is closed with `hSp` at the grade `w1t w + T`
  have eV : w1t n d (w.1 - (n - d), w.2 - (n + d)) = w1t n d w + w1T n d := by
    unfold w1t w1T; ring
  have eS : w1s n d (w.1 - (n - d), w.2 - (n + d)) = w1s n d w := by
    unfold w1s; ring
  have hwC := (closedRect_iff_ClG hn hd _).mp hwF.1
  rw [eV, eS, w1t_diff n d c w, w1s_diff n d c w] at hwC
  have hwS := hwF.2.2
  rw [eV, w1t_diff n d c w] at hwS
  exact bot_top_empty n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hT3
    ⟨v.1 - c.1, v.2 - c.2, hb1.1, hb1.2, hb2.1, hb2.2, hvC, hvS⟩
    ⟨w.1 - c.1, w.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, hwC, hwS⟩

end FLatticePaper.BottomExcl
