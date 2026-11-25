import FLatticePaper.Plane.Induction.HWeb
import FLatticePaper.Plane.Induction.TpRange
import FLatticePaper.Plane.Induction.W1ArcBottom

/-! Task w3, step 1(b)(B): the parent t-grade range of the transport query, from the free H window of the word.

For a free H point `z` of a child frame, the query is `x = z − sheetShift`, with `t_p(x) = t_p(z) − (1 − W) ε`
(`parentTGrade_sheetShift`). The integer core is `TpRange`; here the free H bounds `t, u` are taken from the `HWeb` branches.
The result (Q29's table): phase zero, even `x`: `1 ≤ t_p ≤ r`; odd `x`: `N + 1 ≤ t_p ≤ D`. Phase one, even: `1 ≤ t_p ≤ r`;
odd: `N ≤ t_p ≤ D + 1`. -/

namespace FLatticePaper.TpFrame

open Farey FLatticePaper FLatticePaper.Induction

/-- The parent t-grade is linear: `t_p(a − b) = t_p a − t_p b`. -/
theorem parentTGrade_sub (frame : ChildFrame) (a b : Site) :
    frame.parentTGrade (a - b) = frame.parentTGrade a - frame.parentTGrade b := by
  unfold ChildFrame.parentTGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Free H, even sites:** `t ∈ [2, L−2]` and `u = x + y ∈ [0, L−2]`. -/
theorem freeH_even_tu (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (he : EvenSite z) :
    (2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∧
      (0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ frame.child.den + frame.child.num - 2) := by
  obtain ⟨hpos, hlt, hgap, -⟩ := frame.child_facts
  have hpar : (frame.child.den + frame.child.num) % 2 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ := frame.linear_facts
    omega
  have hn : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hcp, -, hsp⟩ := hz
  have hcpu := hcp
  unfold ChildFrame.closedPolygon at hcpu
  simp only [Set.mem_setOf_eq, if_pos he] at hcpu
  have hTp := frame.tGrade_mod_two_eq z
  have hev : (z.1 + z.2) % 2 = 0 := he
  unfold ChildFrame.hSpectrum at hsp
  have ht : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hsp with ⟨-, h1, h2⟩ | ⟨h0, -, -⟩
    · exact ⟨h1, h2⟩
    · exfalso
      omega
  exact ⟨ht, frame.m_range_even hn hnd hpar he ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩⟩

/-- **Free H, odd sites:** `t ∈ [n, d]` and `u = x + y ∈ [0, L−1]`. -/
theorem freeH_odd_tu (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (ho : ¬ EvenSite z) :
    (frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den) ∧
      (0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ frame.child.den + frame.child.num - 1) := by
  obtain ⟨hpos, hlt, hgap, -⟩ := frame.child_facts
  have hpar : (frame.child.den + frame.child.num) % 2 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ := frame.linear_facts
    omega
  have hn : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hcp, -, hsp⟩ := hz
  have hcpu := hcp
  unfold ChildFrame.closedPolygon at hcpu
  simp only [Set.mem_setOf_eq, if_neg ho] at hcpu
  have hTp := frame.tGrade_mod_two_eq z
  have hod : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at ho
    omega
  unfold ChildFrame.hSpectrum at hsp
  have ht : frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
    rcases hsp with ⟨h0, -, -⟩ | ⟨-, h1, h2⟩
    · exfalso
      omega
    · exact ⟨h1, h2⟩
  exact ⟨ht, frame.m_range_odd hn hnd hpar hod ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩⟩

/-- **The transport query's parent t-grade, by phase and parity.** For a free H point `z` of the child frame and the query
`x = z − sheetShift`: phase zero (`ε = −1`) gives `t_p(x) ∈ [1, r]` (even) and `[N+1, D]` (odd); phase one (`ε = 1`) gives
`t_p(x) ∈ [1, r]` (even) and `[N, D+1]` (odd). -/
theorem tp_query_bounds (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    (frame.eps = -1 → (EvenSite z →
        1 ≤ frame.parentTGrade (z - frame.sheetShift) ∧
          frame.parentTGrade (z - frame.sheetShift) ≤ frame.parents.odd.den + frame.parents.odd.num) ∧
      (¬ EvenSite z →
        frame.parents.odd.num + 1 ≤ frame.parentTGrade (z - frame.sheetShift) ∧
          frame.parentTGrade (z - frame.sheetShift) ≤ frame.parents.odd.den)) ∧
    (frame.eps = 1 → (EvenSite z →
        1 ≤ frame.parentTGrade (z - frame.sheetShift) ∧
          frame.parentTGrade (z - frame.sheetShift) ≤ frame.parents.odd.den + frame.parents.odd.num) ∧
      (¬ EvenSite z →
        frame.parents.odd.num ≤ frame.parentTGrade (z - frame.sheetShift) ∧
          frame.parentTGrade (z - frame.sheetShift) ≤ frame.parents.odd.den + 1)) := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ : 0 < frame.parents.odd.den ∧ 0 ≤ frame.parents.odd.num ∧
      frame.parents.odd.num ≤ frame.parents.odd.den ∧ (frame.parents.odd.den + frame.parents.odd.num) % 2 = 1 := by
    have hb := frame.valid.odd_bounds
    have hp := frame.valid.odd_parity
    unfold Fraction.InUnitInterval at hb
    unfold Fraction.Odd at hp
    exact ⟨hb.1, hb.2.1, hb.2.2, by omega⟩
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  have hL : 0 < frame.child.den + frame.child.num := by omega
  have hL2 : 2 ≤ frame.child.den + frame.child.num := by omega
  have hdet := frame.odd_det_child
  have key := frame.key_identity_tp z
  have hshift := W1ArcBottom.parentTGrade_sheetShift frame
  have hsub := parentTGrade_sub frame z frame.sheetShift
  have hbnd := frame.parentTGrade_bounds_of_freeH hz
  constructor
  · intro hε
    have hW : frame.phaseW = 0 := by
      unfold ChildFrame.phaseW
      rw [hε]
      norm_num
    have hsh : frame.parentTGrade frame.sheetShift = -1 := by
      rw [hshift, hW, hε]
      norm_num
    rw [hsub, hsh]
    have key' := key
    rw [hε] at key'
    have hdet' := hdet
    rw [hε] at hdet'
    constructor
    · intro he
      obtain ⟨⟨ht0, ht1⟩, ⟨hu0, hu1⟩⟩ := freeH_even_tu frame hz he
      have h := TpRange.tp_even_W0 frame.parents.odd.den frame.parents.odd.num (frame.child.den + frame.child.num)
        (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z) hDpos hN0 hL key' ht1 hu0 hbnd.1
      constructor <;> omega
    · intro ho
      obtain ⟨⟨hn1, hd1⟩, ⟨hu0, hu1⟩⟩ := freeH_odd_tu frame hz ho
      have hrn : (frame.parents.odd.den + frame.parents.odd.num) * frame.child.num =
          frame.parents.odd.num * (frame.child.den + frame.child.num) + 1 := by
        linear_combination (-1 : ℤ) * hdet'
      have hrd : (frame.parents.odd.den + frame.parents.odd.num) * frame.child.den =
          frame.parents.odd.den * (frame.child.den + frame.child.num) - 1 := by
        linear_combination hdet'
      have h := TpRange.tp_odd_W0 frame.parents.odd.den frame.parents.odd.num (frame.child.den + frame.child.num)
        frame.child.num frame.child.den (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z) hDpos hN0 hL hrn hrd
        key' hn1 hd1 hu0 hu1
      constructor <;> omega
  · intro hε
    have hW : frame.phaseW = 1 := by
      unfold ChildFrame.phaseW
      rw [hε]
      norm_num
    have hsh : frame.parentTGrade frame.sheetShift = 0 := by
      rw [hshift, hW]
      norm_num
    rw [hsub, hsh]
    have key' := key
    rw [hε] at key'
    have hdet' := hdet
    rw [hε] at hdet'
    constructor
    · intro he
      obtain ⟨⟨ht0, ht1⟩, ⟨hu0, hu1⟩⟩ := freeH_even_tu frame hz he
      have h := TpRange.tp_even_W1 frame.parents.odd.den frame.parents.odd.num (frame.child.den + frame.child.num)
        (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z) hDpos hN0 hL key' ht0 ht1 hu0 hu1
      constructor <;> omega
    · intro ho
      obtain ⟨⟨hn1, hd1⟩, ⟨hu0, hu1⟩⟩ := freeH_odd_tu frame hz ho
      have hrn : (frame.parents.odd.den + frame.parents.odd.num) * frame.child.num =
          frame.parents.odd.num * (frame.child.den + frame.child.num) - 1 := by
        linear_combination (-1 : ℤ) * hdet'
      have hrd : (frame.parents.odd.den + frame.parents.odd.num) * frame.child.den =
          frame.parents.odd.den * (frame.child.den + frame.child.num) + 1 := by
        linear_combination hdet'
      have h := TpRange.tp_odd_W1 frame.parents.odd.den frame.parents.odd.num (frame.child.den + frame.child.num)
        frame.child.num frame.child.den (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z) hDpos hN0 hL2 hrn hrd
        key' hn1 hd1 hu0 hu1
      constructor <;> omega

end FLatticePaper.TpFrame
