import FLatticePaper.Plane.Induction.Q3Paragraph8
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.SheetCover

/-! Task 66 (4): the H-web condition `hweb` on the free H cut, `0 ≤ t_p ≤ N + D`.

With `L = d + n` (child), `L_p = D + N` (odd parent), `m = x + y`, `t = n x − d y`, `s = L x + (d − n) y`, `T = d² + 2dn − n²`:
* `L · t_p = L_p · t + ε · m` (every site, from `N d − D n = ε`);
* `T · m = L · s − 2 n · t` (every site);
* `n, d` odd, so `t ≡ m (mod 2)`.
On the free H cut (`z ∈ E`, `t` in the H spectrum) the even sites have `t ∈ [2, L−2]` and `m ∈ [0, L−2]`, the odd sites
have `t ∈ [n, d]` and `m ∈ [0, L−1]`. So `t, m ∈ [0, L−1]`, and the key identity gives `0 ≤ t_p ≤ L_p`.
The bounds on `m` use the `s`-window and parity (no floor/residue argument). W1's `H_endpoint` is the even residue form of the
same identity and agrees with these bounds. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `N d − D n = ε` for the child `(n, d)` of the word. -/
theorem ChildFrame.odd_det_child (frame : ChildFrame) :
    frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = frame.eps := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have hdet := frame.eps_det_even
  rw [hd, hn]
  linear_combination hdet

/-- The key identity `L · t_p = L_p · t + ε · (x + y)` (every site). -/
theorem ChildFrame.key_identity_tp (frame : ChildFrame) (z : Site) :
    (frame.child.den + frame.child.num) * frame.parentTGrade z =
      (frame.parents.odd.den + frame.parents.odd.num) * frame.tGrade z + frame.eps * (z.1 + z.2) := by
  have h := frame.odd_det_child
  unfold ChildFrame.parentTGrade ChildFrame.tGrade
  linear_combination (z.1 + z.2) * h

/-- The `s`-identity `T · (x + y) = L · s − 2 n · t` (every site). -/
theorem ChildFrame.s_identity (frame : ChildFrame) (z : Site) :
    frame.child.periodDenominator * (z.1 + z.2) =
      (frame.child.den + frame.child.num) * frame.sGrade z - 2 * frame.child.num * frame.tGrade z := by
  unfold ChildFrame.sGrade ChildFrame.tGrade Fraction.periodDenominator
  ring

/-- `n x − L y = n (x + y) − t`: the divisibility identity `t ≡ n m (mod L)`. -/
theorem ChildFrame.div_identity (frame : ChildFrame) (z : Site) :
    frame.child.num * (z.1 + z.2) - frame.tGrade z = (frame.child.den + frame.child.num) * z.2 := by
  unfold ChildFrame.tGrade
  ring

/-- The parity of `t` is the parity of `x + y`, since `n` and `d` are odd. -/
theorem ChildFrame.tGrade_mod_two_eq (frame : ChildFrame) (z : Site) :
    frame.tGrade z % 2 = (z.1 + z.2) % 2 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  unfold ChildFrame.tGrade
  have h1 : (frame.child.num * z.1) % 2 = z.1 % 2 := by
    rw [Int.mul_emod, hn]
    simp
  have h2 : (frame.child.den * z.2) % 2 = z.2 % 2 := by
    rw [Int.mul_emod, hd]
    simp
  rw [Int.sub_emod, h1, h2]
  omega

/-- Free H cut, even sites: `t ∈ [2, L−2]`, `s ∈ [0, T + 2n]`, hence `m = x + y ∈ [0, L−2]`. -/
theorem ChildFrame.m_range_even (frame : ChildFrame) (hn : 1 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) (hpar : (frame.child.den + frame.child.num) % 2 = 0) {z : Site}
    (he : EvenSite z) (ht : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2)
    (hs : 0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) :
    0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ frame.child.den + frame.child.num - 2 := by
  have hid := frame.s_identity z
  have hdiv := frame.div_identity z
  have hEv : (z.1 + z.2) % 2 = 0 := he
  have hTdef : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num -
      frame.child.num ^ 2 := rfl
  have hLpos : 0 < frame.child.den + frame.child.num := by omega
  have hnT : frame.child.num * (frame.child.den + frame.child.num - 2) < frame.child.periodDenominator := by
    rw [hTdef]
    nlinarith
  have hT : 0 < frame.child.periodDenominator := by
    nlinarith
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · by_contra hc
    rw [not_le] at hc
    have hm2 : z.1 + z.2 ≤ -2 := by omega
    nlinarith
  · by_contra hc
    rw [not_le] at hc
    have hmL : z.1 + z.2 = frame.child.den + frame.child.num ∨
        frame.child.den + frame.child.num + 2 ≤ z.1 + z.2 := by omega
    rcases hmL with hmL | hmL
    · -- m = L: then t = L (n − y), contradicting 2 ≤ t ≤ L − 2
      rw [hmL] at hdiv
      have htL : frame.tGrade z = (frame.child.den + frame.child.num) * (frame.child.num - z.2) := by
        linear_combination (-1 : ℤ) * hdiv
      rcases le_or_gt (frame.child.num - z.2) 0 with hk | hk
      · nlinarith
      · nlinarith
    · nlinarith

/-- Free H cut, odd sites: `t ∈ [n, d]`, `s ∈ [2 − d + n, T + L − 2]`, hence `m = x + y ∈ [0, L−1]`. -/
theorem ChildFrame.m_range_odd (frame : ChildFrame) (hn : 1 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) (hpar : (frame.child.den + frame.child.num) % 2 = 0) {z : Site}
    (hod : (z.1 + z.2) % 2 = 1) (ht : frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den)
    (hs : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :
    0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ frame.child.den + frame.child.num - 1 := by
  have hid := frame.s_identity z
  have hTdef : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num -
      frame.child.num ^ 2 := rfl
  have hLpos : 0 < frame.child.den + frame.child.num := by omega
  have hT : 0 < frame.child.periodDenominator := by
    rw [hTdef]
    nlinarith
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · by_contra hc
    rw [not_le] at hc
    have hm1 : z.1 + z.2 ≤ -1 := by omega
    nlinarith
  · by_contra hc
    rw [not_le] at hc
    have hm2 : frame.child.den + frame.child.num + 1 ≤ z.1 + z.2 := by omega
    nlinarith

/-- The `t_p` bound from the key identity: `0 ≤ t_p ≤ L_p` when `t, m ∈ [0, L−1]` and `ε = ±1`. -/
theorem tp_bounds_of_key (L Lp t m tp ε : ℤ) (hL : 0 < L) (hLp : 0 < Lp) (ht0 : 0 ≤ t) (ht1 : t ≤ L - 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ L - 1) (hε : ε = 1 ∨ ε = -1) (key : L * tp = Lp * t + ε * m) :
    0 ≤ tp ∧ tp ≤ Lp := by
  rcases hε with rfl | rfl
  · constructor
    · by_contra hc
      rw [not_le] at hc
      nlinarith
    · by_contra hc
      rw [not_le] at hc
      nlinarith
  · constructor
    · by_contra hc
      rw [not_le] at hc
      nlinarith
    · by_contra hc
      rw [not_le] at hc
      nlinarith

/-- **The H-web bound on the free H cut** (`hweb`): `0 ≤ t_p ≤ N + D`. -/
theorem ChildFrame.parentTGrade_bounds_of_freeH (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    0 ≤ frame.parentTGrade z ∧ frame.parentTGrade z ≤ frame.parents.odd.num + frame.parents.odd.den := by
  obtain ⟨hpos, hlt, hgap, -⟩ := frame.child_facts
  have hpar : (frame.child.den + frame.child.num) % 2 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ := frame.linear_facts
    omega
  have hn : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hcp, -, hsp⟩ := hz
  have hkey := frame.key_identity_tp z
  have hε := frame.eps_unit
  have hL : 0 < frame.child.den + frame.child.num := by omega
  have hLp : 0 < frame.parents.odd.den + frame.parents.odd.num := by
    obtain ⟨hD, hN0, -⟩ := frame.valid.odd_bounds
    omega
  have hsub : frame.child.num ≤ frame.child.den := by omega
  by_cases he : EvenSite z
  · have hpc := frame.closedPolygon_even he hcp
    have hcpu := hcp
    unfold ChildFrame.closedPolygon at hcpu
    simp only [Set.mem_setOf_eq, if_pos he] at hcpu
    have hTp := frame.tGrade_mod_two_eq z
    unfold ChildFrame.hSpectrum at hsp
    have hev : (z.1 + z.2) % 2 = 0 := he
    have ht : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
      rcases hsp with ⟨-, h1, h2⟩ | ⟨h0, -, -⟩
      · exact ⟨h1, h2⟩
      · exfalso
        omega
    have hm := frame.m_range_even hn hnd hpar he ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩
    have ht' : 0 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 1 := by
      constructor <;> omega
    have hres := tp_bounds_of_key (frame.child.den + frame.child.num)
      (frame.parents.odd.den + frame.parents.odd.num) (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z)
      frame.eps hL hLp ht'.1 ht'.2 hm.1 (by omega) hε hkey
    exact ⟨hres.1, by linarith [hres.2]⟩
  · have hcpu := hcp
    unfold ChildFrame.closedPolygon at hcpu
    simp only [Set.mem_setOf_eq, if_neg he] at hcpu
    have hTp := frame.tGrade_mod_two_eq z
    unfold ChildFrame.hSpectrum at hsp
    have hod : (z.1 + z.2) % 2 = 1 := by
      unfold EvenSite at he
      omega
    have ht : frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
      rcases hsp with ⟨h0, -, -⟩ | ⟨-, h1, h2⟩
      · exfalso
        omega
      · exact ⟨h1, h2⟩
    have hm := frame.m_range_odd hn hnd hpar hod ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩
    have ht' : 0 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 1 := by
      constructor <;> omega
    have hres := tp_bounds_of_key (frame.child.den + frame.child.num)
      (frame.parents.odd.den + frame.parents.odd.num) (frame.tGrade z) (z.1 + z.2) (frame.parentTGrade z)
      frame.eps hL hLp ht'.1 ht'.2 hm.1 hm.2 hε hkey
    exact ⟨hres.1, by linarith [hres.2]⟩

/-- The H-web condition at a free H root of the word: `HRootWeb N D t_p` (`HRootWeb_iff_bounds`). -/
theorem hweb_of_freeH {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {z : Site}
    (hz : z ∈ (frameAt word).freeH) :
    HRootWeb (frameAt word).parents.odd.num (frameAt word).parents.odd.den ((frameAt word).parentTGrade z) := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨hD, hN0, hND⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND' : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  rw [HRootWeb_iff_bounds hN hND']
  have hb := (frameAt word).parentTGrade_bounds_of_freeH hz
  exact hb

end FLatticePaper.Induction
