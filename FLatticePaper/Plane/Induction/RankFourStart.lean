import FLatticePaper.Plane.Induction.MinusRowRemoval
import FLatticePaper.Plane.Induction.Rank4Fort
import FLatticePaper.Plane.Induction.ConeBoundary

/-! # The rank-4 start in the C slot of the row removal

`rank4_start_not_mem`: for an odd black east-free H entry `e = hAt(m−d) = z − U` (`z = hpath m`), under the row induction (every
earlier row entry is outside the restricted fort `S`), the rank-4 start `e + (1,2) = z + (1,2) − U` is outside `S`.
It is `Rank4Fort.rank4_at` with `Eset` the row prefix (`MinusRowWiring.earlierAt`), `hG` from `ConeBoundary.hG_of_faces`
(the row inputs `hEH_row`, `hEV_row`), and the minimal cone height `exists_minimal_K`. The parent break is `r = odd.den + odd.num`. -/

namespace FLatticePaper.RankFourStart

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.MinusRowWiring FLatticePaper.EasyHRank FLatticePaper.OddAxialRank FLatticePaper.ConeBoundary
open FLatticePaper.Rank4Fort

/-- A minimal cone height: `n K ∈ [d + 2n − 1, d + 3n − 2]`. -/
theorem exists_minimal_K (num den : ℤ) (hn : 1 ≤ num) (hnd : 2 * num ≤ den) :
    ∃ K : ℕ, 3 ≤ K ∧ den + 2 * num - 1 ≤ num * (K : ℤ) ∧ num * (K : ℤ) ≤ den + 3 * num - 2 := by
  have hn0 : (0 : ℤ) < num := by omega
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = (den + 3 * num - 2) / num := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (den + 3 * num - 2) % num := ⟨_, rfl⟩
  have h1 : num * K0 + r = den + 3 * num - 2 := by
    rw [hK0, hr, Int.emod_def]
    ring
  have h2 : 0 ≤ r := by
    rw [hr]
    exact Int.emod_nonneg _ (ne_of_gt hn0)
  have h3 : r < num := by
    rw [hr]
    exact Int.emod_lt_of_pos _ hn0
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    exact Int.ediv_nonneg (by omega) (le_of_lt hn0)
  have hK3 : 3 ≤ K0 := by
    by_contra hc
    push Not at hc
    have hc2 : K0 ≤ 2 := by omega
    have hc3 : num * K0 ≤ num * 2 := mul_le_mul_of_nonneg_left hc2 (le_of_lt hn0)
    omega
  refine ⟨K0.toNat, by omega, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hK0nn]
    omega
  · rw [Int.toNat_of_nonneg hK0nn]
    omega

/-- **The rank-4 start is outside the fort.** Under the row induction `hIH`, the start `e + (1,2)` of the odd black east-free
H entry `e = hAt(m−d)` is not in the restricted fort `S`. -/
theorem rank4_start_not_mem (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num) (hr0 : 0 ≤ frame.parents.odd.den + frame.parents.odd.num)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hblack : laplacian F ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) = -1)
    {K : ℕ} (hK3 : 3 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    (hIH : ∀ x ∈ earlierAt frame (frame.parents.odd.den + frame.parents.odd.num)
      (entryPos frame (frame.parents.odd.den + frame.parents.odd.num) m), x ∉ S) :
    RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) ∉ S := by
  set z := HChain.hpath frame m with hz
  set r := frame.parents.odd.den + frame.parents.odd.num with hr
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : z.1 < frame.child.den := by omega
  have hx2 : 2 ≤ z.1 := by omega
  have hzt := odd_t_range frame hzfree hodd hx2 hzd
  have hG := hG_of_faces frame (K := K) hx2 hzd hzt hn1 hnd hNo hKu (earlierAt frame r (entryPos frame r m))
    (fun k h1 h2 => hEH_row frame r m k (by omega) h2)
    (fun k h1 h2 h3 => hEV_row frame r hr0 m k h1 h2 h3)
  have hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1 := by
    nlinarith
  have hbig := rank4_at frame F hP hsig hs hnd hZ K (by omega) hK3 hKs hKr hcap hS
    (earlierAt frame r (entryPos frame r m)) hIH z hzfree hodd hx2 hzd hblack hG
  have he : RowAt.hAt frame ((m : ℤ) - frame.child.den) = z - RowAt.Uvec frame :=
    EasyHRank.hAt_sub_den frame (m := m) (by omega)
  have heq : RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) =
      (z.1 + 1, z.2 + 2) - RowAt.Uvec frame := by
    rw [he]
    exact Prod.ext (by simp only [Prod.fst_add, Prod.fst_sub]; ring) (by simp only [Prod.snd_add, Prod.snd_sub]; ring)
  rw [heq]
  exact hbig

end FLatticePaper.RankFourStart
