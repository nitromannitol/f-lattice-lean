import FLatticePaper.Plane.Induction.Rank4Fort
import FLatticePaper.Plane.Induction.ConeBoundary
import FLatticePaper.Plane.Induction.HChainEta

/-! # The rank-4 start exclusion for an arbitrary sign η

`rank4_at_eta` is `Rank4Fort.rank4_at` with the restricted-fort hypothesis for `permitsQ1 frame F η`; the fan argument only uses the
η-generic `fortAt_nonfree_of_restricted`. `hG_gen` is `ConeBoundary.hG_of_faces` with the V bound and the boundary V-index hypothesis
as inputs (the minus bound `brk` and the plus bound `L − r − 2` are both instances). -/

namespace FLatticePaper.GenStart

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.Rank4Fort FLatticePaper.ConeBoundary FLatticePaper.CapRay FLatticePaper.FanPropagation
open FLatticePaper.ContactCone FLatticePaper.RestrictedFan FLatticePaper.FanTerminal FLatticePaper.ConeTerminal
open FLatticePaper.OddAxialRank

theorem rank4_at_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (K : ℕ) (hK2 : 2 ≤ K) (hK3 : 3 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F η) S)
    (Eset : Set Site) (hE : ∀ e ∈ Eset, e ∉ S)
    (z : Site) (hzfree : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den)
    (hblack : laplacian F (z.1 + 1, z.2 + 1) = -1)
    (hG : ∀ x i : Site, (frame.openRect x ∧ CapRay.ConeRoot z K x) → (i = incomingNeg x ∨ i = incomingPos x) →
      i ∈ frame.closedPolygon → ¬ frame.openRect i → ∃ e ∈ Eset, i = e + RowAt.Uvec frame) :
    (z.1 + 1, z.2 + 2) - RowAt.Uvec frame ∉ S := by
  intro h
  have hrange := OddAxialRank.odd_t_range frame hzfree hodd hx2 hxd
  have hstart := start_F_value frame hP hZ hodd hrange.1 hrange.2 hblack
  have hPw := start_open_cone frame hd2 hzfree hodd hx2 hxd hK3
  have hper : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c :=
    fun c i j => laplacian_add_combine hP.periods c i j
  have hv0S : (z.1 + 1, z.2 + 2) ∈ shiftSet (RowAt.Uvec frame) S := by
    show (z.1 + 1, z.2 + 2) - RowAt.Uvec frame ∈ S
    exact h
  have hFS' : FortAt (Nonfree frame) F (shiftSet (RowAt.Uvec frame) S) :=
    shiftSet_fortAt frame hper (fortAt_nonfree_of_restricted frame hS)
  have hPN : ∀ x, (frame.openRect x ∧ CapRay.ConeRoot z K x) → Nonfree frame x :=
    fun x hx => strictInterior_nonfree frame ((W1Exit.openRect_iff frame x).1 hx.1)
  obtain ⟨next, hr⟩ := fan_path_exists_fortAt (P := fun x => frame.openRect x ∧ CapRay.ConeRoot z K x) hFS' hPN
    (parabola_binary z.2) (fun w hw => parabola_lap_even z.2 w hw)
    (cone_window frame hP hsig hs K hcap z hrange.1)
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr (cone_finite frame z K)
    ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩
  cases k with
  | zero => exact absurd hPw (by simpa using hk)
  | succ k' =>
    have hpred := hj k' (Nat.lt_succ_self k')
    have hsucc : next^[k' + 1] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩
        = next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩) :=
      Function.iterate_succ_apply' next k' _
    rw [hsucc] at hk
    have hrk := hr _ hpred
    have hcl : (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 ∈ frame.closedPolygon :=
      FLatticePaper.W1Exit.rectInputs frame _ hpred.1 _ hrk.2
    have hout : ¬ frame.openRect (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 :=
      fun hopen => hk (fan_next_P frame hP hsig hs K hK2 hKs hKr hcap z hrange.1 _ _ hpred hrk.2 hrk.1 hopen
        (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).2.2)
    obtain ⟨e, he, heq⟩ := hG _ _ hpred hrk.2 hcl hout
    have hmem : (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 - RowAt.Uvec frame ∈ S :=
      (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).2.1
    rw [heq, add_sub_cancel_right] at hmem
    exact hE e he hmem


/-- **The boundary claim with a general V bound.** Its V-index hypothesis `hVidx` is the input that the minus bound `brk` and the
plus bound `L − r − 2` each instantiate. -/
theorem hG_gen (frame : ChildFrame) {z : Site} {K : ℕ} (hz1 : 2 ≤ z.1)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (Eset : Set Site) (B : ℤ)
    (hEH : ∀ k : ℕ, z.1 ≤ (k : ℤ) → (k : ℤ) < frame.child.den →
      HChain.hpath frame k - RowAt.Uvec frame ∈ Eset)
    (hEV : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) → (k : ℤ) ≤ B →
      VChain.vpath frame k ∈ Eset)
    (hVidx : ∀ x i : Site, frame.openRect x → CapRay.ConeRoot z K x → EvenSite x → i = incomingPos x →
      i ∈ frame.closedPolygon → ¬ frame.openRect i → 1 ≤ x.2 - frame.child.num ∧ x.2 - frame.child.num ≤ B) :
    ∀ x i : Site, (frame.openRect x ∧ CapRay.ConeRoot z K x) → (i = incomingNeg x ∨ i = incomingPos x) →
      i ∈ frame.closedPolygon → ¬ frame.openRect i → ∃ e ∈ Eset, i = e + RowAt.Uvec frame := by
  rintro x i ⟨hx, hcone⟩ hi hiC hiopen
  by_cases hiE : EvenSite i
  · obtain ⟨k, hk1, hk2, hk⟩ := H_label frame hz1 hzt hn1 hnd hx hcone hi hiE hiC hiopen
    exact ⟨_, hEH k hk1 hk2, by rw [hk, sub_add_cancel]⟩
  · obtain ⟨k, hkL, hkx, hki⟩ := V_label frame hz1 hzt hn1 hnd hx hcone hi hiE hiC hiopen
    have hxe := odd_input_even_x hi hiE
    obtain ⟨hpos, _⟩ := odd_input_V frame hz1 hzt hn1 hnd hx hcone hi hiE hiopen
    obtain ⟨hr1, hr2⟩ := hVidx x i hx hcone hxe hpos hiC hiopen
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by omega
    have hk2 : (k : ℤ) ≤ B := by omega
    exact ⟨_, hEV k hkL hk1 hk2, hki⟩

/-- **The rank-4 start is outside the fort** for an arbitrary sign η, with an arbitrary earlier set `Eset` (its entries outside
`S`) and the boundary claim from `hG_gen`. -/
theorem rank4_start_gen (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hblack : laplacian F ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) = -1)
    {K : ℕ} (hK3 : 3 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F η) S)
    (Eset : Set Site) (hE : ∀ e ∈ Eset, e ∉ S) (B : ℤ)
    (hEH : ∀ k : ℕ, ((m : ℤ) + 1 ≤ (k : ℤ)) → (k : ℤ) < frame.child.den →
      HChain.hpath frame k - RowAt.Uvec frame ∈ Eset)
    (hEV : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) → (k : ℤ) ≤ B →
      VChain.vpath frame k ∈ Eset)
    (hVidx : ∀ x i : Site, frame.openRect x → CapRay.ConeRoot (HChain.hpath frame m) K x → EvenSite x →
      i = incomingPos x → i ∈ frame.closedPolygon → ¬ frame.openRect i →
      1 ≤ x.2 - frame.child.num ∧ x.2 - frame.child.num ≤ B) :
    RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) ∉ S := by
  set z := HChain.hpath frame m with hz
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : z.1 < frame.child.den := by omega
  have hx2 : 2 ≤ z.1 := by omega
  have hzt := odd_t_range frame hzfree hodd hx2 hzd
  have hG := hG_gen frame (K := K) hx2 hzt hn1 hnd Eset B
    (fun k h1 h2 => hEH k (by omega) h2) hEV hVidx
  have hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1 := by
    nlinarith
  have hbig := rank4_at_eta frame F η hP hsig hs hnd hZ K (by omega) hK3 hKs hKr hcap hS Eset hE z hzfree
    hodd hx2 hzd hblack hG
  have he : RowAt.hAt frame ((m : ℤ) - frame.child.den) = z - RowAt.Uvec frame :=
    EasyHRank.hAt_sub_den frame (m := m) (by omega)
  have heq : RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) =
      (z.1 + 1, z.2 + 2) - RowAt.Uvec frame := by
    rw [he]
    exact Prod.ext (by simp only [Prod.fst_add, Prod.fst_sub]; ring) (by simp only [Prod.snd_add, Prod.snd_sub]; ring)
  rw [heq]
  exact hbig

end FLatticePaper.GenStart
