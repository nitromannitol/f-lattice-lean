import FLatticePaper.Plane.Induction.RegionalCompat
import FLatticePaper.Plane.Induction.AllBranchFan
import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.DeckForced

/-! # The reflected contact fan: the forced west arrow at the black `z+SW` roots (Q32 he1, source §B hard midpoint)

`reflH z = U + I − z` (U = (d,n), I = (1,−1)) sends the root `z` to the odd free H point `x' = reflH z`, the start `x'+N` of the
all-branch contact fan to `z+S`, and `x'+NE` to `z+SW`. Given the field symmetry `G (reflH y) = G y` (named), a forced edge of the fan
start `x'+N` (a white contact of the cone of base `x'`, its east input forced) transports to `z+S → z+SW`.

Named inputs: the all-slope data `hsig`, `hs`, `hcap` (the cone window's ray, as in `CapRay.cone_window`), the field symmetry `hsym`,
and the start contact `G (z+S) = 0`. -/

namespace FLatticePaper.ReflectedFan

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.AndOrRank
  FLatticePaper.FanCompat FLatticePaper.AllBranchFan FLatticePaper.CapRay FLatticePaper.ContactCone
  FLatticePaper.FanAcyclic FLatticePaper.FanPropagation

/-- The reflection `reflH z = U + I − z` with `U = (d, n)`, `I = (1, −1)`. -/
def reflH (frame : ChildFrame) (z : Site) : Site :=
  (frame.child.den + 1 - z.1, frame.child.num - 1 - z.2)

theorem reflH_reflH (frame : ChildFrame) (z : Site) : reflH frame (reflH frame z) = z := by
  unfold reflH
  refine Prod.ext ?_ ?_
  · try dsimp only
    try omega
  · try dsimp only
    try omega

theorem evenSite_reflH (frame : ChildFrame) (z : Site) : EvenSite (reflH frame z) ↔ EvenSite z := by
  have h : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  unfold EvenSite reflH
  dsimp only
  omega

theorem incomingNeg_reflH (frame : ChildFrame) (z : Site) :
    incomingNeg (reflH frame z) = reflH frame (incomingPos z) := by
  unfold incomingNeg incomingPos
  by_cases hz : EvenSite z
  · rw [if_pos ((evenSite_reflH frame z).mpr hz), if_pos hz]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  · rw [if_neg (fun h => hz ((evenSite_reflH frame z).mp h)), if_neg hz]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega

theorem incomingPos_reflH (frame : ChildFrame) (z : Site) :
    incomingPos (reflH frame z) = reflH frame (incomingNeg z) := by
  unfold incomingNeg incomingPos
  by_cases hz : EvenSite z
  · rw [if_pos ((evenSite_reflH frame z).mpr hz), if_pos hz]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  · rw [if_neg (fun h => hz ((evenSite_reflH frame z).mp h)), if_neg hz]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega

theorem laplacian_reflH {G : Field} (frame : ChildFrame) (hsym : ∀ y, G (reflH frame y) = G y) (z : Site) :
    laplacian G (reflH frame z) = laplacian G z := by
  unfold laplacian
  simp only [incomingNeg_reflH, incomingPos_reflH, hsym]
  ring

theorem reflH_mem_square_iff (frame : ChildFrame) {a b : ℤ} (c : Site) :
    reflH frame c ∈ squareCorners (frame.child.den - a) (frame.child.num - 2 - b) ↔ c ∈ squareCorners a b := by
  rw [mem_squareCorners_iff, mem_squareCorners_iff]
  unfold reflH
  dsimp only
  omega

/-- **Forced edges are carried by the reflection** (`reflH` swaps the two inputs and maps unit squares to unit squares). -/
theorem forcedEdge_reflH {frame : ChildFrame} {G : Field} (hsym : ∀ y, G (reflH frame y) = G y)
    {c i : Site} (h : ForcedEdge G (fun _ _ => False) c i) :
    ForcedEdge G (fun _ _ => False) (reflH frame c) (reflH frame i) := by
  induction h with
  | seed hs => exact (hs : False).elim
  | @unit a b c' o inside hc hw ho hout hin hforced ih =>
    refine ForcedEdge.unit (a := frame.child.den - a) (b := frame.child.num - 2 - b)
      (inside := fun x => reflH frame (inside (reflH frame x))) ((reflH_mem_square_iff frame c').mpr hc) ?_ ?_ ?_ ?_ ?_
    · rw [laplacian_reflH frame hsym]
      exact hw
    · rcases ho with h1 | h1
      · right
        rw [h1, incomingPos_reflH]
      · left
        rw [h1, incomingNeg_reflH]
    · intro hmem
      exact hout ((reflH_mem_square_iff frame o).mp hmem)
    · intro c'' hc'' hne
      obtain ⟨x, rfl⟩ : ∃ x, c'' = reflH frame x := ⟨reflH frame c'', (reflH_reflH frame c'').symm⟩
      have hx : x ∈ squareCorners a b := (reflH_mem_square_iff frame x).mp hc''
      have hxne : x ≠ c' := by
        intro h'
        apply hne
        rw [h']
      simp only [reflH_reflH]
      rcases hin x hx hxne with hb' | ⟨h0, hinSq, hinIn⟩
      · left
        rw [laplacian_reflH frame hsym]
        exact hb'
      · right
        refine ⟨by rw [laplacian_reflH frame hsym]; exact h0, (reflH_mem_square_iff frame _).mpr hinSq, ?_⟩
        rcases hinIn with h2 | h2
        · right
          rw [h2, incomingPos_reflH]
        · left
          rw [h2, incomingNeg_reflH]
    · intro c'' hc'' hne hl
      obtain ⟨x, rfl⟩ : ∃ x, c'' = reflH frame x := ⟨reflH frame c'', (reflH_reflH frame c'').symm⟩
      have hx : x ∈ squareCorners a b := (reflH_mem_square_iff frame x).mp hc''
      have hxne : x ≠ c' := by
        intro h'
        apply hne
        rw [h']
      have hl' : laplacian G x = 0 := by
        rw [← laplacian_reflH frame hsym]
        exact hl
      simp only [reflH_reflH]
      exact ih x hx hxne hl'

/-- Both inputs of a fan contact with the parabola Laplacian are contacts (the excesses are nonnegative and sum to zero). -/
theorem fan_both_inputs {frame : ChildFrame} {G : Field} {b : Site} {K : ℕ}
    (hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) G (fun i => parabolaField b.2 i))
    {x : Site} (hx : x ∈ contactFan frame G b K)
    (hl : laplacian G x = laplacian (parabolaField b.2) x) :
    G (incomingNeg x) = parabolaField b.2 (incomingNeg x) ∧
      G (incomingPos x) = parabolaField b.2 (incomingPos x) := by
  obtain ⟨hcone, hc⟩ := mem_contactFan.mp hx
  have key := excess_sum (F := G) (m := parabolaField b.2) hc
  rw [hl] at key
  have hn : parabolaField b.2 (incomingNeg x) ≤ G (incomingNeg x) := hwin x hcone (incomingNeg x) (Or.inl rfl)
  have hp : parabolaField b.2 (incomingPos x) ≤ G (incomingPos x) := hwin x hcone (incomingPos x) (Or.inr rfl)
  constructor <;> omega

/-- **The fan start is forced to its east input.** The all-branch contact fan of the cone of base `b` is a region for
`RegionalCompat.regional_forced`: even contacts are white with the east input a contact (rank drops east), odd black contacts keep both
vertical contacts, odd white contacts keep one; the fan is closed (contact inputs in the open rectangle lie in the fan,
`contactFan_mem_of_input`) and acyclic (`fanRank`). A forced edge out of the even fan start is therefore its east edge. -/
theorem fan_start_forced {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) {K : ℕ}
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    {b start : Site} (hb : frame.child.num + 2 ≤ frame.tGrade b)
    (hstart : start ∈ contactFan frame G b K) (heven : EvenSite start)
    {o : Site}
    (ho : ForcedEdgeIn G (FLatticePaper.W1.StrictInterior frame.child.num frame.child.den) (fun _ _ => False) start o) :
    o = incomingPos start := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot b K x) G (fun i => parabolaField b.2 i) :=
    cone_window frame hP hsig hs K hcap b hb
  have hreg := FLatticePaper.RegionalCompat.regional_forced (F := G)
    (R := FLatticePaper.W1.StrictInterior frame.child.num frame.child.den)
    (S := fun x => x ∈ contactFan frame G b K)
    (C := fun x u => (EvenSite x ∧ u = incomingPos x ∧ G u = parabolaField b.2 u) ∨
      (¬ EvenSite x ∧ (u = incomingNeg x ∨ u = incomingPos x) ∧ G u = parabolaField b.2 u))
    (r := fanRank)
    (by
      intro x u hCu
      rcases hCu with ⟨he, hu, -⟩ | ⟨hne, hu, -⟩
      · rw [hu]
        exact fanRank_east_of_even x he
      · exact fanRank_vertical_of_odd x hne u hu)
    (by
      intro x u hx hCu hR
      rcases hCu with ⟨he, hu, hcu⟩ | ⟨hne, hu, hcu⟩
      · exact contactFan_mem_of_input hP hsig hs hK2 hKs hKr hcap hb hx (Or.inr hu) (fun _ => hu)
          ((FLatticePaper.W1Exit.openRect_iff frame u).mpr hR) hcu
      · exact contactFan_mem_of_input hP hsig hs hK2 hKs hKr hcap hb hx hu (fun h => absurd h hne)
          ((FLatticePaper.W1Exit.openRect_iff frame u).mpr hR) hcu)
    (by
      intro x hx hl u hu
      have hodd : ¬ EvenSite x := by
        intro he
        have h0 := contactFan_even_white hbin hwin hx he
        rw [hl] at h0
        norm_num at h0
      have hsum := fan_both_inputs hwin hx (by rw [hl, parabola_lap_odd b.2 x hodd])
      rcases hu with rfl | rfl
      · exact Or.inr ⟨hodd, Or.inl rfl, hsum.1⟩
      · exact Or.inr ⟨hodd, Or.inr rfl, hsum.2⟩)
    (by
      intro x hx hl
      by_cases he : EvenSite x
      · have hsum := fan_both_inputs hwin hx (by rw [hl, parabola_lap_even b.2 x he])
        exact ⟨incomingPos x, Or.inl ⟨he, rfl, hsum.2⟩, Or.inr rfl⟩
      · obtain ⟨y, hy, hyc⟩ := contactFan_odd_input hwin hx he hl
        exact ⟨y, Or.inr ⟨he, hy, hyc⟩, hy⟩)
    ho hstart
  rcases hreg with ⟨-, h, -⟩ | ⟨hne, -⟩
  · exact h
  · exact absurd heven hne

/-- The start `reflH z + N` of the reflected root is strict-interior (the window arithmetic of `SI_seV`, with `t ↦ n − t(z)`,
`s ↦ T + d + n − s(z)`). -/
theorem start_SI {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z)
    (hne : z ≠ frame.hLast) (hbt : frame.child.num + 2 ≤ frame.tGrade z) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den
      ((reflH frame z).1, (reflH frame z).2 + 1) := by
  have ht := FLatticePaper.ShortRoute.freeH_tGrade_add_two_le frame hz hodd hne
  obtain ⟨-, hs2⟩ := FLatticePaper.ShortRoute.freeH_sGrade_bounds frame hz
  have hsbig := FLatticePaper.WestForced.sGrade_odd_H_big hz hodd hne hbt
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hev : EvenSite ((reflH frame z).1, (reflH frame z).2 + 1) := by
    unfold EvenSite reflH
    dsimp only
    unfold EvenSite at hodd
    omega
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hP]
    rfl
  have hTbig : 2 * frame.child.den + 2 < frame.child.periodDenominator := by
    rw [hP]
    nlinarith
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den ((reflH frame z).1, (reflH frame z).2 + 1)
      = frame.child.num - frame.tGrade z := by
    unfold FLatticePaper.W1.w1t reflH ChildFrame.tGrade
    dsimp only
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den ((reflH frame z).1, (reflH frame z).2 + 1)
      = frame.child.periodDenominator + frame.child.den + frame.child.num - frame.sGrade z := by
    unfold FLatticePaper.W1.w1s reflH ChildFrame.sGrade
    dsimp only
    rw [hP]
    ring
  unfold FLatticePaper.W1.StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_pos hev]
  rw [htw, hsw, hTw]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The forced west arrow `z+S → z+SW` at an odd free H root**, from the reflected contact fan. The field symmetry `hsym`
and the start contact `hcon : G (z+S) = 0` are named inputs; the fan start `reflH z + N` is then a white contact in the open
rectangle, its `W1`-forced edge is its east edge (`fan_start_forced`), and `reflH` carries that to `z+S → z+SW`. -/
theorem forcedEdge_he1 {frame : ChildFrame} {G : Field} (hP : frame.Packet G)
    (hsig : ∀ w ∈ frame.closedPolygon, G w - G (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) {K : ℕ}
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ G (p + (k : ℤ), q + (k : ℤ)))
    (hsym : ∀ y, G (reflH frame y) = G y)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hne : z ≠ frame.hLast)
    (hbt : frame.child.num + 2 ≤ frame.tGrade z)
    (hcon : G (z.1, z.2 - 1) = 0) :
    ForcedEdge G (fun _ _ => False) (z.1, z.2 - 1) (z.1 - 1, z.2 - 1) := by
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have htb : frame.child.num + 2 ≤ frame.tGrade (reflH frame z) := by
    have e : frame.tGrade (reflH frame z) = frame.child.num + frame.child.den - frame.tGrade z := by
      unfold ChildFrame.tGrade reflH
      dsimp only
      ring
    have ht := FLatticePaper.ShortRoute.freeH_tGrade_add_two_le frame hz hodd hne
    omega
  have hSI := start_SI hz hodd hne hbt
  obtain ⟨start, hsdef⟩ : ∃ s : Site, s = ((reflH frame z).1, (reflH frame z).2 + 1) := ⟨_, rfl⟩
  rw [← hsdef] at hSI
  have hevS : EvenSite start := by
    rw [hsdef]
    unfold EvenSite reflH
    dsimp only
    unfold EvenSite at hodd
    omega
  have hsGS : reflH frame (z.1, z.2 - 1) = start := by
    rw [hsdef]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  have hGstart : G start = 0 := by
    rw [← hsGS, hsym]
    exact hcon
  have hevP : EvenSite ((reflH frame z).1, (reflH frame z).2 + 1) := by
    rw [← hsdef]
    exact hevS
  have hconeS : ConeRoot (reflH frame z) K start := by
    rw [hsdef]
    unfold ConeRoot
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hevP h⟩
    · dsimp only
      omega
    · dsimp only
      omega
    · dsimp only
      omega
  have hc1 : FLatticePaper.QuadraticCap.capMin (start.2 - (reflH frame z).2) = 0 := by
    have e1 : start.2 - (reflH frame z).2 = 1 := by
      rw [hsdef]
      dsimp only
      omega
    rw [e1]
    norm_num [FLatticePaper.QuadraticCap.capMin]
  have hmem : start ∈ contactFan frame G (reflH frame z) K := by
    refine mem_contactFan.mpr ⟨⟨(FLatticePaper.W1Exit.openRect_iff frame start).mpr hSI, hconeS⟩, ?_⟩
    unfold parabolaField
    rw [hGstart, hc1]
  have hwin : WindowOn (fun x => frame.openRect x ∧ ConeRoot (reflH frame z) K x) G
      (fun i => parabolaField (reflH frame z).2 i) :=
    cone_window frame hP hsig hs K hcap (reflH frame z) htb
  have hlapS : laplacian G start = 0 := contactFan_even_white hbin hwin hmem hevS
  obtain ⟨o, ho⟩ := hW1 start ((FLatticePaper.W1Exit.openRect_iff frame start).mp ((FLatticePaper.W1Exit.openRect_iff frame start).mpr hSI)) hlapS
  have hO := fan_start_forced hP hsig hs hK2 hKs hKr hcap htb hmem hevS ho
  rw [hO] at ho
  have hF : ForcedEdge G (fun _ _ => False) start (incomingPos start) :=
    FLatticePaper.W1.forcedEdgeIn_forced ho
  have hT := forcedEdge_reflH hsym hF
  have e1 : reflH frame start = (z.1, z.2 - 1) := by
    rw [← hsGS, reflH_reflH]
  have e2 : reflH frame (incomingPos start) = (z.1 - 1, z.2 - 1) := by
    have hpos : incomingPos start = (start.1 + 1, start.2) := by
      unfold incomingPos
      rw [if_pos hevS]
    rw [hpos, hsdef]
    unfold reflH
    refine Prod.ext ?_ ?_
    · try dsimp only
      try omega
    · try dsimp only
      try omega
  rw [e1, e2] at hT
  exact hT

end FLatticePaper.ReflectedFan
