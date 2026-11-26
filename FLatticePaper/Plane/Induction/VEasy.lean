import FLatticePaper.Plane.Induction.VStrict
import FLatticePaper.Plane.Induction.VLattice
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.RouteRegional
import FLatticePaper.Plane.Induction.V2Minus
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.RotatedForced
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.V2Arrows

/-! # The easy V regime (`2n ≤ d`): the target of the `v3` middle arrow is white, and the arrow

For an odd free V root `z`, the target `nxt` of the middle arrow is an even site whose two inputs and itself lie in the harmonic
band of the field `G` (the strips `HasStrips.2`, and the odd `h₀` intervals `hlow`, `hup` as hypotheses), so `laplacian G nxt = 0`.
The points: `z`, `z + (2, 0)` (`η = +1`) or `z − (2, 0)` (`η = −1`), and `nxt`. The arrow is `RouteRegional.white_route_policy`
applied to the middle (strict by `VStrict`), with the deck shift `(d, n)` for `η = −1`. -/

namespace FLatticePaper.VEasy

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem strips_harm {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) {x : Site}
    (h1 : 1 - 2 * frame.child.den ≤ frame.sGrade x) (h2 : frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    G x = harmonicGrid x := by
  unfold ChildFrame.HasStrips at hS
  exact hS.2 x h1 h2

/-- The odd band `2 − 3d + n ≤ s ≤ 3d + n − 2` carries the harmonic grid (strips, and the odd `h₀` intervals `hlow`, `hup`). -/
theorem odd_band {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {x : Site} (hx : ¬ EvenSite x) (h1 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x)
    (h2 : frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2) : G x = harmonicGrid x := by
  obtain ⟨hn1, hnd, -, -, -⟩ := frame.child_facts
  by_cases a : frame.sGrade x ≤ 1 - 2 * frame.child.den
  · exact hlow x hx h1 a
  by_cases b : frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 1
  · exact strips_harm hS (by omega) b
  · exact hup x hx (by omega) h2

/-- The zero Laplacian of `G` at an even site whose inputs and itself lie in the harmonic bands. -/
theorem lap_zero_of_harm {G : Field} {x : Site}
    (ha : G (incomingNeg x) = harmonicGrid (incomingNeg x)) (hb : G (incomingPos x) = harmonicGrid (incomingPos x))
    (hc : G x = harmonicGrid x) : laplacian G x = 0 := by
  have hh := harmonicGrid_harmonic x
  unfold laplacian at hh ⊢
  rw [ha, hb, hc]
  linarith

/-- **The target of the `η = +1` middle arrow is white** (easy regime): `z`, `z + (2, 0)` and `nxt = z + (1, 0)` lie in the harmonic
band, using `s(z + (2,0)) = s(z) + 2(d + n) ≤ 3d + n − 2`, i.e. `s(z) ≤ d − n − 2`. -/
theorem nxt_zero_plus {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hs2 : frame.sGrade z ≤ frame.child.den - frame.child.num - 2) :
    laplacian G (z.1 + 1, z.2) = 0 := by
  obtain ⟨h1, h2, h3, h4, hvs⟩ := VStrict.odd_free_V_facts hz hodd
  obtain ⟨hn0, -, hd2, -, -⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hs_lo, hs_hi⟩ := VLattice.s_range hnd hvs
  have hodd' : ¬ ((z.1 + z.2) % 2 = 0) := hodd
  have hev : EvenSite (z.1 + 1, z.2) := by
    show (z.1 + 1 + z.2) % 2 = 0
    omega
  have hzb : G z = harmonicGrid z := odd_band hS hlow hup hodd (by omega) (by omega)
  have hodd2 : ¬ EvenSite (z.1 + 2, z.2) := by
    show ¬ ((z.1 + 2 + z.2) % 2 = 0)
    omega
  have e2s : frame.sGrade (z.1 + 2, z.2) = frame.sGrade z + 2 * (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hz2b : G (z.1 + 2, z.2) = harmonicGrid (z.1 + 2, z.2) :=
    odd_band hS hlow hup hodd2 (by rw [e2s]; omega) (by rw [e2s]; omega)
  have es : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hnb : G (z.1 + 1, z.2) = harmonicGrid (z.1 + 1, z.2) :=
    strips_harm hS (by rw [es]; omega) (by rw [es]; omega)
  have e1 : incomingNeg (z.1 + 1, z.2) = z := by
    unfold incomingNeg
    rw [if_pos hev]
    show (z.1 + 1 - 1, z.2) = (z.1, z.2)
    congr 1
    ring
  have e2 : incomingPos (z.1 + 1, z.2) = (z.1 + 2, z.2) := by
    unfold incomingPos
    rw [if_pos hev]
    show (z.1 + 1 + 1, z.2) = (z.1 + 2, z.2)
    congr 1
    ring
  apply lap_zero_of_harm
  · rw [e1]
    exact hzb
  · rw [e2]
    exact hz2b
  · exact hnb

/-- **The target of the `η = −1` middle arrow is white** (easy regime, `d ≥ 2n + 1`): `z`, `z − (2, 0)` and `nxt = z − (1, 0)`
lie in the harmonic band; the closed neighbour `z − (0, 1)` gives `s(z) ≥ d − n`. -/
theorem nxt_zero_minus {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    (hV : 2 * frame.child.num ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hs2 : frame.child.den - frame.child.num ≤ frame.sGrade z) :
    laplacian G (z.1 - 1, z.2) = 0 := by
  obtain ⟨h1, h2, h3, h4, hvs⟩ := VStrict.odd_free_V_facts hz hodd
  obtain ⟨hn0, -, hd2, hd3, -⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hnodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hdn : 2 * frame.child.num + 1 ≤ frame.child.den := by omega
  obtain ⟨hs_lo, hs_hi⟩ := VLattice.s_range hnd hvs
  have hodd' : ¬ ((z.1 + z.2) % 2 = 0) := hodd
  have hev : EvenSite (z.1 - 1, z.2) := by
    show (z.1 - 1 + z.2) % 2 = 0
    omega
  have hzb : G z = harmonicGrid z := odd_band hS hlow hup hodd (by omega) (by omega)
  have hodd2 : ¬ EvenSite (z.1 - 2, z.2) := by
    show ¬ ((z.1 - 2 + z.2) % 2 = 0)
    omega
  have e2s : frame.sGrade (z.1 - 2, z.2) = frame.sGrade z - 2 * (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hz2b : G (z.1 - 2, z.2) = harmonicGrid (z.1 - 2, z.2) :=
    odd_band hS hlow hup hodd2 (by rw [e2s]; omega) (by rw [e2s]; omega)
  have es : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hnb : G (z.1 - 1, z.2) = harmonicGrid (z.1 - 1, z.2) :=
    strips_harm hS (by rw [es]; omega) (by rw [es]; omega)
  have e1 : incomingNeg (z.1 - 1, z.2) = (z.1 - 2, z.2) := by
    unfold incomingNeg
    rw [if_pos hev]
    show (z.1 - 1 - 1, z.2) = (z.1 - 2, z.2)
    congr 1
    ring
  have e2 : incomingPos (z.1 - 1, z.2) = z := by
    unfold incomingPos
    rw [if_pos hev]
    show (z.1 - 1 + 1, z.2) = (z.1, z.2)
    congr 1
    ring
  apply lap_zero_of_harm
  · rw [e1]
    exact hz2b
  · rw [e2]
    exact hzb
  · exact hnb

/-- The `s`-bound `s(z) ≤ d − n − 2` from the free neighbour `z + (0, 1)` (`VLattice.s_le_of_free_nb`). -/
theorem s_le_of_nb_plus {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hnb : (z.1, z.2 + 1) ∈ frame.freeV) (hV : 2 * frame.child.num ≤ frame.child.den) :
    frame.sGrade z ≤ frame.child.den - frame.child.num - 2 := by
  obtain ⟨h1, h2, h3, h4, hvs⟩ := VStrict.odd_free_V_facts hz hodd
  obtain ⟨hn0, -, hd2, -, hT⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hnodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hspar : frame.sGrade z % 2 = 0 := FLatticePaper.Induction.sGrade_even frame z
  have hsnb : frame.sGrade (z.1, z.2 + 1) = frame.sGrade z + (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have htz : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hsz : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
    omega
  have hnbF := hnb
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hnbF
  obtain ⟨-, hnbnot, hnbvs⟩ := hnbF
  unfold ChildFrame.vSpectrum at hnbvs
  obtain ⟨-, hnbs⟩ := hnbvs
  rw [hsnb] at hnbs
  have hfree : frame.tGrade z < 2 * frame.child.num + frame.child.den - (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2)
      ∨ frame.sGrade z < 3 * frame.child.num + 2 - frame.child.den := by
    by_contra hc
    push Not at hc
    apply hnbnot
    have hodd_nb : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
      show ¬ ((z.1 - 1 + (z.2 + 1)) % 2 = 0)
      omega
    rw [(frame.mem_closedPolygon_iff (z.1 - 1, z.2 + 1))]
    have htw : frame.tGrade (z.1 - 1, z.2 + 1) = frame.tGrade z - frame.child.num - frame.child.den := by
      unfold ChildFrame.tGrade
      ring
    have hsw : frame.sGrade (z.1 - 1, z.2 + 1) = frame.sGrade z - 2 * frame.child.num := by
      unfold ChildFrame.sGrade
      ring
    right
    refine ⟨hodd_nb, ?_, ?_, ?_, ?_⟩
    · rw [htw, hT]
      omega
    · rw [htw]
      omega
    · rw [hsw]
      omega
    · rw [hsw, hT]
      omega
  have hnbs' : (0 ≤ frame.sGrade z + frame.child.den - frame.child.num ∧
        frame.sGrade z + frame.child.den - frame.child.num ≤ 2 * frame.child.num) ∨
      (2 - frame.child.den + frame.child.num ≤ frame.sGrade z + frame.child.den - frame.child.num ∧
        frame.sGrade z + frame.child.den - frame.child.num ≤ frame.child.den + frame.child.num - 2) := by
    omega
  exact VLattice.s_le_of_free_nb hn1 hnd hV hnodd hdodd hodd' hspar htz hsz h1 hfree hnbs'

/-- **The middle arrow of the `η = +1` V row (easy regime)**: `z + (1, 1) → z + (1, 0)`, from the white-middle regional argument. -/
theorem v3_arrow_plus_easy {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hS : frame.HasStrips G)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    (hV : 2 * frame.child.num ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hnb : (z.1, z.2 + 1) ∈ frame.freeV) :
    laplacian G (z.1 + 1, z.2 + 1) = -1 ∨ C.policy (z.1 + 1, z.2 + 1) (z.1 + 1, z.2) := by
  have hs2 := s_le_of_nb_plus hz hodd hnb hV
  by_cases hb : laplacian G (z.1 + 1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hmw : laplacian G (z.1 + 1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hm := VStrict.vplus_middle_strict hz hodd
    have hnw := nxt_zero_plus hS hlow hup hz hodd hs2
    have hoddm : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
      show ¬ ((z.1 + 1 + (z.2 + 1)) % 2 = 0)
      have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
      omega
    have hev : EvenSite (z.1 + 1, z.2) := by
      show (z.1 + 1 + z.2) % 2 = 0
      have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
      omega
    have hin : (z.1 + 1, z.2) = incomingNeg (z.1 + 1, z.2 + 1) ∨ (z.1 + 1, z.2) = incomingPos (z.1 + 1, z.2 + 1) :=
      Or.inl (by
        unfold incomingNeg
        rw [if_neg hoddm]
        show (z.1 + 1, z.2) = (z.1 + 1, z.2 + 1 - 1)
        congr 1
        ring)
    have hzin : z = incomingNeg (z.1 + 1, z.2) ∨ z = incomingPos (z.1 + 1, z.2) :=
      Or.inl (by
        unfold incomingNeg
        rw [if_pos hev]
        show (z.1, z.2) = (z.1 + 1 - 1, z.2)
        congr 1
        ring)
    have hzR := FLatticePaper.V2Arrows.not_strict_of_freeV hz
    have hzm : z ≠ (z.1 + 1, z.2 + 1) := by
      intro h
      have h1 : z.1 = z.1 + 1 := congrArg Prod.fst h
      omega
    exact FLatticePaper.RouteRegional.white_route_policy C hW1 hm hmw hin hnw hzin hzR hzm

/-- **The middle arrow of the `η = −1` V row (easy regime)**: `z − (1, 1) → z − (1, 0)`, from the white-middle regional argument on the
deck translate `(d, n)`, transported back by `hdeck`. -/
theorem v3_arrow_minus_easy {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hS : frame.HasStrips G)
    (hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 1 - 2 * frame.child.den → G x = harmonicGrid x)
    (hup : ∀ x : Site, ¬ EvenSite x → frame.child.den + frame.child.num - 2 < frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    (hV : 2 * frame.child.num ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hnb : (z.1, z.2 - 1) ∈ frame.freeV) :
    laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1 - 1, z.2) := by
  have hev' : EvenSite (z.1, z.2 - 1) := by
    show (z.1 + (z.2 - 1)) % 2 = 0
    have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
    omega
  have hs2 : frame.child.den - frame.child.num ≤ frame.sGrade z := by
    have hcl := hnb
    simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hcl
    obtain ⟨hcl1, -, -⟩ := hcl
    have hcl2 := (frame.mem_closedPolygon_iff (z.1, z.2 - 1)).mp hcl1
    have e : frame.sGrade (z.1, z.2 - 1) = frame.sGrade z - (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade
      ring
    rcases hcl2 with h | h
    · have := h.2.2.2.1
      omega
    · exact absurd hev' h.1
  by_cases hb : laplacian G (z.1 - 1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hmw : laplacian G (z.1 - 1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have hm' := VStrict.vminus_middle_strict hz hodd
    have hnw := nxt_zero_minus hS hlow hup hV hz hodd hs2
    have hK : EvenSite (frame.child.den, frame.child.num) := by
      show (frame.child.den + frame.child.num) % 2 = 0
      have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
      omega
    have hmK : laplacian G ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) = 0 := by
      rw [FLatticePaper.StripColours.lap_add_kernel frame hP.periods]
      exact hmw
    have hnK : laplacian G ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) = 0 := by
      rw [FLatticePaper.StripColours.lap_add_kernel frame hP.periods]
      exact hnw
    have hposm : incomingPos (z.1 - 1, z.2 - 1) = (z.1 - 1, z.2) := by
      have hoddm : ¬ EvenSite (z.1 - 1, z.2 - 1) := by
        show ¬ ((z.1 - 1 + (z.2 - 1)) % 2 = 0)
        have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
        omega
      unfold incomingPos
      rw [if_neg hoddm]
      show (z.1 - 1, z.2 - 1 + 1) = (z.1 - 1, z.2)
      congr 1
      ring
    have hposn : incomingPos (z.1 - 1, z.2) = z := by
      unfold incomingPos
      rw [if_pos (show EvenSite (z.1 - 1, z.2) from by
        show (z.1 - 1 + z.2) % 2 = 0
        have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
        omega)]
      show (z.1 - 1 + 1, z.2) = (z.1, z.2)
      congr 1
      ring
    have hin' : (z.1 - 1, z.2) + (frame.child.den, frame.child.num) =
        incomingNeg ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) ∨
        (z.1 - 1, z.2) + (frame.child.den, frame.child.num) =
          incomingPos ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) :=
      Or.inr (by
        rw [FLatticePaper.RotatedForced.incomingPos_add (z.1 - 1, z.2 - 1) (frame.child.den, frame.child.num) hK, hposm])
    have hzin' : z + (frame.child.den, frame.child.num) =
        incomingNeg ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) ∨
        z + (frame.child.den, frame.child.num) =
          incomingPos ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) :=
      Or.inr (by
        rw [FLatticePaper.RotatedForced.incomingPos_add (z.1 - 1, z.2) (frame.child.den, frame.child.num) hK, hposn])
    have hzR' := FLatticePaper.V2Minus.not_strict_shift_of_freeV hz
    have hzm : z ≠ (z.1 - 1, z.2 - 1) := by
      intro h
      have h1 : z.1 = z.1 - 1 := congrArg Prod.fst h
      omega
    have hzm' : z + (frame.child.den, frame.child.num) ≠ (z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num) := by
      intro h
      exact hzm (add_right_cancel h)
    have key := FLatticePaper.RouteRegional.white_route_policy C hW1 hm' hmK hin' hnK hzin' hzR' hzm'
    have hK10 : frame.child.modifiedDeck.combine 1 0 = (frame.child.den, frame.child.num) :=
      FLatticePaper.ChainWire.combine_one_zero_eq_Kdeck frame
    have h := hdeck 1 0 (z.1 - 1, z.2 - 1) (z.1 - 1, z.2)
    rw [hK10] at h
    exact h.mpr key

end FLatticePaper.VEasy
