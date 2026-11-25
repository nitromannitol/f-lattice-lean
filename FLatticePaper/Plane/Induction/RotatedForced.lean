import FLatticePaper.Plane.Induction.CapConeGrades
import FLatticePaper.Plane.Induction.RotatedCap
import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.RotatedMono

/-! # Z-covariance of `ForcedEdgeIn` (the rotated forcing)

`Z(y) = (−y₂, y₁−1)` carries the residual `f = quarterTurnField G` to `G`: the residual laplacian at `y` is the laplacian of `G` at
`Z y`, and `Z` maps unit squares to unit squares and the incoming neighbours of `y` to those of `Z y` (up to the swap of the two inputs).
So a derivation `ForcedEdgeIn G RV seed` in the region `RV x = ropenNL (Zinv x)` transfers to a derivation `ForcedEdgeIn f (ropenNL)`.
The region `RV` is the `V`-region of `G`; it is not `W1.StrictInterior (num, den)` (the two regions are not nested, checked numerically),
so the transfer needs the forcing of `G` in `RV`, not `W1Forced` of `G`. -/

namespace FLatticePaper.RotatedForced

open FLatticePaper FLatticePaper.Induction FLatticePaper.CapRecursion FLatticePaper.RotatedCap FLatticePaper.W1
  FLatticePaper.CapConeGrades FLatticePaper.AndOrRank

/-- The inverse of `Z`: `Zinv(x) = (x₂+1, −x₁)`. -/
def Zinv (x : Site) : Site := (x.2 + 1, -x.1)

theorem Zs_Zinv (x : Site) : Zs (Zinv x) = x := by
  unfold Zs Zinv
  ext <;> simp

theorem Zinv_Zs (y : Site) : Zinv (Zs y) = y := by
  unfold Zs Zinv
  ext <;> simp

/-- The incoming neighbours of `Zy` are the images of those of `y`, up to the order of the two inputs. -/
theorem neighbour_Zs (y o : Site) (h : o = incomingNeg (Zs y) ∨ o = incomingPos (Zs y)) :
    Zinv o = incomingNeg y ∨ Zinv o = incomingPos y := by
  by_cases hy : EvenSite y
  · have hZ : ¬ EvenSite (Zs y) := by
      unfold EvenSite at hy ⊢
      unfold Zs
      dsimp only
      omega
    rw [incomingNeg_of_odd' (Zs y) hZ, incomingPos_of_odd' (Zs y) hZ] at h
    rw [incomingNeg_of_even' y hy, incomingPos_of_even' y hy]
    rcases h with rfl | rfl
    · left
      unfold Zs Zinv
      ext <;> simp
    · right
      unfold Zs Zinv
      ext <;> simp
  · have hZ : EvenSite (Zs y) := by
      unfold EvenSite at hy ⊢
      unfold Zs
      dsimp only
      omega
    rw [incomingNeg_of_even' (Zs y) hZ, incomingPos_of_even' (Zs y) hZ] at h
    rw [incomingNeg_of_odd' y hy, incomingPos_of_odd' y hy]
    rcases h with rfl | rfl
    · right
      unfold Zs Zinv
      ext <;> simp
      omega
    · left
      unfold Zs Zinv
      ext <;> simp
      omega

/-- A unit square of `G` at base `(a,b)` is a unit square of the residual at base `(b+1, −a−1)`. -/
theorem mem_square_Zs (a b : ℤ) (c : Site) :
    c ∈ squareCorners (b + 1) (-a - 1) ↔ Zs c ∈ squareCorners a b := by
  rw [FLatticePaper.FanCompat.mem_squareCorners_iff, FLatticePaper.FanCompat.mem_squareCorners_iff]
  unfold Zs
  simp only
  omega

/-- **Z-covariance of the forced derivations.** A derivation of `G` in the region `RV` (a `V`-region) transfers to a derivation of the
residual `quarterTurnField G` in the region `y ↦ RV (Zs y)`, with the seed pulled back by `Z`. -/
theorem forcedEdgeIn_Zs {G : Field} {RV : Site → Prop} {seedG : Site → Site → Prop} {c o : Site}
    (h : W1.ForcedEdgeIn G RV seedG c o) :
    ∀ y o' : Site, c = Zs y → o = Zs o' →
      W1.ForcedEdgeIn (quarterTurnField G) (fun y => RV (Zs y)) (fun y o' => seedG (Zs y) (Zs o')) y o' := by
  induction h with
  | seed hs =>
    intro y o' hc ho
    subst hc
    subst ho
    exact W1.ForcedEdgeIn.seed hs
  | @unit a b c o inside hR hc hw ho hout hin hforced ih =>
    intro y o' hc0 ho0
    subst hc0
    subst ho0
    refine W1.ForcedEdgeIn.unit (a := b + 1) (b := -a - 1) (inside := fun y' => Zinv (inside (Zs y')))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro c' hc'
      exact hR (Zs c') ((mem_square_Zs a b c').mp hc')
    · exact (mem_square_Zs a b y).mpr hc
    · rw [laplacian_quarterTurnField]
      exact hw
    · have hn := neighbour_Zs y (Zs o') ho
      rw [Zinv_Zs] at hn
      exact hn
    · intro hmem
      exact hout ((mem_square_Zs a b o').mp hmem)
    · intro c' hc' hne
      have hZc : Zs c' ∈ squareCorners a b := (mem_square_Zs a b c').mp hc'
      have hne' : Zs c' ≠ Zs y := by
        intro heq
        apply hne
        have h2 := congrArg Zinv heq
        rwa [Zinv_Zs, Zinv_Zs] at h2
      rcases hin (Zs c') hZc hne' with h1 | ⟨h0, hi1, hi2⟩
      · left
        rw [laplacian_quarterTurnField]
        exact h1
      · right
        refine ⟨by rw [laplacian_quarterTurnField]; exact h0, ?_, ?_⟩
        · exact (mem_square_Zs a b _).mpr (by rw [Zs_Zinv]; exact hi1)
        · exact neighbour_Zs c' (inside (Zs c')) hi2
    · intro c' hc' hne h0
      have hZc : Zs c' ∈ squareCorners a b := (mem_square_Zs a b c').mp hc'
      have hne' : Zs c' ≠ Zs y := by
        intro heq
        apply hne
        have h2 := congrArg Zinv heq
        rwa [Zinv_Zs, Zinv_Zs] at h2
      have h0' : laplacian G (Zs c') = 0 := by
        rw [laplacian_quarterTurnField] at h0
        exact h0
      exact ih (Zs c') hZc hne' h0' c' (Zinv (inside (Zs c'))) rfl (Zs_Zinv _).symm

/-- **The residual forcing from the `V`-region.** A derivation of `G` in the region `x ↦ ropenNL (Zinv x)` gives a derivation of the
residual `quarterTurnField G` in `ropenNL` itself (the pull-back of `ropenNL` by `Z` is the region of `G`). -/
theorem forcedEdgeIn_ropen {G : Field} {N D T : ℤ} {seedG : Site → Site → Prop} {c o : Site}
    (h : W1.ForcedEdgeIn G (fun x => CapConeGrades.ropenNL N D T (Zinv x)) seedG c o) (y o' : Site)
    (hc : c = Zs y) (ho : o = Zs o') :
    W1.ForcedEdgeIn (quarterTurnField G) (CapConeGrades.ropenNL N D T)
      (fun y o' => seedG (Zs y) (Zs o')) y o' := by
  simpa only [Zinv_Zs] using forcedEdgeIn_Zs h y o' hc ho

/-- **The cap data of the residual.** The residual `quarterTurnField G` satisfies the `(N, D)`-cap hypotheses (`NLCap`): its laplacian is
binary, its zero and harmonic strips are those of `G` through `Z` (`quarterTurnField_eq_zero`, `quarterTurnField_eq_harmonic`), and its
two sheet monotonicities are `rotated_mono` (the frame's price, with the parity matched by `¬EvenSite`). -/
theorem rotated_NL {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) :
    CapConeGrades.NLCap N D (quarterTurnField G) := by
  have hden : fr.child.den = N + D := by omega
  have hnum : fr.child.num = D - N := by omega
  refine
    { binary := ?_, zero := ?_, odd := ?_, even := ?_, harm := ?_ }
  · intro x
    rw [laplacian_quarterTurnField]
    exact hP.binary _
  · intro w h1 h2
    apply FLatticePaper.Induction.quarterTurnField_eq_zero hP.strips
    · rw [mapSite_eq_Zs]
      unfold ChildFrame.sGrade
      simp only [Zs]
      rw [hden, hnum]
      nlinarith
    · rw [mapSite_eq_Zs]
      unfold ChildFrame.sGrade
      simp only [Zs]
      rw [hden, hnum]
      nlinarith
  · intro u v hu hv h1 h2
    have hpar : (u.1 + u.2) % 2 = (v.1 + v.2) % 2 := by
      unfold EvenSite at hu hv
      omega
    exact RotatedMono.rotated_mono hP hprice hdrU hdrV N D hN2.symm hD2.symm hN0 hNDlt u v hpar h1 h2
  · intro u v hu hv h1 h2
    have hpar : (u.1 + u.2) % 2 = (v.1 + v.2) % 2 := by
      unfold EvenSite at hu hv
      omega
    exact RotatedMono.rotated_mono hP hprice hdrU hdrV N D hN2.symm hD2.symm hN0 hNDlt u v hpar h1 h2
  · intro w h1 h2
    apply FLatticePaper.Induction.quarterTurnField_eq_harmonic hP.strips
    · rw [mapSite_eq_Zs]
      unfold ChildFrame.tGrade
      simp only [Zs]
      rw [hden, hnum]
      nlinarith
    · rw [mapSite_eq_Zs]
      unfold ChildFrame.tGrade
      simp only [Zs]
      rw [hden, hnum]
      nlinarith

/-- **The forced east start of the rotated fan.** For the residual `quarterTurnField G` in the open rectangle `ropenNL N D T`, a
forced edge out of an even fan start is its east edge. The cap of the residual is `rotated_ray_cap_mono` (depth `2NK ≤ 3D + 3N − 1`);
the fan depth `4N + 2D − a ≤ 2NK` is an explicit hypothesis (the window of depths `K` is not automatic for every `(N, D)`). -/
theorem rotated_fan_start {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D a T : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (J : ℕ) (hJ1 : 2 * N * (J : ℤ) ≤ N + D - 2) (hJ2 : N + D - 2 < 2 * N * ((J : ℤ) + 1))
    (K : ℕ) (hK2 : 2 ≤ K) (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1)
    (b start : Site) (hb : N + a ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet (CapConeGrades.ropenNL N D T) (quarterTurnField G) b K)
    (heven : EvenSite start) {o : Site}
    (ho : W1.ForcedEdgeIn (quarterTurnField G) (CapConeGrades.ropenNL N D T) (fun _ _ => False) start o) :
    o = incomingPos start :=
  CapConeGrades.fan_start_forced_NL (rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt) hN0 hNDlt ha1 ha2 hs hpq K hK2
    hKs (by linarith) (RotatedMono.rotated_ray_cap_mono hP hprice hdrU hdrV N D a ha1 ha2 hN2 hD2 hN0 hNDlt hs hpq J K hJ1 hJ2 hKr)
    b start hb hstart heven ho

/-- **The forced east start from the `V`-region of `G`.** The residual's forced edge is the image of a forced edge of `G` in the region
`x ↦ ropenNL (Zinv x)` (`forcedEdgeIn_ropen`), so the forced east start of the rotated fan needs only the `V`-side forcing in that
region. -/
theorem rotated_fan_start_G {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D a T : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (J : ℕ) (hJ1 : 2 * N * (J : ℤ) ≤ N + D - 2) (hJ2 : N + D - 2 < 2 * N * ((J : ℤ) + 1))
    (K : ℕ) (hK2 : 2 ≤ K) (hKs : 4 * N + 2 * D - a ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1)
    (b start : Site) (hb : N + a ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet (CapConeGrades.ropenNL N D T) (quarterTurnField G) b K)
    (heven : EvenSite start) (o : Site)
    (hG : W1.ForcedEdgeIn G (fun x => CapConeGrades.ropenNL N D T (Zinv x)) (fun _ _ => False) (Zs start) (Zs o)) :
    o = incomingPos start :=
  rotated_fan_start hP hprice hdrU hdrV N D a T hN2 hD2 hN0 hNDlt ha1 ha2 hs hpq J hJ1 hJ2 K hK2 hKs hKr b start hb hstart heven
    (forcedEdgeIn_ropen hG start o rfl rfl)

end FLatticePaper.RotatedForced
