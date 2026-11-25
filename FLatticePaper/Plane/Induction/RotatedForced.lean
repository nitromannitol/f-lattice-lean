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

/-- A multiple of `m` in a window `[lo, hi]` of length at least `m − 1`. -/
theorem exists_mult_window {m lo hi : ℤ} (hm : 0 < m) (hlo : 0 ≤ lo) (hw : lo + m - 1 ≤ hi) :
    ∃ K : ℕ, lo ≤ m * (K : ℤ) ∧ m * (K : ℤ) ≤ hi := by
  have hmod := Int.emod_def (lo + m - 1) m
  have hmnn := Int.emod_nonneg (lo + m - 1) (ne_of_gt hm)
  have hmlt := Int.emod_lt_of_pos (lo + m - 1) hm
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℤ, K0 = (lo + m - 1) / m := ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    exact Int.ediv_nonneg (by linarith) (le_of_lt hm)
  rw [← hK0] at hmod
  have hcast : ((K0.toNat : ℕ) : ℤ) = K0 := Int.toNat_of_nonneg hK0nn
  refine ⟨K0.toNat, ?_, ?_⟩
  · rw [hcast]
    linarith
  · rw [hcast]
    linarith

/-- Integer floor: `m J ≤ X < m (J + 1)` for some natural `J`, when `0 < m` and `0 ≤ X`. -/
theorem exists_floor_window (m X : ℤ) (hm : 0 < m) (hX : 0 ≤ X) :
    ∃ J : ℕ, m * (J : ℤ) ≤ X ∧ X < m * ((J : ℤ) + 1) := by
  have hmod := Int.emod_def X m
  have hmnn := Int.emod_nonneg X (ne_of_gt hm)
  have hmlt := Int.emod_lt_of_pos X hm
  obtain ⟨J0, hJ0⟩ : ∃ J0 : ℤ, J0 = X / m := ⟨_, rfl⟩
  have hJ0nn : 0 ≤ J0 := by
    rw [hJ0]
    exact Int.ediv_nonneg hX (le_of_lt hm)
  rw [← hJ0] at hmod
  have hcast : ((J0.toNat : ℕ) : ℤ) = J0 := Int.toNat_of_nonneg hJ0nn
  refine ⟨J0.toNat, ?_, ?_⟩
  · rw [hcast]
    linarith
  · rw [hcast]
    linarith

/-- **The fan depths of the residual (a = 1).** For `1 ≤ N` and `3N − 1 ≤ D` there is a depth `K ≥ 2` with
`4N + 2D − 1 ≤ 2NK ≤ 3D + 3N − 1`: the smallest multiple of `2N` above `4N + 2D − 1` lies below `3D + 3N − 1` exactly when `3N − 1 ≤ D`. -/
theorem K_bounds_rot {N D : ℤ} (hN : 1 ≤ N) (hD : 3 * N - 1 ≤ D) :
    ∃ K : ℕ, 2 ≤ K ∧ 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ) ∧ 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1 := by
  obtain ⟨K, hK1, hK2⟩ := exists_mult_window (m := 2 * N) (lo := 4 * N + 2 * D - 1) (hi := 3 * D + 3 * N - 1)
    (by omega) (by omega) (by omega)
  refine ⟨K, ?_, hK1, hK2⟩
  by_contra h
  have hK : K ≤ 1 := by omega
  have hK' : (K : ℤ) ≤ 1 := by exact_mod_cast hK
  nlinarith

/-- **The forced east start of the rotated fan, for `a = 1` and `3N − 1 ≤ D`.** The ray start `(p, q)` with `N p − D q = 1 − N` and
`p + q` odd is that of `CapRayGrades.ray_start_odd` (the coprimality of `(N, D)` is `RotatedMono.coprime_residual`); the cap is
`rotated_ray_cap_mono` at a floor index `J`; the depth `K` is any depth in the window, which exists by `K_bounds_rot` when
`3N − 1 ≤ D` (the residual's `D + N` odd excludes `D = 3N − 2`). -/
theorem rotated_fan_start_D {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D T : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hodd : (D + N) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K) (hKs : 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1)
    (b start : Site) (hb : N + 1 ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet (CapConeGrades.ropenNL N D T) (quarterTurnField G) b K)
    (heven : EvenSite start) {o : Site}
    (ho : W1.ForcedEdgeIn (quarterTurnField G) (CapConeGrades.ropenNL N D T) (fun _ _ => False) start o) :
    o = incomingPos start := by
  obtain ⟨p, q, hs, hpq⟩ := CapRayGrades.ray_start_odd N D 1 (RotatedMono.coprime_residual fr N D hN2.symm hD2.symm) hodd
  obtain ⟨J, hJ1, hJ2⟩ := exists_floor_window (2 * N) (N + D - 2) (by omega) (by omega)
  exact rotated_fan_start hP hprice hdrU hdrV N D 1 T hN2 hD2 hN0 hNDlt (by norm_num) (by norm_num) hs hpq J hJ1
    (by linarith) K hK2 hKs (by linarith) b start hb hstart heven ho

/-! ## The residual forcing on the strict interior of `E − U`

The residual region is `y ↦ SI(Zs y + U)` with `U = (d, n)` the kernel: the strict interior of `E − U`, pulled back by `Z`. It lies in the
residual open rectangle `ropenNL` at the grade `T` of `G`, so a derivation in the region is a derivation in `ropenNL`. The forcing comes from
`W1Forced G` at the translate by `U`. -/

/-- The residual region `y ↦ SI(Zs y + U)`, with `U = (d, n)` the kernel. -/
def resRegion (n d : ℤ) (y : Site) : Prop :=
  FLatticePaper.W1.StrictInterior n d (-y.2 + d, y.1 - 1 + n)

/-- **The residual region lies in the residual open rectangle.** With `t(Zs y + U) = d − s'(y)` and `s(Zs y + U) = 2 t'(y) + T − 2N`,
the strict-interior inequalities of `G` give those of `ropenNL` (`T = w1T n d`). -/
theorem resRegion_sub_ropen {N D n d : ℤ} (hn : n = D - N) (hd : d = D + N) (hN0 : 0 < N) (hND : N < D) (y : Site)
    (h : resRegion n d y) : CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T n d) y := by
  subst hn hd
  unfold resRegion FLatticePaper.W1.StrictInterior FLatticePaper.W1.w1b FLatticePaper.W1.w1T
    FLatticePaper.W1.w1t FLatticePaper.W1.w1a FLatticePaper.W1.w1s FLatticePaper.W1.w1h
    FLatticePaper.W1.w1c at h
  unfold CapConeGrades.ropenNL FLatticePaper.W1.w1T
  have hT0 : 2 * N < (D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2 := by nlinarith
  by_cases hy : EvenSite y
  · have hz : ¬ EvenSite (-y.2 + (D + N), y.1 - 1 + (D - N)) := by
      unfold EvenSite at hy ⊢
      dsimp only
      omega
    rw [if_pos hy]
    simp only [if_neg hz] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ring_nf at h1 h2 h3 h4 hT0 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hz : EvenSite (-y.2 + (D + N), y.1 - 1 + (D - N)) := by
      unfold EvenSite at hy ⊢
      dsimp only
      omega
    rw [if_neg hy]
    simp only [if_pos hz] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ring_nf at h1 h2 h3 h4 hT0 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Monotonicity of `ForcedEdgeIn` in the region: a derivation in `R` is one in any `R' ⊇ R`. -/
theorem forcedEdgeIn_mono {F : Field} {R R' : Site → Prop} (hRR : ∀ x, R x → R' x) {seed : Site → Site → Prop}
    {c o : Site} (h : W1.ForcedEdgeIn F R seed c o) : W1.ForcedEdgeIn F R' seed c o := by
  induction h with
  | seed hs => exact W1.ForcedEdgeIn.seed hs
  | @unit a b cc oo inside hR hc hw ho hout hin hforced ih =>
    exact W1.ForcedEdgeIn.unit inside (fun c' hc' => hRR c' (hR c' hc')) hc hw ho hout hin ih

theorem mem_squareCorners_translate (a b : ℤ) (U c : Site) :
    c ∈ AndOrRank.squareCorners (a - U.1) (b - U.2) ↔ c + U ∈ AndOrRank.squareCorners a b := by
  rw [FLatticePaper.FanCompat.mem_squareCorners_iff, FLatticePaper.FanCompat.mem_squareCorners_iff]
  simp only [Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor <;> omega

theorem incomingNeg_add (z U : Site) (hU : EvenSite U) : incomingNeg (z + U) = incomingNeg z + U := by
  have hU' : (U.1 + U.2) % 2 = 0 := hU
  unfold incomingNeg EvenSite
  by_cases h : (z.1 + z.2) % 2 = 0
  · have h' : ((z + U).1 + (z + U).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos h', if_pos h]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega
  · have h' : ¬ ((z + U).1 + (z + U).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg h', if_neg h]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega

theorem incomingPos_add (z U : Site) (hU : EvenSite U) : incomingPos (z + U) = incomingPos z + U := by
  have hU' : (U.1 + U.2) % 2 = 0 := hU
  unfold incomingPos EvenSite
  by_cases h : (z.1 + z.2) % 2 = 0
  · have h' : ((z + U).1 + (z + U).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos h', if_pos h]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega
  · have h' : ¬ ((z + U).1 + (z + U).2) % 2 = 0 := by
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg h', if_neg h]
    refine Prod.ext ?_ ?_
    all_goals simp only [Prod.fst_add, Prod.snd_add]
    all_goals omega

/-- The laplacian is invariant under an even period of the field. -/
theorem laplacian_add_period {F : Field} {U : Site} (hU : EvenSite U) (hper : ∀ z, F (z + U) = F z) (z : Site) :
    laplacian F (z + U) = laplacian F z := by
  unfold laplacian
  rw [incomingNeg_add z U hU, incomingPos_add z U hU, hper, hper, hper]

/-- **Translation of derivations by a period.** A `ForcedEdgeIn` derivation of `F` in `R` gives one in `R − U` (the region `z ↦ R (z + U)`)
for an even period `U` of `F`. -/
theorem forcedEdgeIn_translate {F : Field} {R : Site → Prop} {seed : Site → Site → Prop} {U : Site}
    (hU : EvenSite U) (hper : ∀ z, F (z + U) = F z) {c o : Site} (h : W1.ForcedEdgeIn F R seed c o) :
    W1.ForcedEdgeIn F (fun z => R (z + U)) (fun c o => seed (c + U) (o + U)) (c - U) (o - U) := by
  induction h with
  | seed hs =>
    exact W1.ForcedEdgeIn.seed (by simpa using hs)
  | @unit a b cc oo inside hR hc hw ho hout hin hforced ih =>
    refine W1.ForcedEdgeIn.unit (a := a - U.1) (b := b - U.2) (c := cc - U) (o := oo - U)
      (fun z => inside (z + U) - U) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro c' hc'
      exact hR (c' + U) ((mem_squareCorners_translate a b U c').mp hc')
    · exact (mem_squareCorners_translate a b U (cc - U)).mpr (by simpa using hc)
    · have := laplacian_add_period hU hper (cc - U)
      rw [sub_add_cancel] at this
      rw [← this]
      exact hw
    · have h1 := incomingNeg_add (cc - U) U hU
      have h2 := incomingPos_add (cc - U) U hU
      rw [sub_add_cancel] at h1 h2
      rcases ho with ho | ho
      · left
        rw [ho, h1, add_sub_cancel_right]
      · right
        rw [ho, h2, add_sub_cancel_right]
    · intro hmem
      exact hout (by simpa using (mem_squareCorners_translate a b U (oo - U)).mp hmem)
    · intro c' hc' hne
      have hc'' : c' + U ∈ AndOrRank.squareCorners a b := (mem_squareCorners_translate a b U c').mp hc'
      have hne' : c' + U ≠ cc := by
        intro e
        apply hne
        rw [← e, add_sub_cancel_right]
      rcases hin (c' + U) hc'' hne' with h1' | ⟨h0, hi1, hi2⟩
      · left
        rw [← laplacian_add_period hU hper c']
        exact h1'
      · right
        refine ⟨by rw [← laplacian_add_period hU hper c']; exact h0, ?_, ?_⟩
        · exact (mem_squareCorners_translate a b U _).mpr (by simpa using hi1)
        · have h1 := incomingNeg_add c' U hU
          have h2 := incomingPos_add c' U hU
          rcases hi2 with hi2 | hi2
          · left
            show inside (c' + U) - U = incomingNeg c'
            rw [hi2, h1, add_sub_cancel_right]
          · right
            show inside (c' + U) - U = incomingPos c'
            rw [hi2, h2, add_sub_cancel_right]
    · intro c' hc' hne h0
      have hc'' : c' + U ∈ AndOrRank.squareCorners a b := (mem_squareCorners_translate a b U c').mp hc'
      have hne' : c' + U ≠ cc := by
        intro e
        apply hne
        rw [← e, add_sub_cancel_right]
      have h0' : laplacian F (c' + U) = 0 := by
        rw [laplacian_add_period hU hper]
        exact h0
      have := ih (c' + U) hc'' hne' h0'
      simpa using this

/-- **The residual forcing on `E − U`.** A residual white point of the region `SI(Zs y + U)` is forced: the `W1Forced` derivation of `G` at
`Zs y + U` (translated back by `U`) is, by `forcedEdgeIn_Zs`, a derivation of the residual in the region `resRegion`. -/
theorem resRegion_forced {G : Field} {n d : ℤ} (hW1 : FLatticePaper.W1.W1Forced n d G) (hU : EvenSite (d, n))
    (hper : ∀ z : Site, G (z + (d, n)) = G z) (y : Site) (hy : resRegion n d y)
    (hw : laplacian (quarterTurnField G) y = 0) :
    ∃ o : Site, W1.ForcedEdgeIn (quarterTurnField G) (resRegion n d) (fun _ _ => False) y o := by
  have hz : FLatticePaper.W1.StrictInterior n d (Zs y + (d, n)) := hy
  have hG0 : laplacian G (Zs y + (d, n)) = 0 := by
    rw [laplacian_add_period hU hper, ← laplacian_quarterTurnField G y]
    exact hw
  obtain ⟨o', hD⟩ := hW1 _ hz hG0
  have hT := forcedEdgeIn_translate hU hper hD
  rw [add_sub_cancel_right] at hT
  exact ⟨Zinv (o' - (d, n)), forcedEdgeIn_Zs hT y _ rfl (Zs_Zinv (o' - (d, n))).symm⟩

/-- **The forced east start of the rotated fan, from `W1Forced G` on `E − U`.** The start lies in the residual region `SI(Zs · + U)` and is a
white contact (`hwhite`); its forced derivation is in the residual open rectangle (`resRegion_sub_ropen`), and `rotated_fan_start_D` says
that it leaves east. -/
theorem rotated_fan_start_W1 {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hodd : (D + N) % 2 = 1)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (K : ℕ) (hK2 : 2 ≤ K) (hKs : 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1)
    (b start : Site) (hb : N + 1 ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet
      (CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T fr.child.num fr.child.den)) (quarterTurnField G) b K)
    (heven : EvenSite start)
    (hR : resRegion fr.child.num fr.child.den start) :
    ∃ o : Site, W1.ForcedEdgeIn (quarterTurnField G)
        (CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T fr.child.num fr.child.den)) (fun _ _ => False) start o ∧
      o = incomingPos start := by
  have hU : EvenSite (fr.child.den, fr.child.num) := by
    unfold EvenSite
    dsimp only
    omega
  -- the start is white: an even contact of the cone window of the residual (the cap of `rotated_ray_cap_mono`)
  have hH := rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt
  obtain ⟨p, q, hs, hpq⟩ := CapRayGrades.ray_start_odd N D 1 (RotatedMono.coprime_residual fr N D hN2.symm hD2.symm) hodd
  obtain ⟨J, hJ1, hJ2⟩ := exists_floor_window (2 * N) (N + D - 2) (by omega) (by omega)
  have hcap := RotatedMono.rotated_ray_cap_mono hP hprice hdrU hdrV N D 1 (by norm_num) (by norm_num) hN2 hD2 hN0 hNDlt
    hs hpq J K hJ1 hJ2 hKr
  have hwin := CapConeGrades.cone_window_NL hH (FLatticePaper.W1.w1T fr.child.num fr.child.den) hN0 hNDlt (by norm_num)
    hs hpq K hcap b hb
  have hwhite : laplacian (quarterTurnField G) start = 0 :=
    FLatticePaper.FanRegion.contact_even_white_R (fun c => hH.binary c) hwin hstart heven
  obtain ⟨o, hD⟩ := resRegion_forced hW1 hU hper start hR hwhite
  have hmono := forcedEdgeIn_mono (fun x hx => resRegion_sub_ropen (N := N) (D := D) (n := fr.child.num)
    (d := fr.child.den) (by omega) (by omega) hN0 hNDlt x hx) hD
  exact ⟨o, hmono, rotated_fan_start_D hP hprice hdrU hdrV N D (FLatticePaper.W1.w1T fr.child.num fr.child.den) hN2 hD2
    hN0 hNDlt hodd K hK2 hKs hKr b start hb hstart heven hmono⟩

/-! ## The box of an odd free V root and the start in the residual region

For an odd site `z` of the closed polygon with `s(z)` in the V spectrum, the grades satisfy `n − T < t(z) < 2n − d` and `s(z) ≤ d + n − 2`
(`freeV_box_core`, integer arithmetic on `T y = n s − L t`). The start of the rotated fan is `(z.2, 1 − z.1)`, whose residual region is the
strict interior of `E − U` at `z + (−1, −1) + U`; that point is in the strict interior because of the box. -/

/-- Integer core of the V box: `n − T < t`, `t < 2n − d` and `s ≤ d + n − 2` for an odd point of the V spectrum on the closed polygon. -/
theorem freeV_box_core (n d T t s x y : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d * d + 2 * d * n - n * n) (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hodd : (x + y) % 2 = 1) (hE1 : n - T ≤ t) (hE2 : t ≤ d) (hE3 : 2 - d + n ≤ s)
    (hV : (0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2)) :
    n - T < t ∧ t < 2 * n - d ∧ s ≤ d + n - 2 := by
  have hy : T * y = n * s - (d + n) * t := by
    subst ht hs hT
    ring
  have hL : 0 < d + n := by omega
  have hdn : 0 < d * n := mul_pos (by omega) (by omega)
  have hsL : s ≤ d + n - 2 := by
    rcases hV with h | h <;> omega
  have hTpos : 0 < T := by
    rw [hT]
    nlinarith [mul_pos (show (0:ℤ) < d by omega) (show (0:ℤ) < d by omega),
      mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < n by omega), hdn]
  have hlow : n - T + 2 ≤ t := by
    by_contra hc
    have hk0 : 0 ≤ t - (n - T) := by linarith
    have hk1 : t - (n - T) ≤ 1 := by omega
    have key : T * (y - (d + n)) = n * (s - (d + n)) - (d + n) * (t - (n - T)) := by
      linear_combination hy
    have hA : n * (s - (d + n)) ≤ n * (-2) :=
      mul_le_mul_of_nonneg_left (show s - (d + n) ≤ -2 by omega) (show (0:ℤ) ≤ n by omega)
    have hB : n * (2 - 2 * d) ≤ n * (s - (d + n)) :=
      mul_le_mul_of_nonneg_left (show 2 - 2 * d ≤ s - (d + n) by omega) (show (0:ℤ) ≤ n by omega)
    have hk1' : (d + n) * (t - (n - T)) ≤ (d + n) * 1 := mul_le_mul_of_nonneg_left hk1 hL.le
    have hk0' : 0 ≤ (d + n) * (t - (n - T)) := mul_nonneg hL.le hk0
    have hpos : 0 < (d - n) * (d + n - 1) := mul_pos (by omega) (by omega)
    have hR1 : n * (s - (d + n)) - (d + n) * (t - (n - T)) < 0 := by linarith
    have hR2 : -T < n * (s - (d + n)) - (d + n) * (t - (n - T)) := by linarith
    rcases le_or_gt 0 (y - (d + n)) with hy0 | hy0
    · have h1 : 0 ≤ T * (y - (d + n)) := mul_nonneg hTpos.le hy0
      linarith
    · have hy1 : 0 ≤ -(y - (d + n)) - 1 := by omega
      have h1 : 0 ≤ T * (-(y - (d + n)) - 1) := mul_nonneg hTpos.le hy1
      linarith
  have hup : t < 2 * n - d := by
    by_contra hc
    have hc' : 2 * n - d ≤ t := by linarith
    have hyb1 : n * s ≤ n * (d + n - 2) := mul_le_mul_of_nonneg_left hsL (show (0:ℤ) ≤ n by omega)
    have hyb1' : (d + n) * (2 * n - d) ≤ (d + n) * t := mul_le_mul_of_nonneg_left hc' hL.le
    have hyb2 : n * (2 - d + n) ≤ n * s := mul_le_mul_of_nonneg_left hE3 (show (0:ℤ) ≤ n by omega)
    have hyb2' : (d + n) * t ≤ (d + n) * d := mul_le_mul_of_nonneg_left hE2 hL.le
    have hy_lt : T * y < T := by linarith
    have hy_gt : -T < T * y := by linarith
    have hy0 : y = 0 := by
      rcases lt_trichotomy y 0 with h | h | h
      · have h1 : y ≤ -1 := by omega
        have h2 : T * y ≤ T * (-1) := mul_le_mul_of_nonneg_left h1 hTpos.le
        linarith
      · exact h
      · have h1 : 1 ≤ y := by omega
        have h2 : T * 1 ≤ T * y := mul_le_mul_of_nonneg_left h1 hTpos.le
        linarith
    subst hy0
    have ht' : t = n * x := by rw [ht]; ring
    have hs' : s = (d + n) * x := by rw [hs]; ring
    have hx0 : x ≤ 0 := by
      by_contra hx
      have h1 : 1 ≤ x := by omega
      have h2 : (d + n) * 1 ≤ (d + n) * x := mul_le_mul_of_nonneg_left h1 hL.le
      linarith
    have hx1 : 0 ≤ x := by
      by_contra hx
      have h1 : x ≤ -1 := by omega
      have h2 : (d + n) * x ≤ (d + n) * (-1) := mul_le_mul_of_nonneg_left h1 hL.le
      linarith
    have hx : x = 0 := by omega
    subst hx
    omega
  exact ⟨by omega, hup, hsL⟩

/-- **The start of the rotated fan lies in the residual region.** For an odd site `z` of the closed polygon with `s(z)` in the V spectrum,
the residual start `(z.2, 1 − z.1)` (the image of `z + (−1, −1)`) lies in `resRegion`: the strict interior of `E − U` at `z + (−1, −1) + U`. -/
theorem resRegion_start_of_box (frame : ChildFrame) {z : Site} (hodd : ¬ EvenSite z)
    (hE : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2)
    (hS : frame.sGrade z % 2 = 0 ∧
      ((0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
        (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2))) :
    resRegion frame.child.num frame.child.den (z.2, 1 - z.1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hPT⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := by
    have h := frame.child_even
    unfold FLatticePaper.Farey.Fraction.Even at h
    omega
  have hT' : frame.child.periodDenominator
      = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num := by
    rw [hPT]
    ring
  have ht : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hs : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hodd
    omega
  have hcore := freeV_box_core frame.child.num frame.child.den frame.child.periodDenominator (frame.tGrade z)
    (frame.sGrade z) z.1 z.2 hn0 (by omega) hT' ht hs hodd' hE.1 hE.2.1 hE.2.2.1
    (by
      rcases hS.2 with h | h
      · exact Or.inl h
      · exact Or.inr h)
  obtain ⟨hlo, hup, hsL⟩ := hcore
  have hP : ¬ EvenSite (-(1 - z.1) + frame.child.den, z.2 - 1 + frame.child.num) := by
    unfold EvenSite
    dsimp only
    omega
  have hT4 : 4 * frame.child.den - 4 < frame.child.periodDenominator := by
    have h1 : 0 ≤ (frame.child.den - frame.child.num - 2) * (frame.child.den + frame.child.num) :=
      mul_nonneg (by omega) (by omega)
    have h2 : 0 ≤ frame.child.den * (frame.child.num - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [hT']
  unfold resRegion FLatticePaper.W1.StrictInterior FLatticePaper.W1.w1b FLatticePaper.W1.w1T
    FLatticePaper.W1.w1t FLatticePaper.W1.w1a FLatticePaper.W1.w1s FLatticePaper.W1.w1h
    FLatticePaper.W1.w1c
  dsimp only
  simp only [if_neg hP]
  rw [ht] at hlo hup
  rw [hs] at hsL
  rw [hs] at hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hT', hlo]
  · linarith [hup]
  · linarith [hT', hT4, hE.2.2.1]
  · linarith [hsL, hT']

/-- **The fan regime.** When `d < 2n` (the V NW-fan regime of Q23; for `d ≥ 2n` the non-fan squares cover every root), the depth
hypothesis `3N − 1 ≤ D` of the fan holds: `d < 2n` is `3N < D`. -/
theorem fan_regime_depth {N D n d : ℤ} (hn : n = D - N) (hd : d = D + N) (hlt : d < 2 * n) :
    3 * N - 1 ≤ D := by
  omega

/-- **The NW-fan start is a fan member.** For an odd V site `z` with `2 ≤ s(z) ≤ L − 2`, the residual start `(z.2, 1 − z.1)` belongs to the
fan of the apex `b = (z.2, −z.1)` at any depth `K ≥ 2`: it lies in the residual open rectangle, it is a cone root, and its residual value is
the parabola `capMin 1 = 0` (the zero window of `quarterTurnField G`, since `t'(start) = s(z)/2 − D`). -/
theorem nw_start_mem {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) {z : Site} (hodd : ¬ EvenSite z)
    (hs2 : 2 ≤ fr.sGrade z) (hsL : fr.sGrade z ≤ fr.child.den + fr.child.num - 2)
    (hR : resRegion fr.child.num fr.child.den (z.2, 1 - z.1)) (K : ℕ) (hK2 : 2 ≤ K) :
    (z.2, 1 - z.1) ∈ FLatticePaper.FanRegion.fanSet
      (CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T fr.child.num fr.child.den)) (quarterTurnField G)
      (z.2, -z.1) K := by
  have hsz : fr.sGrade z = 2 * (N * z.2 + D * z.1) := by
    have e : fr.sGrade z = (fr.child.den + fr.child.num) * z.1 + (fr.child.den - fr.child.num) * z.2 := rfl
    have h1 : fr.child.den + fr.child.num = 2 * D := by omega
    have h2 : fr.child.den - fr.child.num = 2 * N := by omega
    rw [e, h1, h2]
    ring
  have hn' : fr.child.num = D - N := by omega
  have hd' : fr.child.den = D + N := by omega
  have hopen : CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T fr.child.num fr.child.den) (z.2, 1 - z.1) :=
    resRegion_sub_ropen hn' hd' hN0 hNDlt (z.2, 1 - z.1) hR
  have hev : EvenSite (z.2, 1 - z.1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hcone : FLatticePaper.CapRay.ConeRoot (z.2, -z.1) K (z.2, 1 - z.1) := by
    unfold FLatticePaper.CapRay.ConeRoot
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hev h⟩
    · dsimp only
      omega
    · dsimp only
      omega
    · dsimp only
      omega
  have hzero : quarterTurnField G (z.2, 1 - z.1) = 0 := by
    apply (rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt).zero
    · show 1 - D ≤ N * z.2 - D * (1 - z.1)
      linarith
    · show N * z.2 - D * (1 - z.1) ≤ N + 2 * D - 1
      linarith
  refine ⟨⟨hopen, hcone⟩, ?_⟩
  unfold FLatticePaper.ContactCone.parabolaField
  rw [hzero]
  have e : (z.2, 1 - z.1).2 - (z.2, -z.1).2 = 1 := by
    dsimp only
    ring
  rw [e]
  norm_num [FLatticePaper.QuadraticCap.capMin]

/-- **The forced arrow of the rotated fan, in `G`.** The forced east start of the residual fan is the arrow `Zs start → Zs (incomingPos start)`
of the field `G` (the `ForcedEdge` of the minus-square's `R → Q`), and the start is white in `G`. -/
theorem rotated_fan_arrow_G {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (hW1 : FLatticePaper.W1.W1Forced fr.child.num fr.child.den G)
    (hper : ∀ z : Site, G (z + (fr.child.den, fr.child.num)) = G z)
    (N D : ℤ) (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) (hodd : (D + N) % 2 = 1)
    (K : ℕ) (hK2 : 2 ≤ K) (hKs : 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ))
    (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1)
    (b start : Site) (hb : N + 1 ≤ N * b.1 - D * b.2)
    (hstart : start ∈ FLatticePaper.FanRegion.fanSet
      (CapConeGrades.ropenNL N D (FLatticePaper.W1.w1T fr.child.num fr.child.den)) (quarterTurnField G) b K)
    (heven : EvenSite start) (hR : resRegion fr.child.num fr.child.den start) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (Zs start) (Zs (incomingPos start)) ∧
      laplacian G (Zs start) = 0 := by
  have hU : EvenSite (fr.child.den, fr.child.num) := by
    unfold EvenSite
    dsimp only
    omega
  have hn' : fr.child.num = D - N := by omega
  have hd' : fr.child.den = D + N := by omega
  have hH := rotated_NL hP hprice hdrU hdrV N D hN2 hD2 hN0 hNDlt
  obtain ⟨p, q, hs, hpq⟩ :=
    CapRayGrades.ray_start_odd N D 1 (RotatedMono.coprime_residual fr N D hN2.symm hD2.symm) hodd
  obtain ⟨J, hJ1, hJ2⟩ := exists_floor_window (2 * N) (N + D - 2) (by omega) (by omega)
  have hcap := RotatedMono.rotated_ray_cap_mono hP hprice hdrU hdrV N D 1 (by norm_num) (by norm_num) hN2 hD2 hN0 hNDlt
    hs hpq J K hJ1 hJ2 hKr
  have hwin := CapConeGrades.cone_window_NL hH (FLatticePaper.W1.w1T fr.child.num fr.child.den) hN0 hNDlt (by norm_num)
    hs hpq K hcap b hb
  have hwhite : laplacian (quarterTurnField G) start = 0 :=
    FLatticePaper.FanRegion.contact_even_white_R (fun c => hH.binary c) hwin hstart heven
  have hlapG : laplacian G (Zs start) = 0 := by
    rw [← laplacian_quarterTurnField G start]
    exact hwhite
  refine ⟨?_, hlapG⟩
  have hG0 : laplacian G (Zs start + (fr.child.den, fr.child.num)) = 0 := by
    rw [laplacian_add_period hU hper]
    exact hlapG
  have hzS : FLatticePaper.W1.StrictInterior fr.child.num fr.child.den (Zs start + (fr.child.den, fr.child.num)) := hR
  obtain ⟨o', hD⟩ := hW1 _ hzS hG0
  have hT := forcedEdgeIn_translate hU hper hD
  rw [add_sub_cancel_right] at hT
  have hres := forcedEdgeIn_Zs hT start (Zinv (o' - (fr.child.den, fr.child.num))) rfl
    (Zs_Zinv (o' - (fr.child.den, fr.child.num))).symm
  have hmono := forcedEdgeIn_mono
    (fun x hx => resRegion_sub_ropen (N := N) (D := D) (n := fr.child.num) (d := fr.child.den) hn' hd' hN0 hNDlt x hx) hres
  have hout := rotated_fan_start_D hP hprice hdrU hdrV N D (FLatticePaper.W1.w1T fr.child.num fr.child.den) hN2 hD2
    hN0 hNDlt hodd K hK2 hKs hKr b start hb hstart heven hmono
  have hfin : o' - (fr.child.den, fr.child.num) = Zs (incomingPos start) := by
    rw [← hout, Zs_Zinv]
  rw [hfin] at hT
  exact FLatticePaper.W1.forcedEdgeIn_forced hT

end FLatticePaper.RotatedForced
