import FLatticePaper.Plane.Induction.CapRayGrades
import FLatticePaper.Plane.Induction.SheetRegions

/-! # The diagonal cap of the rotated residual (the long V case, `(N, D) = ((d−n)/2, (d+n)/2)`)

The residual `f = quarterTurnField G`, `f(x) = G(Zx) + h0(x)` with `Z(x, y) = (−y, x−1)`, is binary: its laplacian is the laplacian of
`G` at `Zx`, since `Z` interchanges the parity classes and the axes, and `h0` is harmonic (`laplacian_quarterTurnField`). Its strips
are the windows of `HasStrips G` read in the grades `(N, D)`: the zero window `1 − D ≤ Nx − Dy ≤ N + 2D − 1` is the sGrade window of `G`
at `Zx` (`sGrade(Zx) = 2(Nx − Dy) − 2N`), and the harmonic window `1 − 2D ≤ (D+N)x + (D−N)y ≤ 2(D+N) − 1` is the tGrade window at `Zx`
(`tGrade(Zx) = (D+N) − ((D+N)x + (D−N)y)`). The sheet monotonicities in the `(N, D)`-grades are named inputs (Q26). -/

namespace FLatticePaper.RotatedCap

open FLatticePaper FLatticePaper.Induction FLatticePaper.CapRayGrades FLatticePaper.CapRecursion

/-- The quarter-turn offset `Z(x, y) = (−y, x − 1)`. -/
def Zs (x : Site) : Site := (-x.2, x.1 - 1)

theorem mapSite_eq_Zs (x : Site) : QuarterTurn.counterclockwise.mapSite (0, -1) x = Zs x := by
  ext <;> simp [QuarterTurn.mapSite, QuarterTurn.turn, Zs, sub_eq_add_neg]

/-- The laplacian of `G ∘ Z` is the laplacian of `G` at `Zx`: `Z` maps the horizontal neighbours of an even site to the vertical
neighbours of its odd image, and conversely. -/
theorem laplacian_comp_Zs (G : Field) (x : Site) : laplacian (fun y => G (Zs y)) x = laplacian G (Zs x) := by
  by_cases hx : EvenSite x
  · have hZ : ¬ EvenSite (Zs x) := by
      unfold EvenSite at hx ⊢
      simp only [Zs]
      omega
    unfold laplacian
    rw [incomingNeg_of_even' x hx, incomingPos_of_even' x hx,
      incomingNeg_of_odd' (Zs x) hZ, incomingPos_of_odd' (Zs x) hZ]
    simp only [Zs]
    ring_nf
  · have hZ : EvenSite (Zs x) := by
      unfold EvenSite at hx ⊢
      simp only [Zs]
      omega
    unfold laplacian
    rw [incomingNeg_of_odd' x hx, incomingPos_of_odd' x hx,
      incomingNeg_of_even' (Zs x) hZ, incomingPos_of_even' (Zs x) hZ]
    simp only [Zs]
    ring_nf

/-- **The residual is binary**: its laplacian is that of `G` at `Zx`, since `h0` is harmonic. -/
theorem laplacian_quarterTurnField (G : Field) (x : Site) :
    laplacian (quarterTurnField G) x = laplacian G (Zs x) := by
  have h1 : quarterTurnField G = fun y => G (Zs y) + harmonicGrid y := by
    funext y
    unfold quarterTurnField
    rw [mapSite_eq_Zs]
  rw [h1]
  have hadd : laplacian (fun y => G (Zs y) + harmonicGrid y) x
      = laplacian (fun y => G (Zs y)) x + laplacian harmonicGrid x := by
    unfold laplacian
    ring
  rw [hadd, laplacian_comp_Zs, harmonicGrid_harmonic, add_zero]

/-- **The diagonal cap of the rotated residual.** For the rotated grades `(N, D)` of a child frame `(n, d)` (`2N = d − n`,
`2D = d + n`), with `0 < N < D`, the residual of the standard field `G` satisfies the cap on the ray `(p+k, q+k)` with
`N p − D q = 2 − N`, `p + q` odd, for `k ≤ K`. The strips are those of `G` (`frame.HasStrips G`), the binary laplacian is that of `G`;
the two sheet monotonicities of the residual in the `(N, D)`-grades are the named inputs `hodd`, `heven` (Q26). -/
theorem rotated_ray_cap {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G)
    (hbin : ∀ x : Site, laplacian G x = -1 ∨ laplacian G x = 0)
    (N D : ℤ) (hN2 : 2 * N = frame.child.den - frame.child.num) (hD2 : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hNDlt : N < D)
    (hodd : ∀ u v : Site, ¬ EvenSite u → ¬ EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
      N * v.1 - D * v.2 ≤ 0 → quarterTurnField G u ≤ quarterTurnField G v)
    (heven : ∀ u v : Site, EvenSite u → EvenSite v → N * u.1 - D * u.2 ≤ N * v.1 - D * v.2 →
      N * v.1 - D * v.2 ≤ 0 → quarterTurnField G u ≤ quarterTurnField G v)
    {p q : ℤ} (hs : N * p - D * q = 2 - N) (hpq : (p + q) % 2 = 1)
    (J K : ℕ)
    (hJ1 : 2 * N * (J : ℤ) ≤ N + D - 2)
    (hJ2 : N + D - 2 < 2 * N * ((J : ℤ) + 1))
    (hK : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ quarterTurnField G (p + (k : ℤ), q + (k : ℤ)) := by
  have hden : frame.child.den = N + D := by omega
  have hnum : frame.child.num = D - N := by omega
  apply CapRayGrades.ray_cap_NDgrades N D hN0 hNDlt
  · intro x
    rw [laplacian_quarterTurnField]
    exact hbin _
  · intro w h1 h2
    apply FLatticePaper.Induction.quarterTurnField_eq_zero hS
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
  · intro w h1 h2
    apply FLatticePaper.Induction.quarterTurnField_eq_harmonic hS
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
  · exact hodd
  · exact heven
  · exact hs
  · exact hpq
  · exact hJ1
  · exact hJ2
  · exact hK

end FLatticePaper.RotatedCap
