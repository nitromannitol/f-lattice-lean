import FLatticePaper.Tiles.SiteStrings
import FLatticePaper.Tiles.SiteFwdCover
import FLatticePaper.Tiles.SiteVertCover
import FLatticePaper.Tiles.SiteUnique

/-! Task 53, item 4 (the hull assembly): the half-turn centre of a symmetric finite site set, and the symmetry of `H`.

A finite nonempty site set `T` symmetric under `z ↦ c − z` has `minX T + maxX T = c.1` and `minY T + maxY T = c.2`, so its half-turn
(`halfTurn` of `SiteStrings`) is the reflection `z ↦ c − z`. For the standard odd tile the symmetry centre is `R = U + V + (1, −1) =
(d + n + 1, 3n + d − 1)` (the rotation identity `rot_rot_oddTile`). -/

namespace FLatticePaper.Tiles.SiteHull

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings

theorem minX_le {T : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) : minX T ≤ z.1 := by
  unfold minX
  have h : ((T.image Prod.fst).min : WithTop ℤ) ≤ ↑z.1 :=
    Finset.min_le (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  cases hm : (T.image Prod.fst).min with
  | top => simp [hm] at h
  | coe a =>
    rw [hm] at h
    exact WithTop.coe_le_coe.mp h

theorem le_maxX {T : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) : z.1 ≤ maxX T := by
  unfold maxX
  have h : (↑z.1 : WithBot ℤ) ≤ (T.image Prod.fst).max :=
    Finset.le_max (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  cases hm : (T.image Prod.fst).max with
  | bot => simp [hm] at h
  | coe a =>
    rw [hm] at h
    exact WithBot.coe_le_coe.mp h

theorem exists_minX {T : Finset (ℤ × ℤ)} (hne : T.Nonempty) : ∃ z ∈ T, z.1 = minX T := by
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (hne.image Prod.fst)
  obtain ⟨z, hz, hz1⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
  refine ⟨z, hz, ?_⟩
  rw [hz1]
  unfold minX
  rw [hm]
  rfl

theorem exists_maxX {T : Finset (ℤ × ℤ)} (hne : T.Nonempty) : ∃ z ∈ T, z.1 = maxX T := by
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty (hne.image Prod.fst)
  obtain ⟨z, hz, hz1⟩ := Finset.mem_image.mp (Finset.mem_of_max hm)
  refine ⟨z, hz, ?_⟩
  rw [hz1]
  unfold maxX
  rw [hm]
  rfl

theorem minY_le {T : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) : minY T ≤ z.2 := by
  unfold minY
  have h : ((T.image Prod.snd).min : WithTop ℤ) ≤ ↑z.2 :=
    Finset.min_le (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  cases hm : (T.image Prod.snd).min with
  | top => simp [hm] at h
  | coe a =>
    rw [hm] at h
    exact WithTop.coe_le_coe.mp h

theorem le_maxY {T : Finset (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) : z.2 ≤ maxY T := by
  unfold maxY
  have h : (↑z.2 : WithBot ℤ) ≤ (T.image Prod.snd).max :=
    Finset.le_max (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  cases hm : (T.image Prod.snd).max with
  | bot => simp [hm] at h
  | coe a =>
    rw [hm] at h
    exact WithBot.coe_le_coe.mp h

theorem exists_minY {T : Finset (ℤ × ℤ)} (hne : T.Nonempty) : ∃ z ∈ T, z.2 = minY T := by
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (hne.image Prod.snd)
  obtain ⟨z, hz, hz1⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
  refine ⟨z, hz, ?_⟩
  rw [hz1]
  unfold minY
  rw [hm]
  rfl

theorem exists_maxY {T : Finset (ℤ × ℤ)} (hne : T.Nonempty) : ∃ z ∈ T, z.2 = maxY T := by
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty (hne.image Prod.snd)
  obtain ⟨z, hz, hz1⟩ := Finset.mem_image.mp (Finset.mem_of_max hm)
  refine ⟨z, hz, ?_⟩
  rw [hz1]
  unfold maxY
  rw [hm]
  rfl

/-- **The half-turn centre.** A finite nonempty site set symmetric under `z ↦ c − z` has half-turn centre `c`. -/
theorem halfTurnCentre_of_symm (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hne : T.Nonempty)
    (hsym : ∀ z ∈ T, (c.1 - z.1, c.2 - z.2) ∈ T) : halfTurnCentre T = c := by
  obtain ⟨z0, hz0, hz0x⟩ := exists_minX hne
  obtain ⟨z1, hz1, hz1x⟩ := exists_maxX hne
  obtain ⟨w0, hw0, hw0y⟩ := exists_minY hne
  obtain ⟨w1, hw1, hw1y⟩ := exists_maxY hne
  have hx1 : c.1 ≤ minX T + maxX T := by
    have := le_maxX (hsym z0 hz0)
    simp only at this
    omega
  have hx2 : minX T + maxX T ≤ c.1 := by
    have := minX_le (hsym z1 hz1)
    simp only at this
    omega
  have hy1 : c.2 ≤ minY T + maxY T := by
    have := le_maxY (hsym w0 hw0)
    simp only at this
    omega
  have hy2 : minY T + maxY T ≤ c.2 := by
    have := minY_le (hsym w1 hw1)
    simp only at this
    omega
  unfold halfTurnCentre
  exact Prod.ext (by simp only; omega) (by simp only; omega)

open FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction in
/-- **The symmetry of `H`.** For an odd fraction `f` (`num + den` odd), `z ∈ H_f` implies `R − z ∈ H_f` with
`R = (den + num + 1, 3 num + den − 1)`: `t(R − z) = L − T − t(z)` and `s(R − z) = 2T + 2N/2·... = 2T + 2num − s(z)`. -/
theorem inH_halfTurn (f : Fraction) (hodd : (f.num + f.den) % 2 = 1)
    (z : ℤ × ℤ) (hz : InH f z) :
    InH f (f.den + f.num + 1 - z.1, 3 * f.num + f.den - 1 - z.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hμ : muOf f = 2 := by
    unfold muOf
    rw [if_pos hodd]
  have ht' : tCo f (f.den + f.num + 1 - z.1, 3 * f.num + f.den - 1 - z.2) = (f.den + f.num) - tOf f - tCo f z := by
    unfold tCo tOf
    ring
  have hs' : sCo f (f.den + f.num + 1 - z.1, 3 * f.num + f.den - 1 - z.2) = 2 * tOf f + 2 * f.num - sCo f z := by
    unfold sCo tOf
    ring
  have hev : decide (((f.den + f.num + 1 - z.1) + (3 * f.num + f.den - 1 - z.2)) % 2 = 0) =
      decide ((z.1 + z.2) % 2 = 0) := by
    congr 1
    apply propext
    omega
  unfold InH
  simp only at hev ⊢
  rw [hev]
  rw [ht', hs', hμ]
  rw [hμ] at h4
  refine ⟨by omega, by omega, by omega, by omega⟩

end FLatticePaper.Tiles.SiteHull
