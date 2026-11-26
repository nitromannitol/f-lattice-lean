import FLatticePaper.Plane.Induction.AlignedClassSite
import FLatticePaper.Plane.Induction.BoundarySpectrum

/-! # The boundary spectrum at lattice points (step (3) of the top-square argument)

A closed integer site with an exterior 4-neighbour is a free H point, a free V point, a free V point translated by the kernel
`K = (d,n)`, or a free H point translated by the transverse vector `V = (n-d,n+d)`. The grade-level statement is
`BoundarySpectrum.spectrum_even`/`spectrum_odd` (which needs no strictness); here the site predicates are translated to the grades
of the site and of its neighbours. -/

namespace FLatticePaper.BoundarySite

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CrossingLattice
  FLatticePaper.BoundarySpectrum

theorem closedRect_iff_E {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site)
    (hy : w1t n d y % 2 = 0) :
    closedRect n d y ↔ EvenRect n d (w1T n d) (w1t n d y) (w1s n d y) := by
  have h : EvenSite y := by
    unfold EvenSite
    have := parity_w1t hn hd y
    omega
  unfold EvenRect
  exact cR_even h

theorem closedRect_iff_O {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site)
    (hy : w1t n d y % 2 = 1) :
    closedRect n d y ↔ OddRect n d (w1T n d) (w1t n d y) (w1s n d y) := by
  have h : ¬ EvenSite y := by
    unfold EvenSite
    have := parity_w1t hn hd y
    omega
  unfold OddRect
  exact cR_odd h

/-! ## Neighbours: the grades of an exterior neighbour -/

theorem nc_of_notO {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (a b : ℤ)
    (ha : w1t n d y = a) (hb : w1s n d y = b) (hodd : a % 2 = 1)
    (h : ¬ OddRect n d (w1T n d) a b) : ¬ closedRect n d y := by
  intro hc
  apply h
  have hy : w1t n d y % 2 = 1 := by rw [ha]; exact hodd
  have := (closedRect_iff_O hn hd y hy).mp hc
  rw [ha, hb] at this
  exact this

theorem notO_of_nc {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (a b : ℤ)
    (ha : w1t n d y = a) (hb : w1s n d y = b) (hodd : a % 2 = 1)
    (h : ¬ closedRect n d y) : ¬ OddRect n d (w1T n d) a b := by
  intro hO
  apply h
  have hy : w1t n d y % 2 = 1 := by rw [ha]; exact hodd
  rw [closedRect_iff_O hn hd y hy, ha, hb]
  exact hO

theorem nc_of_notE {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (a b : ℤ)
    (ha : w1t n d y = a) (hb : w1s n d y = b) (hev : a % 2 = 0)
    (h : ¬ EvenRect n d (w1T n d) a b) : ¬ closedRect n d y := by
  intro hc
  apply h
  have hy : w1t n d y % 2 = 0 := by rw [ha]; exact hev
  have := (closedRect_iff_E hn hd y hy).mp hc
  rw [ha, hb] at this
  exact this

theorem notE_of_nc {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (a b : ℤ)
    (ha : w1t n d y = a) (hb : w1s n d y = b) (hev : a % 2 = 0)
    (h : ¬ closedRect n d y) : ¬ EvenRect n d (w1T n d) a b := by
  intro hE
  apply h
  have hy : w1t n d y % 2 = 0 := by rw [ha]; exact hev
  rw [closedRect_iff_E hn hd y hy, ha, hb]
  exact hE

/-! ## Back to free points -/

theorem freeVn_E {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (hy : w1t n d y % 2 = 0)
    (hC : EvenRect n d (w1T n d) (w1t n d y) (w1s n d y))
    (hL : ¬ OddRect n d (w1T n d) (w1t n d y - n) (w1s n d y - (d + n)))
    (hV : VSp n d (w1s n d y)) : freeVn n d y := by
  have hLc : ¬ closedRect n d (y.1 - 1, y.2) :=
    nc_of_notO hn hd (y.1 - 1, y.2) (w1t n d y - n) (w1s n d y - (d + n))
      (by unfold w1t; ring) (by unfold w1s; ring) (by omega) hL
  exact ⟨(closedRect_iff_E hn hd y hy).mpr hC, hLc, ⟨parity_w1s hn hd y, hV⟩⟩

theorem freeHn_E {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (hy : w1t n d y % 2 = 0)
    (hC : EvenRect n d (w1T n d) (w1t n d y) (w1s n d y))
    (hH : HSpE n d (w1t n d y))
    (hD : ¬ OddRect n d (w1T n d) (w1t n d y + d) (w1s n d y - (d - n))) : freeHn n d y := by
  have hDc : ¬ closedRect n d (y.1, y.2 - 1) :=
    nc_of_notO hn hd (y.1, y.2 - 1) (w1t n d y + d) (w1s n d y - (d - n))
      (by unfold w1t; ring) (by unfold w1s; ring) (by omega) hD
  exact ⟨(closedRect_iff_E hn hd y hy).mpr hC, hDc, Or.inl ⟨hy, hH.1, hH.2⟩⟩

theorem freeVn_O {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (hy : w1t n d y % 2 = 1)
    (hC : OddRect n d (w1T n d) (w1t n d y) (w1s n d y))
    (hL : ¬ EvenRect n d (w1T n d) (w1t n d y - n) (w1s n d y - (d + n)))
    (hV : VSp n d (w1s n d y)) : freeVn n d y := by
  have hLc : ¬ closedRect n d (y.1 - 1, y.2) :=
    nc_of_notE hn hd (y.1 - 1, y.2) (w1t n d y - n) (w1s n d y - (d + n))
      (by unfold w1t; ring) (by unfold w1s; ring) (by omega) hL
  exact ⟨(closedRect_iff_O hn hd y hy).mpr hC, hLc, ⟨parity_w1s hn hd y, hV⟩⟩

theorem freeHn_O {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (y : Site) (hy : w1t n d y % 2 = 1)
    (hC : OddRect n d (w1T n d) (w1t n d y) (w1s n d y))
    (hH : HSpO n d (w1t n d y))
    (hD : ¬ EvenRect n d (w1T n d) (w1t n d y + d) (w1s n d y - (d - n))) : freeHn n d y := by
  have hDc : ¬ closedRect n d (y.1, y.2 - 1) :=
    nc_of_notE hn hd (y.1, y.2 - 1) (w1t n d y + d) (w1s n d y - (d - n))
      (by unfold w1t; ring) (by unfold w1s; ring) (by omega) hD
  exact ⟨(closedRect_iff_O hn hd y hy).mpr hC, hDc, Or.inr ⟨hy, hH.1, hH.2⟩⟩

/-! ## The spectrum at a site, by the parity of `w1t` -/

theorem spectrum_site_even {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < w1T n d) (z : Site) (hz : w1t n d z % 2 = 0) (hC : closedRect n d z)
    (hX : ¬ closedRect n d (z.1 + 1, z.2) ∨ ¬ closedRect n d (z.1 - 1, z.2) ∨
      ¬ closedRect n d (z.1, z.2 + 1) ∨ ¬ closedRect n d (z.1, z.2 - 1)) :
    freeHn n d z ∨ freeVn n d z ∨ freeVn n d (z.1 - d, z.2 - n) ∨
      freeHn n d (z.1 - (n - d), z.2 - (n + d)) := by
  have hT2 := parity_w1T hn hd
  have hs := parity_w1s hn hd z
  have hE := (closedRect_iff_E hn hd z hz).mp hC
  have hex : ¬ OddRect n d (w1T n d) (w1t n d z - n) (w1s n d z - (d + n)) ∨
      ¬ OddRect n d (w1T n d) (w1t n d z + n) (w1s n d z + (d + n)) ∨
      ¬ OddRect n d (w1T n d) (w1t n d z + d) (w1s n d z - (d - n)) ∨
      ¬ OddRect n d (w1T n d) (w1t n d z - d) (w1s n d z + (d - n)) := by
    rcases hX with h | h | h | h
    · right; left
      exact notO_of_nc hn hd (z.1 + 1, z.2) (w1t n d z + n) (w1s n d z + (d + n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · left
      exact notO_of_nc hn hd (z.1 - 1, z.2) (w1t n d z - n) (w1s n d z - (d + n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · right; right; right
      exact notO_of_nc hn hd (z.1, z.2 + 1) (w1t n d z - d) (w1s n d z + (d - n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · right; right; left
      exact notO_of_nc hn hd (z.1, z.2 - 1) (w1t n d z + d) (w1s n d z - (d - n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
  have eK : w1t n d (z.1 - d, z.2 - n) = w1t n d z := by unfold w1t; ring
  have eKs : w1s n d (z.1 - d, z.2 - n) = w1s n d z - w1T n d := by unfold w1s w1T; ring
  have eV : w1t n d (z.1 - (n - d), z.2 - (n + d)) = w1t n d z + w1T n d := by unfold w1t w1T; ring
  have eVs : w1s n d (z.1 - (n - d), z.2 - (n + d)) = w1s n d z := by unfold w1s; ring
  rcases spectrum_even n d (w1T n d) (w1t n d z) (w1s n d z) hn1 hnd hn hd hTL hT2 hz hs hE hex with
    ⟨hH, hNd⟩ | ⟨hV, hNl⟩ | ⟨hE', hV', hNl'⟩ | ⟨hE'', hH', hNd'⟩
  · exact Or.inl (freeHn_E hn hd z hz hE hH hNd)
  · exact Or.inr (Or.inl (freeVn_E hn hd z hz hE hNl hV))
  · refine Or.inr (Or.inr (Or.inl ?_))
    refine freeVn_E hn hd (z.1 - d, z.2 - n) (by rw [eK]; exact hz) ?_ ?_ ?_
    · rw [eK, eKs]; exact hE'
    · rw [eK, eKs]; exact hNl'
    · rw [eKs]; exact hV'
  · refine Or.inr (Or.inr (Or.inr ?_))
    refine freeHn_E hn hd (z.1 - (n - d), z.2 - (n + d)) (by rw [eV]; omega) ?_ ?_ ?_
    · rw [eV, eVs]; exact hE''
    · rw [eV]; exact hH'
    · rw [eV, eVs]; exact hNd'

theorem spectrum_site_odd {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < w1T n d) (z : Site) (hz : w1t n d z % 2 = 1) (hC : closedRect n d z)
    (hX : ¬ closedRect n d (z.1 + 1, z.2) ∨ ¬ closedRect n d (z.1 - 1, z.2) ∨
      ¬ closedRect n d (z.1, z.2 + 1) ∨ ¬ closedRect n d (z.1, z.2 - 1)) :
    freeHn n d z ∨ freeVn n d z ∨ freeVn n d (z.1 - d, z.2 - n) ∨
      freeHn n d (z.1 - (n - d), z.2 - (n + d)) := by
  have hT2 := parity_w1T hn hd
  have hs := parity_w1s hn hd z
  have hO := (closedRect_iff_O hn hd z hz).mp hC
  have hex : ¬ EvenRect n d (w1T n d) (w1t n d z - n) (w1s n d z - (d + n)) ∨
      ¬ EvenRect n d (w1T n d) (w1t n d z + n) (w1s n d z + (d + n)) ∨
      ¬ EvenRect n d (w1T n d) (w1t n d z + d) (w1s n d z - (d - n)) ∨
      ¬ EvenRect n d (w1T n d) (w1t n d z - d) (w1s n d z + (d - n)) := by
    rcases hX with h | h | h | h
    · right; left
      exact notE_of_nc hn hd (z.1 + 1, z.2) (w1t n d z + n) (w1s n d z + (d + n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · left
      exact notE_of_nc hn hd (z.1 - 1, z.2) (w1t n d z - n) (w1s n d z - (d + n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · right; right; right
      exact notE_of_nc hn hd (z.1, z.2 + 1) (w1t n d z - d) (w1s n d z + (d - n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
    · right; right; left
      exact notE_of_nc hn hd (z.1, z.2 - 1) (w1t n d z + d) (w1s n d z - (d - n))
        (by unfold w1t; ring) (by unfold w1s; ring) (by omega) h
  have eK : w1t n d (z.1 - d, z.2 - n) = w1t n d z := by unfold w1t; ring
  have eKs : w1s n d (z.1 - d, z.2 - n) = w1s n d z - w1T n d := by unfold w1s w1T; ring
  have eV : w1t n d (z.1 - (n - d), z.2 - (n + d)) = w1t n d z + w1T n d := by unfold w1t w1T; ring
  have eVs : w1s n d (z.1 - (n - d), z.2 - (n + d)) = w1s n d z := by unfold w1s; ring
  rcases spectrum_odd n d (w1T n d) (w1t n d z) (w1s n d z) hn1 hnd hn hd hTL hT2 hz hs hO hex with
    ⟨hH, hNd⟩ | ⟨hV, hNl⟩ | ⟨hO', hV', hNl'⟩ | ⟨hO'', hH', hNd'⟩
  · exact Or.inl (freeHn_O hn hd z hz hO hH hNd)
  · exact Or.inr (Or.inl (freeVn_O hn hd z hz hO hNl hV))
  · refine Or.inr (Or.inr (Or.inl ?_))
    refine freeVn_O hn hd (z.1 - d, z.2 - n) (by rw [eK]; exact hz) ?_ ?_ ?_
    · rw [eK, eKs]; exact hO'
    · rw [eK, eKs]; exact hNl'
    · rw [eKs]; exact hV'
  · refine Or.inr (Or.inr (Or.inr ?_))
    refine freeHn_O hn hd (z.1 - (n - d), z.2 - (n + d)) (by rw [eV]; omega) ?_ ?_ ?_
    · rw [eV, eVs]; exact hO''
    · rw [eV]; exact hH'
    · rw [eV, eVs]; exact hNd'

/-- **The boundary spectrum at lattice points.** A closed integer site with an exterior 4-neighbour is free H, free V, free V
translated by `K = (d,n)`, or free H translated by `V = (n-d,n+d)`. -/
theorem spectrum_site {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTL : 2 * (d + n) < w1T n d) (z : Site) (hC : closedRect n d z)
    (hX : ¬ closedRect n d (z.1 + 1, z.2) ∨ ¬ closedRect n d (z.1 - 1, z.2) ∨
      ¬ closedRect n d (z.1, z.2 + 1) ∨ ¬ closedRect n d (z.1, z.2 - 1)) :
    freeHn n d z ∨ freeVn n d z ∨ freeVn n d (z.1 - d, z.2 - n) ∨
      freeHn n d (z.1 - (n - d), z.2 - (n + d)) := by
  rcases (show w1t n d z % 2 = 0 ∨ w1t n d z % 2 = 1 by omega) with hz | hz
  · exact spectrum_site_even hn hd hn1 hnd hTL z hz hC hX
  · exact spectrum_site_odd hn hd hn1 hnd hTL z hz hC hX

end FLatticePaper.BoundarySite
