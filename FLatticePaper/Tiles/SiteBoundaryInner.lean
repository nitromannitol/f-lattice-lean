import FLatticePaper.Tiles.SiteBoundaryCover

/-! Task 53, item 4 (inner boundary): every site of `H` with a unit neighbour outside `H` is a mark.

The neighbour `e = z + δ` leaves `H` through one of its four window edges. A violation of the upper `t` edge gives the
`t_hi` witness at `z` (`−n < t`, and `0 < t` for even sites), so `z` is a forward mark (`sh_hi`). A violation of the lower
`s` edge gives the `s_lo` witness at `z` (`s < L` for odd sites, `s < 2d` for even sites), so `z` is a vertical mark (`sv_hi`).
The lower `t` edge and the upper `s` edge are the upper `t` and lower `s` edges of the half-turn image `R − z`, whose neighbour is
`R − e`; the reflected marks are `mem_marksOdd_of_sh_refl` and `mem_marksOdd_of_sv_refl` (and their even analogues). -/

namespace FLatticePaper.Tiles.SiteBoundaryInner

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction
  FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SiteHullEven FLatticePaper.Tiles.SiteBoundaryCover
  FLatticePaper.Tiles.SiteHull

theorem mem_unitNeighbours_iff (z e : ℤ × ℤ) :
    e ∈ unitNeighbours z ↔ ∃ δ1 δ2 : ℤ,
      ((δ1 = 1 ∧ δ2 = 0) ∨ (δ1 = -1 ∧ δ2 = 0) ∨ (δ1 = 0 ∧ δ2 = 1) ∨ (δ1 = 0 ∧ δ2 = -1)) ∧
        e = (z.1 + δ1, z.2 + δ2) := by
  constructor
  · intro h
    simp only [unitNeighbours, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨1, 0, Or.inl ⟨rfl, rfl⟩, by simp⟩
    · exact ⟨-1, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), Prod.ext (by ring) (by ring)⟩
    · exact ⟨0, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), by simp⟩
    · exact ⟨0, -1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Prod.ext (by ring) (by ring)⟩
  · rintro ⟨δ1, δ2, hδ, rfl⟩
    rcases hδ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [unitNeighbours, sub_eq_add_neg]

/-- The upper `t` edge violated by a unit neighbour gives the `t_hi` witness. -/
theorem wit_t (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (z e : ℤ × ℤ) (δ1 δ2 : ℤ)
    (hδ : (δ1 = 1 ∧ δ2 = 0) ∨ (δ1 = -1 ∧ δ2 = 0) ∨ (δ1 = 0 ∧ δ2 = 1) ∨ (δ1 = 0 ∧ δ2 = -1))
    (he1 : e.1 = z.1 + δ1) (he2 : e.2 = z.2 + δ2)
    (hv : f.den + f.num - aOf f (decide ((e.1 + e.2) % 2 = 0)) < tCo f e) :
    -f.num < tCo f z ∧ ((z.1 + z.2) % 2 = 0 → 0 < tCo f z) := by
  have key : tCo f e = tCo f z + f.num * δ1 - f.den * δ2 := by
    unfold tCo
    rw [he1, he2]
    ring
  rw [key, he1, he2] at hv
  rcases hδ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · unfold aOf at hv
    split_ifs at hv with hP <;> simp only [decide_eq_true_eq] at hP <;>
      exact ⟨by omega, fun h => by omega⟩

/-- The lower `s` edge violated by a unit neighbour gives the `s_lo` witness. -/
theorem wit_s (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (z e : ℤ × ℤ) (δ1 δ2 : ℤ)
    (hδ : (δ1 = 1 ∧ δ2 = 0) ∨ (δ1 = -1 ∧ δ2 = 0) ∨ (δ1 = 0 ∧ δ2 = 1) ∨ (δ1 = 0 ∧ δ2 = -1))
    (he1 : e.1 = z.1 + δ1) (he2 : e.2 = z.2 + δ2)
    (hv : sCo f e < lOf f (decide ((e.1 + e.2) % 2 = 0))) :
    ((z.1 + z.2) % 2 = 1 → sCo f z < f.den + f.num) ∧ ((z.1 + z.2) % 2 = 0 → sCo f z < 2 * f.den) := by
  have key : sCo f e = sCo f z + (f.den + f.num) * δ1 + (f.den - f.num) * δ2 := by
    unfold sCo
    rw [he1, he2]
    ring
  rw [key, he1, he2] at hv
  rcases hδ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · unfold lOf at hv
    split_ifs at hv with hP <;> simp only [decide_eq_true_eq] at hP <;>
      exact ⟨fun h => by omega, fun h => by omega⟩

theorem decide_mod_two_eq (a b : ℤ) (h : a % 2 = b % 2) : decide (a % 2 = 0) = decide (b % 2 = 0) := by
  rw [h]

/-- The half-turn of the odd tile: `t(R − e) = L − T − t(e)`. -/
theorem tCo_refl_odd (f : Fraction) (e : ℤ × ℤ) :
    tCo f (f.den + f.num + 1 - e.1, 3 * f.num + f.den - 1 - e.2) = (f.den + f.num) - tOf f - tCo f e := by
  simp only [tCo, tOf]
  ring

/-- The half-turn of the odd tile: `s(R − e) = 2T + N − s(e)`. -/
theorem sCo_refl_odd (f : Fraction) (e : ℤ × ℤ) :
    sCo f (f.den + f.num + 1 - e.1, 3 * f.num + f.den - 1 - e.2) = 2 * tOf f + 2 * f.num - sCo f e := by
  simp only [sCo, tOf]
  ring

/-- The half-turn of the even tile: `t(R' − e) = L − T − t(e)`. -/
theorem tCo_refl_even (f : Fraction) (e : ℤ × ℤ) :
    tCo f (f.num + 1 - e.1, 2 * f.num + f.den - 1 - e.2) = (f.den + f.num) - tOf f - tCo f e := by
  simp only [tCo, tOf]
  ring

/-- The half-turn of the even tile: `s(R' − e) = T + N − s(e)`. -/
theorem sCo_refl_even (f : Fraction) (e : ℤ × ℤ) :
    sCo f (f.num + 1 - e.1, 2 * f.num + f.den - 1 - e.2) = tOf f + 2 * f.num - sCo f e := by
  simp only [sCo, tOf]
  ring

/-- The lower `t` edge violated by the neighbour `e` of `z` is the upper `t` edge of `R − e` at `R − z`. -/
theorem wit_t_refl (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (R1 R2 : ℤ)
    (hR : ∀ p : ℤ × ℤ, tCo f (R1 - p.1, R2 - p.2) = (f.den + f.num) - tOf f - tCo f p)
    (hpar : (R1 + R2) % 2 = 0) (z e : ℤ × ℤ) (δ1 δ2 : ℤ)
    (hδ : (δ1 = 1 ∧ δ2 = 0) ∨ (δ1 = -1 ∧ δ2 = 0) ∨ (δ1 = 0 ∧ δ2 = 1) ∨ (δ1 = 0 ∧ δ2 = -1))
    (he1 : e.1 = z.1 + δ1) (he2 : e.2 = z.2 + δ2)
    (hviol : tCo f e < aOf f (decide ((e.1 + e.2) % 2 = 0)) - tOf f) :
    -f.num < tCo f (R1 - z.1, R2 - z.2) ∧
      ((R1 - z.1 + (R2 - z.2)) % 2 = 0 → 0 < tCo f (R1 - z.1, R2 - z.2)) := by
  have hδ' : (-δ1 = 1 ∧ -δ2 = 0) ∨ (-δ1 = -1 ∧ -δ2 = 0) ∨ (-δ1 = 0 ∧ -δ2 = 1) ∨ (-δ1 = 0 ∧ -δ2 = -1) := by
    rcases hδ with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hd : decide ((((R1 - e.1, R2 - e.2) : ℤ × ℤ).1 + ((R1 - e.1, R2 - e.2) : ℤ × ℤ).2) % 2 = 0) =
      decide ((e.1 + e.2) % 2 = 0) :=
    decide_mod_two_eq _ _ (by show (R1 - e.1 + (R2 - e.2)) % 2 = (e.1 + e.2) % 2; omega)
  have hv' : f.den + f.num - aOf f (decide ((((R1 - e.1, R2 - e.2) : ℤ × ℤ).1 +
      ((R1 - e.1, R2 - e.2) : ℤ × ℤ).2) % 2 = 0)) < tCo f (R1 - e.1, R2 - e.2) := by
    rw [hd, hR e]
    omega
  exact wit_t f hn hnd (R1 - z.1, R2 - z.2) (R1 - e.1, R2 - e.2) (-δ1) (-δ2) hδ'
    (by show R1 - e.1 = (R1 - z.1) + -δ1; omega) (by show R2 - e.2 = (R2 - z.2) + -δ2; omega) hv'

/-- The upper `s` edge violated by the neighbour `e` of `z` is the lower `s` edge of `R − e` at `R − z`. -/
theorem wit_s_refl (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (R1 R2 K : ℤ)
    (hR : ∀ p : ℤ × ℤ, sCo f (R1 - p.1, R2 - p.2) = K - sCo f p) (hpar : (R1 + R2) % 2 = 0)
    (z e : ℤ × ℤ) (δ1 δ2 : ℤ)
    (hδ : (δ1 = 1 ∧ δ2 = 0) ∨ (δ1 = -1 ∧ δ2 = 0) ∨ (δ1 = 0 ∧ δ2 = 1) ∨ (δ1 = 0 ∧ δ2 = -1))
    (he1 : e.1 = z.1 + δ1) (he2 : e.2 = z.2 + δ2)
    (hviol : K - lOf f (decide ((e.1 + e.2) % 2 = 0)) < sCo f e) :
    ((R1 - z.1 + (R2 - z.2)) % 2 = 1 → sCo f (R1 - z.1, R2 - z.2) < f.den + f.num) ∧
      ((R1 - z.1 + (R2 - z.2)) % 2 = 0 → sCo f (R1 - z.1, R2 - z.2) < 2 * f.den) := by
  have hδ' : (-δ1 = 1 ∧ -δ2 = 0) ∨ (-δ1 = -1 ∧ -δ2 = 0) ∨ (-δ1 = 0 ∧ -δ2 = 1) ∨ (-δ1 = 0 ∧ -δ2 = -1) := by
    rcases hδ with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hd : decide ((((R1 - e.1, R2 - e.2) : ℤ × ℤ).1 + ((R1 - e.1, R2 - e.2) : ℤ × ℤ).2) % 2 = 0) =
      decide ((e.1 + e.2) % 2 = 0) :=
    decide_mod_two_eq _ _ (by show (R1 - e.1 + (R2 - e.2)) % 2 = (e.1 + e.2) % 2; omega)
  have hv' : sCo f (R1 - e.1, R2 - e.2) < lOf f (decide ((((R1 - e.1, R2 - e.2) : ℤ × ℤ).1 +
      ((R1 - e.1, R2 - e.2) : ℤ × ℤ).2) % 2 = 0)) := by
    rw [hd, hR e]
    omega
  exact wit_s f hn hnd (R1 - z.1, R2 - z.2) (R1 - e.1, R2 - e.2) (-δ1) (-δ2) hδ'
    (by show R1 - e.1 = (R1 - z.1) + -δ1; omega) (by show R2 - e.2 = (R2 - z.2) + -δ2; omega) hv'

/-- **The inner boundary of the odd tile is marked.** A site of `H_{curO w}` with a unit neighbour outside `H` is a marked site. -/
theorem bd_odd_mem (w : Word) (z : ℤ × ℤ) (hz : InH (curO w) z) (e : ℤ × ℤ) (he : e ∈ unitNeighbours z)
    (hout : ¬ InH (curO w) e) : z ∈ marksOdd w := by
  have hpos := curO_pos_lt w
  have hodd : ((curO w).num + (curO w).den) % 2 = 1 := curO_odd w
  have hμ : muOf (curO w) = 2 := by
    unfold muOf
    rw [if_pos hodd]
  obtain ⟨δ1, δ2, hδ, hep⟩ := (mem_unitNeighbours_iff z e).mp he
  have he1 : e.1 = z.1 + δ1 := by rw [hep]
  have he2 : e.2 = z.2 + δ2 := by rw [hep]
  unfold InH at hout
  by_cases h1 : tCo (curO w) e ≤ (curO w).den + (curO w).num - aOf (curO w) (decide ((e.1 + e.2) % 2 = 0))
  · by_cases h2 : aOf (curO w) (decide ((e.1 + e.2) % 2 = 0)) - tOf (curO w) ≤ tCo (curO w) e
    · by_cases h3 : lOf (curO w) (decide ((e.1 + e.2) % 2 = 0)) ≤ sCo (curO w) e
      · have h4 : ¬ (sCo (curO w) e ≤ muOf (curO w) * tOf (curO w) + 2 * (curO w).num -
            lOf (curO w) (decide ((e.1 + e.2) % 2 = 0))) := fun h => hout ⟨h2, h1, h3, h⟩
        rw [hμ] at h4
        obtain ⟨hs1, hs2⟩ := wit_s_refl (curO w) hpos.1 hpos.2 ((curO w).den + (curO w).num + 1)
          (3 * (curO w).num + (curO w).den - 1) (2 * tOf (curO w) + 2 * (curO w).num)
          (fun p => sCo_refl_odd (curO w) p) (by omega) z e δ1 δ2 hδ he1 he2 (not_le.mp h4)
        exact mem_marksOdd_of_sv_refl w z (sv_hi_odd w _ (inH_halfTurn (curO w) hodd z hz) hs1 hs2)
      · obtain ⟨hs1, hs2⟩ := wit_s (curO w) hpos.1 hpos.2 z e δ1 δ2 hδ he1 he2 (not_le.mp h3)
        exact mem_marksOdd_of_sv w z (sv_hi_odd w z hz hs1 hs2)
    · obtain ⟨htl, hte⟩ := wit_t_refl (curO w) hpos.1 hpos.2 ((curO w).den + (curO w).num + 1)
        (3 * (curO w).num + (curO w).den - 1) (fun p => tCo_refl_odd (curO w) p) (by omega) z e δ1 δ2 hδ he1 he2
        (not_le.mp h2)
      exact mem_marksOdd_of_sh_refl w z (sh_hi_odd w _ (inH_halfTurn (curO w) hodd z hz) htl hte)
  · obtain ⟨htl, hte⟩ := wit_t (curO w) hpos.1 hpos.2 z e δ1 δ2 hδ he1 he2 (not_le.mp h1)
    exact mem_marksOdd_of_sh w z (sh_hi_odd w z hz htl hte)

/-- **The inner boundary of the even tile is marked.** -/
theorem bd_even_mem (w : Word) (z : ℤ × ℤ) (hz : InH (curE w) z) (e : ℤ × ℤ) (he : e ∈ unitNeighbours z)
    (hout : ¬ InH (curE w) e) : z ∈ marksEven w := by
  have hpos := curE_pos_lt w
  have heven : ((curE w).num + (curE w).den) % 2 = 0 := curE_num_add_den_even w
  have hμ : muOf (curE w) = 1 := by
    unfold muOf
    rw [if_neg (by omega)]
  obtain ⟨δ1, δ2, hδ, hep⟩ := (mem_unitNeighbours_iff z e).mp he
  have he1 : e.1 = z.1 + δ1 := by rw [hep]
  have he2 : e.2 = z.2 + δ2 := by rw [hep]
  unfold InH at hout
  by_cases h1 : tCo (curE w) e ≤ (curE w).den + (curE w).num - aOf (curE w) (decide ((e.1 + e.2) % 2 = 0))
  · by_cases h2 : aOf (curE w) (decide ((e.1 + e.2) % 2 = 0)) - tOf (curE w) ≤ tCo (curE w) e
    · by_cases h3 : lOf (curE w) (decide ((e.1 + e.2) % 2 = 0)) ≤ sCo (curE w) e
      · have h4 : ¬ (sCo (curE w) e ≤ muOf (curE w) * tOf (curE w) + 2 * (curE w).num -
            lOf (curE w) (decide ((e.1 + e.2) % 2 = 0))) := fun h => hout ⟨h2, h1, h3, h⟩
        rw [hμ, one_mul] at h4
        obtain ⟨hs1, hs2⟩ := wit_s_refl (curE w) hpos.1 hpos.2 ((curE w).num + 1)
          (2 * (curE w).num + (curE w).den - 1) (tOf (curE w) + 2 * (curE w).num)
          (fun p => sCo_refl_even (curE w) p) (by omega) z e δ1 δ2 hδ he1 he2 (not_le.mp h4)
        exact mem_marksEven_of_sv_refl w z (sv_hi_even w _ (inH_halfTurn_even (curE w) heven z hz) hs1 hs2)
      · obtain ⟨hs1, hs2⟩ := wit_s (curE w) hpos.1 hpos.2 z e δ1 δ2 hδ he1 he2 (not_le.mp h3)
        exact mem_marksEven_of_sv w z (sv_hi_even w z hz hs1 hs2)
    · obtain ⟨htl, hte⟩ := wit_t_refl (curE w) hpos.1 hpos.2 ((curE w).num + 1)
        (2 * (curE w).num + (curE w).den - 1) (fun p => tCo_refl_even (curE w) p) (by omega) z e δ1 δ2 hδ he1 he2
        (not_le.mp h2)
      exact mem_marksEven_of_sh_refl w z (sh_hi_even w _ (inH_halfTurn_even (curE w) heven z hz) htl hte)
  · obtain ⟨htl, hte⟩ := wit_t (curE w) hpos.1 hpos.2 z e δ1 δ2 hδ he1 he2 (not_le.mp h1)
    exact mem_marksEven_of_sh w z (sh_hi_even w z hz htl hte)

/-- **Boundary, odd tile.** The inner boundary of `H_{curO w}` lies in the marks of `w`. -/
theorem boundary_odd (w : Word) : innerBd (HSet (curO w)) ⊆ marksOdd w := by
  rintro z ⟨hz, e, he, hout⟩
  exact bd_odd_mem w z hz e he hout

/-- **Boundary, even tile.** The inner boundary of `H_{curE w}` lies in the marks of `w`. -/
theorem boundary_even (w : Word) : innerBd (HSet (curE w)) ⊆ marksEven w := by
  rintro z ⟨hz, e, he, hout⟩
  exact bd_even_mem w z hz e he hout

end FLatticePaper.Tiles.SiteBoundaryInner
