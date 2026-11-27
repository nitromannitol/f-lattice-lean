import FLatticePaper.Tiles.PartialBoundary
import FLatticePaper.Tiles.ZeroOneH0
import FLatticePaper.Tiles.SurgicalAffineChain

/-! Lemma A(b) of the standard decompositions (condition (C)), the vertical zero-one constancy with `h_0`.

For a vertical zero-one tile of letter `l` and orientation `rev`, the canonical position is `cstarV l rev` (the tile
position at which the base identity holds with `h_0` at the argument `u + cstarV`), and `linV l rev` is the affine term of
that identity (`a_{1/1,2} = (1, -1)` for the reversed `p`-tile). The tile at `cstarV + d` has affine factor
`linV - ℓ(d)` with `ℓ(d) = (p, q)`, `2p = -d_1 - d_2`, `2q = d_2 - d_1`, and the identity `canon_tile` says that
`o(x) + h_0(x) - (affine factor)·x` is constant on the tile, equal to `vV l rev u` plus an explicit constant. -/

namespace FLatticePaper.Tiles

/-- The canonical position of a tile of letter `l` in a vertical string of orientation `rev`. -/
def cstarV : Letter → Bool → Site
  | .p, false => (-1, -1)
  | .p, true => (0, 1)
  | .q, _ => (0, 0)

/-- The affine term of the canonical identity of a tile of letter `l` (`a_{1/1,2} = (1, -1)` for a reversed `p` tile). -/
def linV : Letter → Bool → Site
  | .p, true => (1, -1)
  | _, _ => (0, 0)

/-- The vertical boundary function `v_i^±` of a tile of letter `l` (`v_0^+ = -1{u=0}`, `v_0^- = -1{u=1+2i}`, `v_1 = 0`). -/
def vV : Letter → Bool → Site → ℤ
  | .p, false => fun u => if u = (0, 0) then -1 else 0
  | .p, true => fun u => if u = (1, 2) then -1 else 0
  | .q, _ => fun _ => 0

/-- The canonical identity: for `u` in the tile of letter `l`, the base odometer plus the affine term at the canonical
position plus `h_0` at the canonical position equals `v_i^±(u)`. -/
theorem canonV (l : Letter) (rev : Bool) (u : Site) (hu : u ∈ tileShape (letterZTile l)) :
    zTileOdo (letterZTile l) u + (linV l rev).1 * (u + cstarV l rev).1 + (linV l rev).2 * (u + cstarV l rev).2 +
        zoH0 (u + cstarV l rev) = vV l rev u := by
  have key : ∀ v ∈ tileShape (letterZTile l),
      zTileOdo (letterZTile l) v + (linV l rev).1 * (v + cstarV l rev).1 + (linV l rev).2 * (v + cstarV l rev).2 +
          zoH0 (v + cstarV l rev) = vV l rev v := by
    cases l <;> cases rev <;> decide
  exact key u hu

/-- The translated identity: for the tile of letter `l` at the position `cstarV l rev + d` with `d` of even coordinate
sum, the odometer with affine factor `linV - ℓ(d)` plus `h_0` is `v_i^±(u)` plus a constant `C(d)` independent of `u`. -/
theorem canonV_tile (l : Letter) (rev : Bool) (d : Site) (p q : ℤ) (hd : (d.1 + d.2) % 2 = 0)
    (hp : 2 * p = -d.1 - d.2) (hq : 2 * q = d.2 - d.1) (u : Site) (hu : u ∈ tileShape (letterZTile l)) :
    zTileOdo (letterZTile l) u + ((linV l rev).1 - p) * (u.1 + (cstarV l rev + d).1) +
        ((linV l rev).2 - q) * (u.2 + (cstarV l rev + d).2) + zoH0 (u + (cstarV l rev + d)) =
      vV l rev u + ((linV l rev).1 * d.1 + (linV l rev).2 * d.2) - (p * d.1 + q * d.2) + zoH0 d := by
  have hcan := canonV l rev u hu
  have hs := zoH0_shift_even (u + cstarV l rev) d p q hp hq hd
  have e : u + cstarV l rev + d = u + (cstarV l rev + d) := by abel
  rw [e] at hs
  simp only [Prod.fst_add, Prod.snd_add] at hs hcan ⊢
  linear_combination hcan + hs

/-- The step of the canonical positions along a vertical string: the offset of the next tile, `vOffset` for the
forward string and `vRevOffset` for the reversed one. -/
def stepV (rev : Bool) (l l' : Letter) : Site := if rev then vRevOffset l l' else vOffset l'

/-- `ℓ(d) = (p, q)` of the manuscript: `2p = -d_1 - d_2`, `2q = d_2 - d_1` for `d` of even coordinate sum. -/
def ellV (d : Site) : Site := ((-d.1 - d.2) / 2, (d.2 - d.1) / 2)

theorem ellV_spec (d : Site) (h : (d.1 + d.2) % 2 = 0) :
    2 * (ellV d).1 = -d.1 - d.2 ∧ 2 * (ellV d).2 = d.2 - d.1 := by
  unfold ellV
  constructor <;> simp only <;> omega

/-- The affine factor of the tile of letter `l` at `cstarV l rev + d`, relative to the common factor `a_0`. -/
def Acl (l : Letter) (rev : Bool) (d : Site) : Site := ((linV l rev).1 - (ellV d).1, (linV l rev).2 - (ellV d).2)

/-- The constant of the tile of letter `l` at `cstarV l rev + d`: the value of `o + h_0 - a·x - v` on the tile. -/
def Cl (l : Letter) (rev : Bool) (d : Site) : ℤ :=
  (linV l rev).1 * d.1 + (linV l rev).2 * d.2 - ((ellV d).1 * d.1 + (ellV d).2 * d.2) + zoH0 d

/-- The tile identity with the explicit factor and constant: on the tile of letter `l` at `cstarV l rev + d`,
`o(u) + Acl·x + h_0(x) = v(u) + Cl`, with `x = u + (cstarV + d)`. -/
theorem tile_identity (l : Letter) (rev : Bool) (d : Site) (hd : (d.1 + d.2) % 2 = 0) (u : Site)
    (hu : u ∈ tileShape (letterZTile l)) :
    zTileOdo (letterZTile l) u + (Acl l rev d).1 * (u.1 + (cstarV l rev + d).1) +
        (Acl l rev d).2 * (u.2 + (cstarV l rev + d).2) + zoH0 (u + (cstarV l rev + d)) =
      vV l rev u + Cl l rev d := by
  obtain ⟨hp, hq⟩ := ellV_spec d hd
  have key := canonV_tile l rev d (ellV d).1 (ellV d).2 hd hp hq u hu
  unfold Acl Cl
  linear_combination key

/-- The slope of the `k`-th odometer of a partial family: the base slope of its tile plus its affine factor. -/
theorem odo_slope (F : PTFamily) (k : ℕ) :
    slopeOf (F.odo k) (F.dom k) = zTileBaseSlope (F.tile k).1 + (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  have hodo : F.odo k = fun y => zTileOdo (F.tile k).1 (y - (F.tile k).2) + (F.a k).1 * y.1 +
      (F.a k).2 * y.2 + F.b k := rfl
  have hT : F.dom k = (tileShape (F.tile k).1).map (· + (F.tile k).2) := rfl
  rw [hodo, hT, slopeOf_translate_affine _ _ _ _ _ (unitSquares_tileShape_ne _)]
  rfl

/-- The table of the vertical slope changes, as affine factors: the change of the affine factor between consecutive
tiles of letters `l, l'` is `(lin' - lin) - ℓ(δ)` with `δ` the change of the canonical-relative position. -/
theorem vert_table (l l' : Letter) (rev : Bool) :
    surgicalSlopeDiff .vertical rev (zTileLetter (letterZTile l)) (zTileLetter (letterZTile l')) -
        (zTileBaseSlope (letterZTile l') - zTileBaseSlope (letterZTile l)) =
      ((((linV l' rev).1 - (linV l rev).1 - (ellV (stepV rev l l' - (cstarV l' rev - cstarV l rev))).1 : ℤ) : ℚ),
        (((linV l' rev).2 - (linV l rev).2 - (ellV (stepV rev l l' - (cstarV l' rev - cstarV l rev))).2 : ℤ) : ℚ)) := by
  cases l <;> cases l' <;> cases rev <;>
    simp [surgicalSlopeDiff, zTileLetter, letterZTile, zTileBaseSlope_zero, zTileBaseSlope_one, stepV, vRevOffset,
      vOffset, cstarV, linV, ellV] <;>
    norm_num

theorem ellV_add (d e : Site) (hd : (d.1 + d.2) % 2 = 0) (he : (e.1 + e.2) % 2 = 0) :
    ellV (d + e) = ellV d + ellV e := by
  unfold ellV
  ext <;> simp <;> omega

/-- The step `δ = stepV - (cstar' - cstar)` has even coordinate sum in every case. -/
theorem stepV_parity (l l' : Letter) (rev : Bool) :
    ((stepV rev l l' - (cstarV l' rev - cstarV l rev)).1 + (stepV rev l l' - (cstarV l' rev - cstarV l rev)).2) % 2 = 0 := by
  cases l <;> cases l' <;> cases rev <;> decide

/-- The consecutive-pair identity of `h_0` at a point of the one tile: `h_0(p + (0,2)) - h_0(p + (0,1)) - ℓ_2(p) = 1`
for `p` of even coordinate sum, with `ℓ_2(p) = (p_2 - p_1)/2`. -/
theorem zoH0_qq_aux (a b : ℤ) (h : (a + b) % 2 = 0) :
    zoH0 (a, b + 2) - zoH0 (a, b + 1) - (b - a) / 2 = 1 := by
  have h4a := zoH0_four (a, b + 2)
  have h4b := zoH0_four (a, b + 1)
  simp only at h4a h4b
  have p1 : (a + (b + 2)) % 2 = 0 := by omega
  have p2 : (a + (b + 1)) % 2 = 1 := by omega
  rw [p1] at h4a
  rw [p2] at h4b
  obtain ⟨t, ht⟩ : ∃ t, b - a = 2 * t := ⟨(b - a) / 2, by omega⟩
  have hq : (b - a) / 2 = t := by omega
  rw [hq]
  have h4 : 4 * (zoH0 (a, b + 2) - zoH0 (a, b + 1) - t - 1) = 0 := by
    linear_combination h4a - h4b + 2 * ht
  have := (mul_eq_zero.mp h4).resolve_left (by norm_num)
  linarith

theorem zoH0_qq (P : Site) (h : (P.1 + P.2) % 2 = 0) :
    zoH0 (P + (0, 2)) - zoH0 (P + (0, 1)) - (P.2 - P.1) / 2 = 1 := by
  obtain ⟨a, b⟩ := P
  have := zoH0_qq_aux a b h
  simpa using this

/-- The invariant at a point of the `k`-th tile: `o_k(P + u) + h_0(P + u) - a_0·(P+u) = v(u) + K` for `u` in the tile. -/
theorem inv_point (F : PTFamily) (rev : Bool) (k : ℕ) (l : Letter) (hT : (F.tile k).1 = letterZTile l) (a0 : GInt)
    (K : ℤ) (ha : F.a k = a0 + Acl l rev ((F.tile k).2 - cstarV l rev)) (hb : F.b k + Cl l rev ((F.tile k).2 - cstarV l rev) = K)
    (hd : (((F.tile k).2 - cstarV l rev).1 + ((F.tile k).2 - cstarV l rev).2) % 2 = 0) (u : Site)
    (hu : u ∈ tileShape (letterZTile l)) :
    F.odo k ((F.tile k).2 + u) + zoH0 ((F.tile k).2 + u) - ((a0.1 : ℤ) * ((F.tile k).2 + u).1 + a0.2 * ((F.tile k).2 + u).2) =
      vV l rev u + K := by
  have e := tile_identity l rev ((F.tile k).2 - cstarV l rev) hd u hu
  have hc : cstarV l rev + ((F.tile k).2 - cstarV l rev) = (F.tile k).2 := by abel
  rw [hc, add_comm u] at e
  have hodo : F.odo k ((F.tile k).2 + u) = zTileOdo (letterZTile l) u + (F.a k).1 * ((F.tile k).2 + u).1 +
      (F.a k).2 * ((F.tile k).2 + u).2 + F.b k := by
    unfold PTFamily.odo
    rw [hT]
    simp
  rw [hodo, ha]
  simp only [Prod.fst_add, Prod.snd_add] at e ⊢
  rw [← hb]
  unfold Acl Cl at *
  linear_combination e

theorem vz_letter (l : Letter) : zTileLetter (letterZTile l) = l := by
  cases l <;> rfl

/-- The affine factor of the first coordinate changes by the table value along a consecutive pair of tiles. -/
theorem a_step_fst (F : PTFamily) (rev : Bool) (k : ℕ) (l l' : Letter) (hk : k + 1 < F.n)
    (hR : F.Respects .vertical rev) (hTk : (F.tile k).1 = letterZTile l) (hTk1 : (F.tile (k + 1)).1 = letterZTile l') :
    (((F.a (k + 1)).1 : ℤ) : ℚ) - (((F.a k).1 : ℤ) : ℚ) =
      ((((linV l' rev).1 - (linV l rev).1 - (ellV (stepV rev l l' - (cstarV l' rev - cstarV l rev))).1 : ℤ)) : ℚ) := by
  have h := (hR k hk).1
  rw [odo_slope F (k + 1), odo_slope F k, hTk, hTk1] at h
  have h1 := congrArg Prod.fst h
  have hv := congrArg Prod.fst (vert_table l l' rev)
  simp only [Prod.fst_sub, Prod.fst_add, vz_letter] at h1 hv
  linarith

theorem a_step_snd (F : PTFamily) (rev : Bool) (k : ℕ) (l l' : Letter) (hk : k + 1 < F.n)
    (hR : F.Respects .vertical rev) (hTk : (F.tile k).1 = letterZTile l) (hTk1 : (F.tile (k + 1)).1 = letterZTile l') :
    (((F.a (k + 1)).2 : ℤ) : ℚ) - (((F.a k).2 : ℤ) : ℚ) =
      ((((linV l' rev).2 - (linV l rev).2 - (ellV (stepV rev l l' - (cstarV l' rev - cstarV l rev))).2 : ℤ)) : ℚ) := by
  have h := (hR k hk).1
  rw [odo_slope F (k + 1), odo_slope F k, hTk, hTk1] at h
  have h1 := congrArg Prod.snd h
  have hv := congrArg Prod.snd (vert_table l l' rev)
  simp only [Prod.snd_sub, Prod.snd_add, vz_letter] at h1 hv
  linarith

/-- The constant at an overlap point of two consecutive tiles: the common value forces `b_{k+1} + C_{k+1} = K`. -/
theorem b_overlap (F : PTFamily) (rev : Bool) (k : ℕ) (l l' : Letter) (a0 : GInt) (K : ℤ)
    (hTk : (F.tile k).1 = letterZTile l) (hTk1 : (F.tile (k + 1)).1 = letterZTile l')
    (hpos : (F.tile (k + 1)).2 = (F.tile k).2 + stepV rev l l')
    (hd : (((F.tile k).2 - cstarV l rev).1 + ((F.tile k).2 - cstarV l rev).2) % 2 = 0)
    (ha : F.a k = a0 + Acl l rev ((F.tile k).2 - cstarV l rev))
    (hb : F.b k + Cl l rev ((F.tile k).2 - cstarV l rev) = K)
    (ha' : F.a (k + 1) = a0 + Acl l' rev ((F.tile (k + 1)).2 - cstarV l' rev))
    (hW : ∀ x ∈ F.dom k, x ∈ F.dom (k + 1) → F.odo k x = F.odo (k + 1) x)
    (w : Site) (hw : w ∈ tileShape (letterZTile l)) (hw' : w - stepV rev l l' ∈ tileShape (letterZTile l'))
    (hv : vV l rev w = 0) (hv' : vV l' rev (w - stepV rev l l') = 0) :
    F.b (k + 1) + Cl l' rev ((F.tile (k + 1)).2 - cstarV l' rev) = K := by
  have hd' : ((((F.tile (k + 1)).2 - cstarV l' rev).1 + ((F.tile (k + 1)).2 - cstarV l' rev).2) % 2 = 0) := by
    have e : (F.tile (k + 1)).2 - cstarV l' rev =
        ((F.tile k).2 - cstarV l rev) + (stepV rev l l' - (cstarV l' rev - cstarV l rev)) := by
      rw [hpos]; abel
    have hp := stepV_parity l l' rev
    rw [e]
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hd hp ⊢
    omega
  have hz : (F.tile k).2 + w ∈ F.dom k := by
    unfold PTFamily.dom
    rw [hTk, chain_mem_map_add_iff]
    simpa using hw
  have hz' : (F.tile k).2 + w ∈ F.dom (k + 1) := by
    unfold PTFamily.dom
    rw [hTk1, chain_mem_map_add_iff, hpos]
    have e : (F.tile k).2 + w - ((F.tile k).2 + stepV rev l l') = w - stepV rev l l' := by abel
    rw [e]
    exact hw'
  have hW' := hW _ hz hz'
  have i1 := inv_point F rev k l hTk a0 K ha hb hd w hw
  have i2 := inv_point F rev (k + 1) l' hTk1 a0 (F.b (k + 1) + Cl l' rev ((F.tile (k + 1)).2 - cstarV l' rev))
    ha' rfl hd' (w - stepV rev l l') hw'
  have e2 : (F.tile (k + 1)).2 + (w - stepV rev l l') = (F.tile k).2 + w := by rw [hpos]; abel
  rw [e2] at i2
  rw [hW'] at i1
  rw [hv] at i1
  rw [hv'] at i2
  linarith

/-- The constant across a `q`–`q` step (the tiles are non-overlapping, the offset is `(0,2)`): the adjacency rule of
`Respects` at the unit-apart pair `P + (0,1)`, `P + (0,2)` gives `b_{k+1} + C_{k+1} = K`, by `zoH0_qq`. -/
theorem b_adj (F : PTFamily) (rev : Bool) (k : ℕ) (a0 : GInt) (K : ℤ) (hk : k + 1 < F.n)
    (hR : F.Respects .vertical rev)
    (hTk : (F.tile k).1 = letterZTile .q) (hTk1 : (F.tile (k + 1)).1 = letterZTile .q)
    (hpos : (F.tile (k + 1)).2 = (F.tile k).2 + stepV rev .q .q)
    (hd : (((F.tile k).2 - cstarV .q rev).1 + ((F.tile k).2 - cstarV .q rev).2) % 2 = 0)
    (ha : F.a k = a0 + Acl .q rev ((F.tile k).2 - cstarV .q rev))
    (hb : F.b k + Cl .q rev ((F.tile k).2 - cstarV .q rev) = K)
    (ha' : F.a (k + 1) = a0 + Acl .q rev ((F.tile (k + 1)).2 - cstarV .q rev)) :
    F.b (k + 1) + Cl .q rev ((F.tile (k + 1)).2 - cstarV .q rev) = K := by
  have hs : stepV rev .q .q = (0, 2) := by cases rev <;> rfl
  have hcs : cstarV .q rev = (0, 0) := by cases rev <;> rfl
  have hl : linV .q rev = (0, 0) := by cases rev <;> rfl
  have hv0 : ∀ u, vV .q rev u = 0 := fun u => by cases rev <;> rfl
  have hPc : (F.tile k).2 - cstarV .q rev = (F.tile k).2 := by rw [hcs]; ext <;> simp
  rw [hs] at hpos
  have hP : ((F.tile k).2.1 + (F.tile k).2.2) % 2 = 0 := by
    have h := hd
    rw [hPc] at h
    exact h
  have hx : (F.tile k).2 + (0, 1) ∈ F.dom k := by
    unfold PTFamily.dom
    rw [hTk, chain_mem_map_add_iff]
    have e : (F.tile k).2 + (0, 1) - (F.tile k).2 = (0, 1) := by abel
    rw [e]
    decide
  have hy : (F.tile k).2 + (0, 2) ∈ F.dom (k + 1) := by
    unfold PTFamily.dom
    rw [hTk1, chain_mem_map_add_iff, hpos, sub_self]
    decide
  have hnon : ¬∃ z, z ∈ F.dom k ∧ z ∈ F.dom (k + 1) := by
    rintro ⟨z, h1, h2⟩
    unfold PTFamily.dom at h1 h2
    rw [hTk, chain_mem_map_add_iff] at h1
    rw [hTk1, chain_mem_map_add_iff, hpos] at h2
    simp only [letterZTile, tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_add, Prod.snd_add] at h1 h2
    omega
  have hu : unitApart ((F.tile k).2 + (0, 1)) ((F.tile k).2 + (0, 2)) := by
    unfold unitApart
    simp only [Prod.fst_add, Prod.snd_add]
    norm_num
  have hadj := ((hR k hk).2 hnon _ hx _ hy hu).2 rfl
  have hx1 : (0, 1) ∈ tileShape (letterZTile .q) := by decide
  have hy1 : (0, 0) ∈ tileShape (letterZTile .q) := by decide
  have hd' : ((((F.tile (k + 1)).2 - cstarV .q rev).1 + ((F.tile (k + 1)).2 - cstarV .q rev).2) % 2 = 0) := by
    rw [hpos, hcs]
    norm_num [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    omega
  have ix := inv_point F rev k .q hTk a0 K ha hb hd (0, 1) hx1
  have iy := inv_point F rev (k + 1) .q hTk1 a0 (F.b (k + 1) + Cl .q rev ((F.tile (k + 1)).2 - cstarV .q rev)) ha' rfl
    hd' (0, 0) hy1
  have e : (F.tile (k + 1)).2 + (0, 0) = (F.tile k).2 + (0, 2) := by rw [hpos]; abel
  rw [e, hv0] at iy
  rw [hv0] at ix
  rw [ha, hPc] at hadj
  unfold ptDot Acl at hadj
  simp only [Prod.fst_add, Prod.snd_add, hl] at hadj
  unfold ellV at hadj
  have zq := zoH0_qq (F.tile k).2 hP
  simp only [Prod.fst_add, Prod.snd_add] at ix iy
  linear_combination ix - iy + hadj + zq

/-- The affine factor of the next tile: `a_{k+1} = a_0 + Acl(l', d_{k+1})`, from the slope clause and the parity of
the canonical-relative position. -/
theorem a_step_eq (F : PTFamily) (rev : Bool) (k : ℕ) (l l' : Letter) (a0 : GInt) (hk : k + 1 < F.n)
    (hR : F.Respects .vertical rev) (hTk : (F.tile k).1 = letterZTile l) (hTk1 : (F.tile (k + 1)).1 = letterZTile l')
    (hpos : (F.tile (k + 1)).2 = (F.tile k).2 + stepV rev l l')
    (hd : (((F.tile k).2 - cstarV l rev).1 + ((F.tile k).2 - cstarV l rev).2) % 2 = 0)
    (ha : F.a k = a0 + Acl l rev ((F.tile k).2 - cstarV l rev)) :
    F.a (k + 1) = a0 + Acl l' rev ((F.tile (k + 1)).2 - cstarV l' rev) := by
  set d := (F.tile k).2 - cstarV l rev with hdef
  set δ := stepV rev l l' - (cstarV l' rev - cstarV l rev) with hδdef
  have hdd : (F.tile (k + 1)).2 - cstarV l' rev = d + δ := by
    rw [hpos, hdef, hδdef]; abel
  have hdp : (δ.1 + δ.2) % 2 = 0 := stepV_parity l l' rev
  have e := ellV_add d δ hd hdp
  have f1 := a_step_fst F rev k l l' hk hR hTk hTk1
  have f2 := a_step_snd F rev k l l' hk hR hTk hTk1
  rw [← hδdef] at f1 f2
  have ha1 : (F.a k).1 = a0.1 + ((linV l rev).1 - (ellV d).1) := by rw [ha]; simp [Acl]
  have ha2 : (F.a k).2 = a0.2 + ((linV l rev).2 - (ellV d).2) := by rw [ha]; simp [Acl]
  have ha1q : (((F.a k).1 : ℤ) : ℚ) = ((a0.1 + ((linV l rev).1 - (ellV d).1) : ℤ) : ℚ) := by rw [ha1]
  have ha2q : (((F.a k).2 : ℤ) : ℚ) = ((a0.2 + ((linV l rev).2 - (ellV d).2) : ℤ) : ℚ) := by rw [ha2]
  have g1 : (F.a (k + 1)).1 = a0.1 + ((linV l' rev).1 - ((ellV d).1 + (ellV δ).1)) := by
    have h : (((F.a (k + 1)).1 : ℤ) : ℚ) =
        ((a0.1 + ((linV l' rev).1 - ((ellV d).1 + (ellV δ).1)) : ℤ) : ℚ) := by
      push_cast at ha1q f1 ⊢
      linarith
    exact_mod_cast h
  have g2 : (F.a (k + 1)).2 = a0.2 + ((linV l' rev).2 - ((ellV d).2 + (ellV δ).2)) := by
    have h : (((F.a (k + 1)).2 : ℤ) : ℚ) =
        ((a0.2 + ((linV l' rev).2 - ((ellV d).2 + (ellV δ).2)) : ℤ) : ℚ) := by
      push_cast at ha2q f2 ⊢
      linarith
    exact_mod_cast h
  rw [hdd]
  unfold Acl
  rw [e]
  apply Prod.ext
  · rw [g1]
    simp [Prod.fst_add]
  · rw [g2]
    simp [Prod.snd_add]

end FLatticePaper.Tiles
