import FLatticePaper.Tiles.SurgicalAffineChain
import FLatticePaper.Tiles.IncrementCounts
import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.SurgicalWeakOdometers

/-! # Identity 3 of (b) in affine factors (`lemma:weak_standard_odometer_properties` (b), third identity)

The third identity `a_C - a_B = a_{n/d,2} - a_{1/1,2} = (n - 1, 1 - d)` is proved by the chain `C → D → (the vertical
reversed string) → A → B`: `a_C - a_D = (-1, 0)` (`corner_rev`), `D` is the last tile of the reversed vertical string
`vRevStringAt wv.reverse 0`, the vertical steps change the affine factor by `(e(letter), -1)` (`chain_vert`, from the vertical
table), the first tile of that string is `A`, and `a_A = a_B` (`corner_fwd`). The sum of the `e` along the string is the number
of `q`'s of `w_v`, and its length is `d` (`vertWord_counts`). -/

namespace FLatticePaper.Tiles

/-- The `e`-value of a placed zero-one tile type: `1` on the one tiles (letter `q`), `0` on the zero tile. -/
def epsZ : ZTile → ℚ
  | .zero => 0
  | .one => 1
  | .oneD => 1

theorem epsZ_letterZTile (x : Letter) : epsZ (letterZTile x) = if x = Letter.q then 1 else 0 := by
  cases x <;> simp [epsZ, letterZTile]

/-- The vertical table of the surgical text does not depend on the reversal flag, and changes the base slope by `(e, -1)`. -/
theorem table_vert (z1 z2 : ZTile) :
    surgicalSlopeDiff .vertical true (zTileLetter z1) (zTileLetter z2) =
      zTileBaseSlope z2 - zTileBaseSlope z1 + (epsZ z1, -1) := by
  cases z1 <;> cases z2 <;>
    simp [surgicalSlopeDiff, zTileLetter, epsZ, zTileBaseSlope_zero, zTileBaseSlope_one, zTileBaseSlope_oneD] <;>
    norm_num

/-- Along a reversed vertical string the affine factor of the `k`-th tile is that of the first plus `(Σ e, -k)`. -/
theorem chain_vert (F : PTFamily) (S : GInt → ℤ)
    (hS : ∀ k, k < F.n → ∀ x ∈ F.dom k, S x = F.odo k x)
    (hR : ∀ k, k + 1 < F.n → slopeOf (F.odo (k + 1)) (F.dom (k + 1)) - slopeOf (F.odo k) (F.dom k) =
      surgicalSlopeDiff .vertical true (zTileLetter (F.tile k).1) (zTileLetter (F.tile (k + 1)).1)) :
    ∀ k, k < F.n → tileAffine S (F.tile k) =
      tileAffine S (F.tile 0) + ((∑ j ∈ Finset.range k, epsZ (F.tile j).1), -(k : ℚ)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hdiff := hR k hk
    rw [table_vert] at hdiff
    have hstep : tileAffine S (F.tile (k + 1)) = tileAffine S (F.tile k) + (epsZ (F.tile k).1, -1) := by
      unfold tileAffine
      rw [tileSlope_eq F S (k + 1) (hS (k + 1) hk), tileSlope_eq F S k (hS k (by omega))]
      apply Prod.ext
      · have h1 := congrArg Prod.fst hdiff
        simp only [Prod.fst_sub, Prod.fst_add] at h1 ⊢
        linarith
      · have h2 := congrArg Prod.snd hdiff
        simp only [Prod.snd_sub, Prod.snd_add] at h2 ⊢
        linarith
    rw [hstep, ihk, Finset.sum_range_succ]
    apply Prod.ext
    · simp only [Prod.fst_add]
      ring
    · simp only [Prod.snd_add]
      push_cast
      ring

theorem vRevStringAt_length (u : BinaryWord) (c : GInt) : (vRevStringAt u c).length = u.length := by
  unfold vRevStringAt
  simp only [List.length_zip, List.length_map, List.length_scanl, List.length_tail]
  omega

theorem vRevStringAt_map_fst (u : BinaryWord) (c : GInt) :
    (vRevStringAt u c).map Prod.fst = u.map letterZTile := by
  unfold vRevStringAt
  apply List.map_fst_zip
  simp only [List.length_map, List.length_scanl, List.length_zip, List.length_tail]
  omega

theorem vRevStringAt_getD_fst (u : BinaryWord) (c : GInt) (i : ℕ) (hi : i < u.length) :
    ((vRevStringAt u c).getD i (ZTile.zero, (0 : GInt))).1 = letterZTile (u.getD i .p) := by
  have e1 : ((vRevStringAt u c).map Prod.fst).getD i ZTile.zero =
      ((vRevStringAt u c).getD i (ZTile.zero, (0 : GInt))).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    generalize (vRevStringAt u c)[i]? = o
    cases o <;> simp
  have e2 : (u.map letterZTile).getD i ZTile.zero = letterZTile (u.getD i .p) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rw [← e1, vRevStringAt_map_fst, e2]

theorem vRevStringAt_getD_snd_zero (u : BinaryWord) (c : GInt) (hu : u ≠ []) :
    ((vRevStringAt u c).getD 0 (ZTile.zero, (0 : GInt))).2 = c := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a l => simp [vRevStringAt]

theorem hRevStringAt_getD_snd_zero (u : BinaryWord) (c : GInt) (hu : u ≠ []) :
    ((hRevStringAt u c).getD 0 (ZTile.zero, (0 : GInt))).2 = c := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a l => simp [hRevStringAt]

theorem lastPosOf_eq_getD (L : List (ZTile × GInt)) :
    lastPosOf L = (L.getD (L.length - 1) (ZTile.zero, (0 : GInt))).2 := by
  unfold lastPosOf
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  generalize L[L.length - 1]? = o
  cases o <;> simp

theorem length_eq_counts (L : BinaryWord) : L.length = L.count .p + L.count .q := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp only [List.length_cons, List.count_cons] <;> simp_all <;> omega

theorem sum_range_eps (u : BinaryWord) :
    ∑ j ∈ Finset.range u.length, (if u.getD j .p = .q then (1 : ℚ) else 0) = (u.count .q : ℚ) := by
  induction u with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    cases a <;> simp

theorem hStringAt_head_q (wh : BinaryWord) (c : GInt) (h : wh.head? = some .q) :
    (hStringAt wh c).headD (ZTile.zero, 0) = (ZTile.one, c) := by
  cases wh with
  | nil => simp at h
  | cons a l =>
    simp at h
    subst h
    cases l with
    | nil => simp [hStringAt, tileSeq, tileSeqAux, List.scanl_nil]
    | cons b l' => simp [hStringAt, tileSeq, tileSeqAux, List.scanl_cons]

/-- The third identity of (b), in the counts of the vertical word (with `d = k + 1`). -/
theorem corner_third (wh wv : BinaryWord) (k : ℕ) (S : GInt → ℤ)
    (hhead : wh.head? = some .q) (hlast : wh.getLast? = some .p)
    (hvh : wv.head? = some .p) (hvl : wv.getLast? = some .q) (hlen : wv.length = k + 1)
    (hA : RespectsTiles .horizontal false (hStringAt wh 0) S)
    (hC : RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S)
    (hV : RespectsTiles .vertical true (vRevStringAt wv.reverse 0) S) :
    tileAffine S (cornerTiles wh wv 0).2.2.1 - tileAffine S (cornerTiles wh wv 0).2.1 =
      (((wv.count .q : ℕ) : ℚ) - 1, -(k : ℚ)) := by
  obtain ⟨F, hF, hS, hRes⟩ := hV
  have hvne : wv ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hwne : wh ≠ [] := by
    intro h
    rw [h] at hhead
    simp at hhead
  have hrne : wh.reverse ≠ [] := by simp [hwne]
  have hvrne : wv.reverse ≠ [] := by simp [hvne]
  have hFn : F.n = k + 1 := by
    unfold PTFamily.n
    rw [hF, vRevStringAt_length, List.length_reverse, hlen]
  have hFt : ∀ j, j < k + 1 → (F.tile j).1 = letterZTile (wv.reverse.getD j .p) := by
    intro j hj
    have hj' : j < wv.reverse.length := by
      rw [List.length_reverse, hlen]
      omega
    show ((F.ts).getD j (ZTile.zero, 0)).1 = _
    rw [hF]
    exact vRevStringAt_getD_fst wv.reverse 0 j hj'
  have hrev_last : wv.reverse.getD k .p = .p := by
    have hk' : k = wv.reverse.length - 1 := by
      rw [List.length_reverse, hlen]
      omega
    rw [hk', List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, List.getLast?_reverse, hvh]
    rfl
  have hrev_first : wv.reverse.getD 0 .p = .q := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hvl]
    rfl
  have hwhr : wh.reverse.getD 0 .p = .p := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, List.head?_reverse, hlast]
    rfl
  have hsum : ∑ j ∈ Finset.range (k + 1), epsZ (F.tile j).1 = ((wv.count .q : ℕ) : ℚ) := by
    have hcongr : ∀ j ∈ Finset.range (k + 1), epsZ (F.tile j).1 =
        if wv.reverse.getD j .p = .q then (1 : ℚ) else 0 := by
      intro j hj
      rw [hFt j (by simpa using hj), epsZ_letterZTile]
    rw [Finset.sum_congr rfl hcongr]
    have h := sum_range_eps wv.reverse
    rw [List.length_reverse, hlen] at h
    rw [h, List.count_reverse]
  have hkey := chain_vert F S hS (fun j hj => (hRes j hj).1) k (by omega)
  have hlast0 : epsZ (F.tile k).1 = 0 := by
    rw [hFt k (by omega), hrev_last]
    rfl
  have hsumk : ∑ j ∈ Finset.range k, epsZ (F.tile j).1 = ((wv.count .q : ℕ) : ℚ) := by
    rw [Finset.sum_range_succ, hlast0, add_zero] at hsum
    exact hsum
  rw [hsumk] at hkey
  -- the tile at the last index of the reversed vertical string is the first tile of the reversed horizontal string
  have hFk : F.tile k = (letterZTile (wv.reverse.getD k .p), lastPosOf (vRevStringAt wv.reverse 0)) := by
    apply Prod.ext
    · rw [hFt k (by omega), hrev_last]
    · show ((F.ts).getD k (ZTile.zero, 0)).2 = _
      have hidx : k = (vRevStringAt wv.reverse 0).length - 1 := by
        rw [vRevStringAt_length, List.length_reverse, hlen]
        omega
      rw [hF, lastPosOf_eq_getD, ← hidx]
  have hDeq : (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).headD (ZTile.zero, 0) =
      F.tile k := by
    rw [headD_eq_getD_zero', hFk]
    apply Prod.ext
    · rw [hRevStringAt_getD_fst wh.reverse _ 0 (by
        rw [List.length_reverse]
        exact List.length_pos_of_ne_nil hwne), hwhr, hrev_last]
    · rw [hRevStringAt_getD_snd_zero wh.reverse _ hrne]
  -- the tile at the first index of the reversed vertical string is the first tile of the forward horizontal string
  have hF0 : F.tile 0 = (ZTile.one, 0) := by
    apply Prod.ext
    · show ((F.ts).getD 0 (ZTile.zero, 0)).1 = _
      rw [hF, vRevStringAt_getD_fst wv.reverse 0 0 (by
        rw [List.length_reverse]
        exact List.length_pos_of_ne_nil hvne), hrev_first]
      rfl
    · show ((F.ts).getD 0 (ZTile.zero, 0)).2 = _
      rw [hF]
      exact vRevStringAt_getD_snd_zero wv.reverse 0 hvrne
  have hA1 : (hStringAt wh 0).headD (ZTile.zero, 0) = (ZTile.one, 0) := hStringAt_head_q wh 0 hhead
  have hB : tileAffine S ((hStringAt wh 0).getLastD (ZTile.zero, 0)) =
      tileAffine S ((hStringAt wh 0).headD (ZTile.zero, 0)) := corner_fwd wh S hA
  have hC' := corner_rev wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) S
    (by rw [List.head?_reverse]; exact hlast) (by rw [List.getLast?_reverse]; exact hhead) hC
  have hZ : tileAffine S ((hStringAt wh 0).getLastD (ZTile.zero, 0)) = tileAffine S (F.tile 0) := by
    rw [hB, hA1, hF0]
  have hY : tileAffine S ((hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))).headD
      (ZTile.zero, 0)) = tileAffine S (F.tile 0) + (((wv.count .q : ℕ) : ℚ), -(k : ℚ)) := by
    rw [hDeq, hkey]
  simp only [cornerTiles]
  rw [hZ]
  have hX1 := congrArg Prod.fst hC'
  have hX2 := congrArg Prod.snd hC'
  have hY1 := congrArg Prod.fst hY
  have hY2 := congrArg Prod.snd hY
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hX1 hX2 hY1 hY2
  apply Prod.ext
  · simp only [Prod.fst_sub]
    linarith
  · simp only [Prod.snd_sub]
    linarith

/-- The third identity of (b) for every odd child of a weak standard family, in the child fraction `n/d` of `oddTile w`
(`(parentsAt w).current .odd`): the horizontal and vertical words of the odd child are `hWordOf w false` and `vWordOf w false`
(`vWordOf w false = vertWord w`), with `#q(w_v) = n` and `|w_v| = d` (`vertWord_counts`). -/
theorem corner_3_family (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).2.2.1 -
      tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).2.1 =
    ((((FLatticePaper.Farey.parentsAt w).current .odd).num : ℚ) - 1,
      (1 - (((FLatticePaper.Farey.parentsAt w).current .odd).den : ℚ))) := by
  obtain ⟨_, hA, hC, hV, _⟩ := (h w).2.2.2.2.1
  have hwv : FLatticePaper.Tiles.SiteStrings.vWordOf w false = vertWord w := rfl
  obtain ⟨hvh, hvl⟩ := StringCorners.vertWord_head_last w
  have hcnt := vertWord_counts w
  have hne : vertWord w ≠ [] := by
    intro hn
    rw [hn] at hvh
    simp at hvh
  obtain ⟨k, hk⟩ : ∃ k, (vertWord w).length = k + 1 :=
    ⟨(vertWord w).length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
  have hlenZ : ((vertWord w).length : ℤ) = ((FLatticePaper.Farey.parentsAt w).current .odd).den := by
    have hl := length_eq_counts (vertWord w)
    have h1 : ((vertWord w).length : ℤ) = ((vertWord w).count .p : ℤ) + ((vertWord w).count .q : ℤ) := by
      exact_mod_cast hl
    rw [h1, hcnt.1, hcnt.2]
    ring
  rw [hwv]
  have key := corner_third (FLatticePaper.Tiles.SiteStrings.hWordOf w false) (vertWord w) k
    (oddO w).val (hWordOf_head_last w false).1 (hWordOf_head_last w false).2 hvh hvl hk hA hC hV
  rw [key]
  have hq : ((vertWord w).count .q : ℚ) = ((((FLatticePaper.Farey.parentsAt w).current .odd).num : ℤ) : ℚ) := by
    exact_mod_cast hcnt.2
  have hkZ : ((k : ℤ) + 1) = ((FLatticePaper.Farey.parentsAt w).current .odd).den := by
    rw [← hlenZ, hk]
    push_cast
    ring
  have hkd : ((k : ℕ) : ℚ) = ((((FLatticePaper.Farey.parentsAt w).current .odd).den : ℤ) : ℚ) - 1 := by
    have : ((k : ℤ) : ℚ) + 1 = ((((FLatticePaper.Farey.parentsAt w).current .odd).den : ℤ) : ℚ) := by
      exact_mod_cast hkZ
    push_cast at this ⊢
    linarith
  rw [hq, hkd]
  apply Prod.ext
  · simp
  · simp

/-- The first two identities of (b) for every even child of a weak standard family. -/
theorem corner_12_family_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).2.1 -
      tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).1 = 0 ∧
    tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).2.2.1 -
      tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).2.2.2 = ((-1 : ℚ), (0 : ℚ)) := by
  obtain ⟨_, hA, hC, _, _⟩ := (h w).2.2.2.2.2
  exact corner_affine_12 _ _ _ (hWordOf_head_last w true).1 (hWordOf_head_last w true).2 hA hC

/-- The third identity of (b) for every even child of a weak standard family, in the fraction `n/d` of `evenTile w`
(`(parentsAt w).current .even`): `#q(w_v) = n` and `|w_v| = d` (`vWord_even_counts`). -/
theorem corner_3_family_even (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word) :
    tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).2.2.1 -
      tileAffine (evenO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) 0).2.1 =
    ((((FLatticePaper.Farey.parentsAt w).current .even).num : ℚ) - 1,
      (1 - (((FLatticePaper.Farey.parentsAt w).current .even).den : ℚ))) := by
  obtain ⟨_, hA, hC, hV, _⟩ := (h w).2.2.2.2.2
  obtain ⟨hvh, hvl⟩ := StringCorners.vWord_even_head_last w
  have hcnt : ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).count .p : ℤ) =
        ((FLatticePaper.Farey.parentsAt w).current .even).den -
          ((FLatticePaper.Farey.parentsAt w).current .even).num ∧
      ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).count .q : ℤ) =
        ((FLatticePaper.Farey.parentsAt w).current .even).num :=
    StringCorners.vWord_even_counts w
  have hne : FLatticePaper.Tiles.SiteStrings.vWordOf w true ≠ [] := by
    intro hn
    rw [hn] at hvh
    simp at hvh
  obtain ⟨k, hk⟩ : ∃ k, (FLatticePaper.Tiles.SiteStrings.vWordOf w true).length = k + 1 :=
    ⟨(FLatticePaper.Tiles.SiteStrings.vWordOf w true).length - 1, by
      have := List.length_pos_of_ne_nil hne
      omega⟩
  have hlenZ : ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).length : ℤ) =
      ((FLatticePaper.Farey.parentsAt w).current .even).den := by
    have hl := length_eq_counts (FLatticePaper.Tiles.SiteStrings.vWordOf w true)
    have h1 : ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).length : ℤ) =
        ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).count .p : ℤ) +
          ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).count .q : ℤ) := by
      exact_mod_cast hl
    rw [h1, hcnt.1, hcnt.2]
    ring
  have key := corner_third (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
    (FLatticePaper.Tiles.SiteStrings.vWordOf w true) k (evenO w).val
    (hWordOf_head_last w true).1 (hWordOf_head_last w true).2 hvh hvl hk hA hC hV
  rw [key]
  have hq : ((FLatticePaper.Tiles.SiteStrings.vWordOf w true).count .q : ℚ) =
      ((((FLatticePaper.Farey.parentsAt w).current .even).num : ℤ) : ℚ) := by
    exact_mod_cast hcnt.2
  have hkZ : ((k : ℤ) + 1) = ((FLatticePaper.Farey.parentsAt w).current .even).den := by
    rw [← hlenZ, hk]
    push_cast
    ring
  have hkd : ((k : ℕ) : ℚ) = ((((FLatticePaper.Farey.parentsAt w).current .even).den : ℤ) : ℚ) - 1 := by
    have : ((k : ℤ) : ℚ) + 1 = ((((FLatticePaper.Farey.parentsAt w).current .even).den : ℤ) : ℚ) := by
      exact_mod_cast hkZ
    push_cast at this ⊢
    linarith
  rw [hq, hkd]
  apply Prod.ext
  · simp
  · simp

end FLatticePaper.Tiles
