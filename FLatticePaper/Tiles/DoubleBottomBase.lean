import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.TileListBridge
import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.WeakStepPaper
import FLatticePaper.Tiles.JointFamily

/-! # The base fact of the double case `pre = 2^j` (`j ≥ 1`)

The bottom string of the even base tile of `2^j` is `hStringAt (q^{2j+1} p) (0,0)`: a `one` tile at `(0,0)`, `oneD` tiles at
`(i,i)` for `1 ≤ i ≤ 2j`, and a `zero` tile at `(2j+2, 2j)`. The base odometer `E` of `2^j` (the near-one ladder) equals the
zero-one tile odometers on these tiles; the odd `2^{j-1}` piece `O'` shifted by `(1,1)` covers the string from `2` on, the
bridge `oneO` covers `(0,0)`, and the enlarged piece `enlOdo` shifted by `(1,1)` covers the tile at `(1,1)`. All three copies
agree with `E` with constant `0`. -/

namespace FLatticePaper.Tiles.DoubleBottomBase

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.BaseHpNearEven FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.WeakStepPaper
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.Standard (nladderN nladderF nstairN nstairF oneTile shift)

/-- `vP1` of the word `2^j`: the odd parent is `j/(j+1)`, so `v_{p_1,1} = (2j+2, 2j)`. -/
theorem vP1_two (j : ℕ) : vP1 (List.replicate j Digit.two) = ((2 : ℤ) * ((j : ℤ) + 1), (2 : ℤ) * (j : ℤ)) := by
  unfold vP1 texV1Odd
  rw [parents_two]

/-- Membership in the bottom string of `2^j`, as a union over the enlarged tiles of `q^{2j+1} p`. -/
theorem mem_bottom (k : ℕ) (x : GInt) :
    x ∈ placedSites (hStringAt (wEv k) (0, 0)) ↔
      ∃ i : ℕ, i < 2 * k + 2 ∧ ∃ u ∈ tileShape (tyEv k i), u + posEv k i = x := by
  rw [← zoForwardE_eq_hStringAt]
  unfold placedSites zoForwardE
  simp only [wEv_length, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ⟨i, hi, rfl⟩, hx⟩
    refine ⟨i, hi, ?_⟩
    rw [tile_type_wEv k i hi, posF_wEv k i hi] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨u, hu, rfl⟩
  · rintro ⟨i, hi, u, hu, rfl⟩
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    rw [tile_type_wEv k i hi, posF_wEv k i hi]
    exact ⟨u, hu, rfl⟩

theorem tyEv_zero (k : ℕ) : tyEv k 0 = ZTile.one := by
  unfold tyEv; rw [if_pos rfl]

theorem posEv_zero (k : ℕ) : posEv k 0 = (0, 0) := by
  unfold posEv; rw [if_pos (by omega)]; simp

theorem tyEv_mid (k i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ 2 * k) : tyEv k i = ZTile.oneD := by
  unfold tyEv; rw [if_neg (by omega), if_pos h2]

theorem posEv_mid (k i : ℕ) (h2 : i ≤ 2 * k) : posEv k i = ((i : ℤ), (i : ℤ)) := by
  unfold posEv; rw [if_pos h2]

theorem tyEv_last (k : ℕ) : tyEv k (2 * k + 1) = ZTile.zero := by
  unfold tyEv; rw [if_neg (by omega), if_neg (by omega)]

theorem posEv_last (k : ℕ) : posEv k (2 * k + 1) = (2 * (k : ℤ) + 2, 2 * (k : ℤ)) := by
  unfold posEv; rw [if_neg (by omega)]

/-- Bounds on the bottom string of `2^j` (`j ≥ 1`), read off its tiles: the sites lie in the strip
`0 ≤ x₁ ≤ 2j+3`, `0 ≤ x₂ ≤ 2j+2`, with `x₂ + 1 - x₁ ≤ 3`, `x₂ + 1 - x₁ ≥ -1` except at the corner `(2j+3, 2j)`, and
`x₂ ≤ 3` on the line `x₁ = 1`. -/
theorem bottom_facts (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (wEv j) (0, 0))) :
    0 ≤ x.1 ∧ x.1 ≤ 2 * (j : ℤ) + 3 ∧ 0 ≤ x.2 ∧ x.2 ≤ 2 * (j : ℤ) + 2 ∧
      x.2 + 1 - x.1 ≤ 3 ∧ (-1 ≤ x.2 + 1 - x.1 ∨ x = (2 * (j : ℤ) + 3, 2 * (j : ℤ))) ∧
      (x.1 ≠ 1 ∨ x.2 ≤ 3) := by
  obtain ⟨i, hi, u, hu, rfl⟩ := (mem_bottom j _).1 hx
  rcases (show i = 0 ∨ (1 ≤ i ∧ i ≤ 2 * j) ∨ i = 2 * j + 1 by omega) with rfl | ⟨h1, h2⟩ | rfl
  · rw [tyEv_zero, posEv_zero] at *
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega)
  · rw [tyEv_mid j i h1 h2, posEv_mid j i h2] at *
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega)
  · rw [tyEv_last j, posEv_last j] at *
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega)

theorem mem_nladderN_iff (d : ℤ) (x : GInt) : x ∈ nladderN d ↔ x + (0, 1) ∈ nladderF d := by
  unfold nladderN shift
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [show a + (0, -1) + (0, 1) = a by ext <;> simp]
    exact ha
  · intro h
    exact ⟨x + (0, 1), h, by ext <;> simp⟩

theorem mem_nstairN_iff (d : ℤ) (x : GInt) : x ∈ nstairN d ↔ x + (0, 1) ∈ nstairF d := by
  unfold nstairN shift
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [show a + (0, -1) + (0, 1) = a by ext <;> simp]
    exact ha
  · intro h
    exact ⟨x + (0, 1), h, by ext <;> simp⟩

/-- The bottom string lies in the domain of the base odometer `E` of `2^j`. -/
theorem bottom_Edom (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (wEv j) (0, 0))) :
    x ∈ nladderN (2 * (j : ℤ) + 2) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bottom_facts j hj (x1, x2) hx
  simp only [Prod.mk.injEq] at b6
  rw [mem_nladderN_iff]
  simp only [nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, add_zero]
  omega

/-- Every site of the bottom string is covered by one of the three copies: the odd `2^{j-1}` piece shifted by `(1,1)`, the
bridge at `0`, or the enlarged tile at `(1,1)`. -/
theorem bottom_cover (j : ℕ) (hj : 1 ≤ j) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (wEv j) (0, 0))) :
    x - ((1 : ℤ), (1 : ℤ)) ∈ nstairN (2 * (j : ℤ) + 1) ∨ x ∈ oneTile ∨
      x - ((1 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.oneD := by
  obtain ⟨i, hi, u, hu, rfl⟩ := (mem_bottom j _).1 hx
  rcases (show i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i ≤ 2 * j) ∨ i = 2 * j + 1 by omega) with rfl | rfl | ⟨h1, h2⟩ | rfl
  · rw [tyEv_zero] at hu
    rw [posEv_zero]
    right; left
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [oneTile]
  · rw [tyEv_mid j 1 le_rfl (by omega)] at hu
    rw [posEv_mid j 1 (by omega)]
    right; right
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [tileShape, Prod.ext_iff]
  · rw [tyEv_mid j i (by omega) h2] at hu
    rw [posEv_mid j i h2]
    left
    rw [mem_nstairN_iff]
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]; omega)
  · rw [tyEv_last j] at hu
    rw [posEv_last j]
    left
    rw [mem_nstairN_iff]
    obtain ⟨a, b⟩ := u
    simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (simp only [nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk_add_mk, Prod.mk_sub_mk]; omega)

/-- The odd piece of `2^{j-1}` (the copy `O'`): its domain and values, for `j ≥ 1`. -/
theorem pbc_odd (j : ℕ) (hj : 1 ≤ j) (O E : PartialOdometer)
    (h : SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.two) O E) :
    O.dom = nstairN (2 * (j : ℤ) + 1) ∧
      ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * (j : ℤ) + 1) (x + (0, 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨hd, hv, -, -⟩ := h.1 rfl
    refine ⟨by rw [hd]; norm_num, fun x hx => ?_⟩
    rw [hv x hx]
    norm_num
  · obtain ⟨hd, hv, -, -⟩ := h.2.2 m hm rfl
    have hd' : (2 * ((m + 1 : ℕ) : ℤ) + 1) = 2 * (m : ℤ) + 3 := by push_cast; ring
    refine ⟨by rw [hd, hd'], fun x hx => ?_⟩
    rw [hv x hx, hd']

/-- The `P1` identity: on the bottom string, the base odometer `E` of `2^j` equals the odd piece of `2^{j-1}` shifted by
`(1,1)`, with constant `0`, at the sites `x` with `0 ≤ x₁`, `x₂ ≤ 2j+2` and `x₂ + 1 - x₁ ≤ 3`. -/
theorem P1_id (j : ℕ) (hj : 1 ≤ j) (x1 x2 : ℤ) (b1 : 0 ≤ x1) (b4 : x2 ≤ 2 * (j : ℤ) + 2)
    (b5 : x2 + 1 - x1 ≤ 3) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (x1, x2 + 1) =
      paperNearStairValue (2 * (j : ℤ) + 1) (x1 - 1, x2) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  rw [pnlV]
  unfold paperNearStairValue
  rw [show x2 + 1 - x1 = x2 - (x1 - 1) by ring]
  rw [show 2 * (j : ℤ) + 2 - (x2 + 1) = 2 * (j : ℤ) + 1 - x2 by ring, min_comm 0 (2 * (j : ℤ) + 1 - x2)]
  rw [min_eq_left (show (0 : ℤ) ≤ 2 * (2 * (j : ℤ) + 2) - (x2 + 1) by omega)]
  rw [max_eq_right (show x2 - (x1 - 1) - (2 * (j : ℤ) + 2) ≤ 0 by omega)]
  generalize (x2 - (x1 - 1)) ^ 2 / 4 = s
  generalize min (2 * (j : ℤ) + 1 - x2) 0 = mm
  split_ifs <;> simp only [Prod.mk.injEq] at * <;> omega

/-- The base odometer of `2^j` on the bridge sites `oneTile = {(0,0), (0,1), (1,0), (1,1)}` is the one-odometer. -/
theorem P2_val (j : ℕ) (hj : 1 ≤ j) (a b : ℤ)
    (hab : (a, b) = (0, 0) ∨ (a, b) = (0, 1) ∨ (a, b) = (1, 0) ∨ (a, b) = (1, 1)) :
    paperNearLadderValue (2 * (j : ℤ) + 2) ((a, b) + (0, 1)) = oneOdometer (a, b) := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  rw [show ((a, b) + (0, 1) : GInt) = (a, b + 1) by ext <;> simp, pnlV]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    norm_num [oneOdometer, min_def, max_def] <;> split_ifs <;> omega

/-- The base odometer of `2^j` on the enlarged tile at `(1,1)` is the enlarged one-odometer. -/
theorem P3_val (j : ℕ) (hj : 1 ≤ j) (z : GInt) (hz : z ∈ tileShape ZTile.oneD) :
    paperNearLadderValue (2 * (j : ℤ) + 2) (z + (1, 1) + (0, 1)) = zTileOdo ZTile.oneD z := by
  have hj' : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  obtain ⟨a, b⟩ := z
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hz
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (simp only [Prod.mk_add_mk]; rw [pnlV]; norm_num [zTileOdo, oneOdometer, min_def, max_def]
     split_ifs <;> omega)

/-- **The base fact of the double case** (`LSidesEvenK.DoubleBottomBaseInput`): for `j ≥ 1`, on the bottom string `B` of the even
base tile of `2^j`, every site lies in one of the three copies (the odd piece of `2^{j-1}` shifted by `(1,1)`, the bridge
`oneO`, the enlarged piece at `(1,1)`); the corner `(1,1) + v_{p_1,1}` lies on `B`; and `E` equals each copy on `B`, with
constants `0`. -/
theorem double_bottom_base : ∀ (j : ℕ), 1 ≤ j → ∀ (O E O' E' : PartialOdometer),
    SurgicalWeak.PaperBaseCond (List.replicate j Digit.two) O E →
    SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.two) O' E' →
    (∀ x ∈ placedSites (hStringAt (hWordOf (List.replicate j Digit.two) true) 0),
      x - ((1 : ℤ), (1 : ℤ)) ∈ O'.dom ∨ x ∈ paperS.oneO.dom ∨ x - ((1 : ℤ), (1 : ℤ)) ∈ enlOdo.dom) ∧
    ((1 : ℤ), (1 : ℤ)) + vP1 (List.replicate j Digit.two) ∈
      placedSites (hStringAt (hWordOf (List.replicate j Digit.two) true) 0) ∧
    ∃ c1 c2 c3 : ℤ, ∀ x ∈ placedSites (hStringAt (hWordOf (List.replicate j Digit.two) true) 0),
      x ∈ E.dom ∧
      (x - ((1 : ℤ), (1 : ℤ)) ∈ O'.dom → E.val x = O'.val (x - ((1 : ℤ), (1 : ℤ))) + c1) ∧
      (x ∈ paperS.oneO.dom → E.val x = paperS.oneO.val x + c2) ∧
      (x - ((1 : ℤ), (1 : ℤ)) ∈ enlOdo.dom → E.val x = enlOdo.val (x - ((1 : ℤ), (1 : ℤ))) + c3) := by
  intro j hj O E O' E' hO hO'
  obtain ⟨-, -, hC⟩ := hO
  obtain ⟨-, -, hEdom, hEval⟩ := hC j hj rfl
  obtain ⟨hOdom, hOval⟩ := pbc_odd j hj O' E' hO'
  rw [hWordOf_two_true j]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ placedSites (hStringAt (wEv j) (0, 0)) := hx
    rcases bottom_cover j hj x hx' with h | h | h
    · left; rw [hOdom]; exact h
    · right; left; exact h
    · right; right; exact List.mem_toFinset.2 h
  · rw [vP1_two]
    have hx : ((1 : ℤ), (1 : ℤ)) + ((2 : ℤ) * ((j : ℤ) + 1), (2 : ℤ) * (j : ℤ)) ∈
        placedSites (hStringAt (wEv j) (0, 0)) := by
      rw [mem_bottom]
      refine ⟨2 * j + 1, by omega, (1, 1), ?_, ?_⟩
      · rw [tyEv_last j]; simp [tileShape]
      · rw [posEv_last j]; simp only [Prod.mk_add_mk]; congr 1
    exact hx
  · refine ⟨0, 0, 0, fun x hx => ?_⟩
    have hx' : x ∈ placedSites (hStringAt (wEv j) (0, 0)) := hx
    obtain ⟨x1, x2⟩ := x
    have hmem : ((x1, x2) : GInt) ∈ E.dom := by rw [hEdom]; exact bottom_Edom j hj _ hx'
    refine ⟨hmem, ?_, ?_, ?_⟩
    · intro hd
      rw [hEval _ hmem, hOval _ hd, add_zero]
      have e1 : ((x1, x2) + (0, 1) : GInt) = (x1, x2 + 1) := by ext <;> simp
      have e2 : ((x1, x2) - ((1 : ℤ), (1 : ℤ)) + (0, 1) : GInt) = (x1 - 1, x2) := by ext <;> simp
      rw [e1, e2]
      obtain ⟨b1, -, -, b4, b5, -, -⟩ := bottom_facts j hj (x1, x2) hx'
      exact P1_id j hj x1 x2 b1 b4 b5
    · intro hx1
      have hx1' : ((x1, x2) : GInt) ∈ oneTile := hx1
      simp only [oneTile, Finset.mem_insert, Finset.mem_singleton] at hx1'
      rw [hEval _ hmem, add_zero]
      exact P2_val j hj x1 x2 hx1'
    · intro hz
      have hz2 : ((x1, x2) - ((1 : ℤ), (1 : ℤ)) : GInt) ∈ (tileShape ZTile.oneD).toFinset := hz
      have hz' := List.mem_toFinset.1 hz2
      have h3 := P3_val j hj _ hz'
      rw [show ((x1, x2) - ((1 : ℤ), (1 : ℤ)) + (1, 1) + (0, 1) : GInt) = (x1, x2 + 1) by ext <;> simp] at h3
      rw [hEval _ hmem, add_zero, show ((x1, x2) + (0, 1) : GInt) = (x1, x2 + 1) by ext <;> simp]
      exact h3

end FLatticePaper.Tiles.DoubleBottomBase
