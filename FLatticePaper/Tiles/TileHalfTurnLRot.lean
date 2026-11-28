import FLatticePaper.Tiles.TileHalfTurnInput
import FLatticePaper.Tiles.SeamSymm

/-! # The half-turn of the L-corrected odometers from their rotations

`lemma:l_correc_properties` (1): `R²(T^{L,+}) = T^{L,-}`. The rotation identities of the L-corrected odometers
(`JointFamily.LRotProps`, part of `JointProps` of every shorter word) at `u` and at `swapW u` compose to the half-turn
`y ↦ C - y` about the centre `C = v_{q₀,1} + v_{q₀,2} + 1 - i` of the child, sending `o^{L,b}` to `o^{L,!b}`: the two
quarter-turn corrections add up to `h_0(i y + c) + h_0(y) = -a_{q₀,2}ᵀy + const` (`h0_pair`, the quadratic parts cancel and the
parity terms add up to `1`). This holds at every prefix, so it gives `TileHalfTurnInput.SpecialLHalfTurn`
(`specialLHalfTurn_of_rot`) and `HalfTurnInput` with no named input (`halfTurnInput_paper_full`). -/

namespace FLatticePaper.Tiles.TileHalfTurnLRot

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.TileHalfTurnCorr (CrossHT)
open FLatticePaper.Tiles.TileStepAssembly (HalfTurnInput)
open FLatticePaper.Tiles.Standard (swapW)

/-- Two rotations compose to a half-turn. -/
theorem compose_rot (L M L' : PartialOdometer) (v1 v1' : Site) (h1 : LRotation L M v1) (h2 : LRotation M L' v1') :
    ∃ c : ℤ, ∀ y ∈ L'.dom, (mulI v1' + v1 + ((1 : ℤ), (-1 : ℤ))) - y ∈ L.dom ∧
      L'.val y = L.val ((mulI v1' + v1 + ((1 : ℤ), (-1 : ℤ))) - y) - h0 (mulI y + (v1' - ((0 : ℤ), (1 : ℤ)))) -
        h0 y + c := by
  obtain ⟨c1, h1⟩ := h1
  obtain ⟨c2, h2⟩ := h2
  refine ⟨c1 + c2, fun y hy => ?_⟩
  obtain ⟨hm, hv⟩ := h2 y hy
  obtain ⟨hl, hv'⟩ := h1 _ hm
  have e : mulI (mulI y + v1' - ((0 : ℤ), (1 : ℤ))) + v1 - ((0 : ℤ), (1 : ℤ)) =
      (mulI v1' + v1 + ((1 : ℤ), (-1 : ℤ))) - y := by
    simp only [mulI]; ext <;> simp <;> ring
  have e' : mulI y + v1' - ((0 : ℤ), (1 : ℤ)) = mulI y + (v1' - ((0 : ℤ), (1 : ℤ))) := add_sub_assoc _ _ _
  rw [e] at hl hv'
  exact ⟨hl, by rw [hv, hv', e']; ring⟩

/-- The two quarter-turn corrections of a half-turn add up to an affine function when `c₁ + c₂` is odd. -/
theorem h0_pair (y c : Site) (hc : (c.1 + c.2) % 2 = 1) :
    4 * (h0 (mulI y + c) + h0 y) = y.1 * (2 * c.2 - 2 * c.1 + 2) + y.2 * (2 * c.1 + 2 * c.2 + 2) +
      (-c.1 ^ 2 - 2 * c.1 * c.2 + c.2 ^ 2 + 2 * c.2 + 1) := by
  have e1 := four_mul_centeredQuarterTurnCorrection (mulI y + c)
  have e2 := four_mul_centeredQuarterTurnCorrection y
  simp only [mulI, Prod.fst_add, Prod.snd_add] at e1
  have hp : (-y.2 + c.1 + (y.1 + c.2)) % 2 = 1 - (y.1 + y.2) % 2 := by omega
  rw [hp] at e1
  simp only [h0, mulI]
  linear_combination (-1 : ℤ) * e1 - e2

/-- The affine part: `h_0(i y + c) + h_0(y) = h_0(c) + h_0(0) - n y₁ + d y₂` for `c = (d + n, d - n - 1)`. -/
theorem h0_pair_nd (y : Site) (n d : ℤ) :
    h0 (mulI y + (d + n, d - n - 1)) + h0 y = h0 (mulI 0 + (d + n, d - n - 1)) + h0 0 - n * y.1 + d * y.2 := by
  have hc : ((d + n, d - n - 1) : Site).1 + ((d + n, d - n - 1) : Site).2 = 2 * d - 1 := by simp; ring
  have h1 := h0_pair y (d + n, d - n - 1) (by rw [hc]; omega)
  have h2 := h0_pair 0 (d + n, d - n - 1) (by rw [hc]; omega)
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, zero_add] at h2
  linarith

/-- The cross half-turn from the composed rotation, with the centre and slope of a child `(n, d)`. -/
theorem cross_of_rot (Ls Lt M : PartialOdometer) (v1 v1' : Site) (n d : ℤ)
    (h1 : LRotation Lt M v1) (h2 : LRotation M Ls v1') (hv1' : v1' = (d + n, d - n))
    (hC : mulI v1' + v1 + ((1 : ℤ), (-1 : ℤ)) = v1 + (n - d, n + d) + ((1 : ℤ), (-1 : ℤ))) :
    CrossHT Ls Lt (v1 + (n - d, n + d) + ((1 : ℤ), (-1 : ℤ))) (n, -d) := by
  obtain ⟨c, hc⟩ := compose_rot Lt M Ls v1 v1' h1 h2
  rw [hC] at hc
  refine ⟨2 * (h0 (mulI 0 + (d + n, d - n - 1)) + h0 0) - 2 * c, fun z hz => ?_⟩
  obtain ⟨hd, hv⟩ := hc z hz
  refine ⟨hd, ?_⟩
  have hc' : v1' - ((0 : ℤ), (1 : ℤ)) = (d + n, d - n - 1) := by rw [hv1']; ext <;> simp
  rw [hc'] at hv
  have hh := h0_pair_nd z n d
  rw [hv]
  simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linarith

/-! ### The two L-corrections -/

theorem rot_even (q : Fraction) (h : q.Even) : texV1Odd q.rotate = (q.den + q.num, q.den - q.num) := by
  rw [Fraction.rotate_of_even h]
  have h' : (q.num + q.den) % 2 = 0 := h
  simp only [texV1Odd, Prod.mk.injEq]
  omega

theorem rot_odd (p : Fraction) (h : p.Odd) : texV1Even p.rotate = (p.den + p.num, p.den - p.num) := by
  rw [Fraction.rotate_of_odd h]
  rfl

/-- **The half-turn of the even L-corrected odometers of `u`**, from the rotations at `u` and `swapW u`. -/
theorem lHalfTurn_even_rot (D : JointData) (f : Word → JSlice) (u : Word) (hG : GoodBelow D f (u.length + 1))
    (hdef : EvenLDefined u) (b elong : Bool) :
    CrossHT ((f u).lEven b elong) ((f u).lEven (!b) elong) (TileHalfTurnStd.cEven ((parentsAt u).current .even))
      (TileHalfTurnStd.aF ((parentsAt u).current .even)) := by
  obtain ⟨-, -, -, hLR1, -⟩ := (hG u (by omega)).2
  obtain ⟨-, -, -, hLR2, -⟩ := (hG (swapW u) (by rw [JointRot.length_swapW]; omega)).2
  rw [JointRot.swapW_swapW'] at hLR2
  have hW := JointRot.W1Odd_swapW u
  have h1 := hLR1.1 hdef (!b) elong
  have h2 := hLR2.2 (JointRot.oddLDefined_swapW hdef) ((!b) != W1Odd u) elong
  have hb : (((!b) != W1Odd u) == W1Odd (swapW u)) = b := by rw [hW]; cases b <;> cases W1Odd u <;> rfl
  rw [hb] at h2
  have hq := (parentsAt_valid u).current_even_parity
  have hrot : (parentsAt (swapW u)).current .odd = ((parentsAt u).current .even).rotate := (SeamSymm.current_swap u).2
  have hv1' : texV1Odd ((parentsAt (swapW u)).current .odd) =
      (((parentsAt u).current .even).den + ((parentsAt u).current .even).num,
        ((parentsAt u).current .even).den - ((parentsAt u).current .even).num) := by
    rw [hrot]; exact rot_even _ hq
  have key := cross_of_rot _ _ _ _ _ ((parentsAt u).current .even).num ((parentsAt u).current .even).den h1 h2 hv1'
    (by rw [hv1']; ext <;> simp [mulI] <;> ring)
  have hc : texV1Even ((parentsAt u).current .even) + (((parentsAt u).current .even).num -
      ((parentsAt u).current .even).den, ((parentsAt u).current .even).num + ((parentsAt u).current .even).den) +
      ((1 : ℤ), (-1 : ℤ)) = TileHalfTurnStd.cEven ((parentsAt u).current .even) := by
    simp [TileHalfTurnStd.cEven, texV2]
  rw [hc] at key
  exact key

/-- **The half-turn of the odd L-corrected odometers of `u`**, from the rotations at `u` and `swapW u`. -/
theorem lHalfTurn_odd_rot (D : JointData) (f : Word → JSlice) (u : Word) (hG : GoodBelow D f (u.length + 1))
    (hdef : OddLDefined u) (b elong : Bool) :
    CrossHT ((f u).lOdd b elong) ((f u).lOdd (!b) elong) (TileHalfTurnStd.cOdd ((parentsAt u).current .odd))
      (TileHalfTurnStd.aF ((parentsAt u).current .odd)) := by
  obtain ⟨-, -, -, hLR1, -⟩ := (hG u (by omega)).2
  obtain ⟨-, -, -, hLR2, -⟩ := (hG (swapW u) (by rw [JointRot.length_swapW]; omega)).2
  rw [JointRot.swapW_swapW'] at hLR2
  have hW := JointRot.W1Odd_swapW u
  have h1 := hLR1.2 hdef (!b) elong
  have h2 := hLR2.1 (JointRot.evenLDefined_swapW hdef) ((!b) == W1Odd u) elong
  have hb : (((!b) == W1Odd u) != W1Odd (swapW u)) = b := by rw [hW]; cases b <;> cases W1Odd u <;> rfl
  rw [hb] at h2
  have hp := (parentsAt_valid u).current_odd_parity
  have hrot : (parentsAt (swapW u)).current .even = ((parentsAt u).current .odd).rotate := (SeamSymm.current_swap u).1
  have hv1' : texV1Even ((parentsAt (swapW u)).current .even) =
      (((parentsAt u).current .odd).den + ((parentsAt u).current .odd).num,
        ((parentsAt u).current .odd).den - ((parentsAt u).current .odd).num) := by
    rw [hrot]; exact rot_odd _ hp
  have key := cross_of_rot _ _ _ _ _ ((parentsAt u).current .odd).num ((parentsAt u).current .odd).den h1 h2 hv1'
    (by rw [hv1']; ext <;> simp [mulI] <;> ring)
  have hc : texV1Odd ((parentsAt u).current .odd) + (((parentsAt u).current .odd).num -
      ((parentsAt u).current .odd).den, ((parentsAt u).current .odd).num + ((parentsAt u).current .odd).den) +
      ((1 : ℤ), (-1 : ℤ)) = TileHalfTurnStd.cOdd ((parentsAt u).current .odd) := by
    simp [TileHalfTurnStd.cOdd, texV2]
  rw [hc] at key
  exact key

/-- **`SpecialLHalfTurn` holds**: the half-turn of the L-corrected odometers at every prefix follows from their rotations. -/
theorem specialLHalfTurn_of_rot (D : JointData) : TileHalfTurnInput.SpecialLHalfTurn D :=
  fun f u hG => ⟨fun hdef _ b elong => lHalfTurn_even_rot D f u hG hdef b elong,
    fun hdef _ b elong => lHalfTurn_odd_rot D f u hG hdef b elong⟩

/-- **`HalfTurnInput` for the paper data**, with no named input. -/
theorem halfTurnInput_paper_full (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (hlS : D.lSides = paperLSides) : HalfTurnInput D :=
  TileHalfTurnInput.halfTurnInput_paper D hS hA hlS (specialLHalfTurn_of_rot D)

end FLatticePaper.Tiles.TileHalfTurnLRot
