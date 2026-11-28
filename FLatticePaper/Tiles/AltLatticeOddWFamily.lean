import FLatticePaper.Tiles.AltLatticeOddWMain
import FLatticePaper.Tiles.MixedCompatEdges
import FLatticePaper.Tiles.StdPseudoAnchoredSets
import FLatticePaper.Tiles.PaperAltDomains
import FLatticePaper.Tiles.AltStairRespects
import FLatticePaper.Tiles.NearLadderAltRespects
import FLatticePaper.Tiles.GlueChain
import FLatticePaper.Tiles.BaseHpStair
import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.ConnectedAltL

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`, odd alternate child along `W`: the parents' data

The values of the parents on their bottom walks, in the overlap form that `AltLatticeOddWMain.odd_W_parents` reads: a normalised
odometer that respects the forward horizontal string of `w_h` at the origin is `β` on the bottom walk (`MixedCompatEdges.bottom`),
and a point `y` of a standard tile with `y + v₂` in it is on that walk (`OverlapSides`). For the even alternate tile, whose
forward horizontal string at the origin lies in the tile (item (3)), the same walk lies in the alternate tile. -/

namespace FLatticePaper.Tiles.AltLatticeOddWFamily

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.JointFamily (FirstTileNormal)

/-- The bottom walk of the odd standard tile of `u` in overlap form. -/
theorem bot_odd (u : Word) (o : PartialOdometer) (β : ℤ)
    (hR : RespectsTiles .horizontal false (hStringAt (hWordOf u false) 0) o.val) (hN : FirstTileNormal o 0 β) :
    ∀ y, y ∈ oddTile u → y + texV2 (StandardClause.fracOdd u) ∈ oddTile u → o.val y = β := by
  intro y h1 h2
  have hb := OverlapSides.odd_bottom_of_overlap u y h1 (by rwa [sub_neg_eq_add])
  have e : StandardBoundary.oddBottom u = gH (hWordOf u false) := RegisterLink.oddBottom_eq_gH u
  rw [e] at hb
  exact MixedCompatEdges.bottom o _ (hWordOf_head_last u false).1 (hWordOf_head_last u false).2 hR β hN y hb

/-- The bottom walk of the even standard tile of `u` in overlap form, for any normalised odometer respecting `w_h(q₀)`. -/
theorem bot_even (u : Word) (o : PartialOdometer) (β : ℤ)
    (hR : RespectsTiles .horizontal false (hStringAt (hWordOf u true) 0) o.val) (hN : FirstTileNormal o 0 β) :
    ∀ y, y ∈ evenTile u → y + texV2 (StandardClause.fracEven u) ∈ evenTile u → o.val y = β := by
  intro y h1 h2
  have hb := OverlapSides.even_bottom_of_overlap u y h1 (by rwa [sub_neg_eq_add])
  have e : StandardBoundary.evenBottom u = gH (hWordOf u true) := RegisterLink.evenBottom_eq_gH u
  rw [e] at hb
  exact MixedCompatEdges.bottom o _ (hWordOf_head_last u true).1 (hWordOf_head_last u true).2 hR β hN y hb

/-- At a non-base word the bottom walk of the even standard tile lies in the even alternate tile (item (3): the forward
horizontal string at the origin lies in `T̂`). -/
theorem alt_bottom_mem (u : Word) (hu : ¬ IsBase u) :
    ∀ y, y ∈ evenTile u → y + texV2 (StandardClause.fracEven u) ∈ evenTile u → y ∈ altEvenTile AltRotStep.B u := by
  intro y h1 h2
  have hb := OverlapSides.even_bottom_of_overlap u y h1 (by rwa [sub_neg_eq_add])
  have hs := HBottom.hB_even u y hb
  have hp := (StdPseudoAnchoredSets.placed_hStringAt_iff _ y).2 hs
  exact (AltItem3.alt_item3_even hu).1 y (by rw [hPartialTiles, placedSites_append, List.mem_append]; exact Or.inl hp)

theorem mem_placed_map (ts : List (ZTile × GInt)) (s x : GInt) :
    x + s ∈ placedSites (ts.map (fun p => (p.1, p.2 + s))) ↔ x ∈ placedSites ts := by
  unfold placedSites
  simp only [List.flatMap_map, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨a, ha, b, hb, by rw [← add_assoc] at he; exact add_right_cancel he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨a, ha, b, hb, by rw [← add_assoc, he]⟩

/-- The forward horizontal string at the origin of the staircase alternate `T̂_{1/(2k+3)}` (the even alternate of `3^k`) lies in it. -/
theorem stair_mem (k : ℕ) (y : Site) (hp : y ∈ placedSites (hStringAt (hWordOf (List.replicate k Digit.three) true) (0, 0))) :
    y ∈ (AltRotStep.B (List.replicate k Digit.three)).2 := by
  have hw : hWordOf (List.replicate k Digit.three) true = stairH k := BaseHpStair.hWordOf_three_true k
  rw [hw] at hp
  have hin := altStair_inside k y (by rw [hPartialTiles, placedSites_append, List.mem_append]; exact Or.inl hp)
  have hm := (PaperAltDomains.stairAltF_iff _ (by omega) y).2 hin
  have e : (AltRotStep.B (List.replicate k Digit.three)).2 = PaperAltBase.stairAltF (2 * (k : ℤ) + 3) := by
    show (PaperAltBase.paperAltBaseTiles (List.replicate k Digit.three)).2 = _
    unfold PaperAltBase.paperAltBaseTiles
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [if_neg (by simp; omega), if_pos (by simp), List.length_replicate]
  rw [e]; exact hm

/-- The forward horizontal string at the origin of the near-ladder alternate (the even alternate of `2^k`, `k ≥ 1`, in the frame
`x + (0, 1)`) lies in it. -/
theorem nla_mem (k : ℕ) (hk : 1 ≤ k) (y : Site)
    (hp : y ∈ placedSites (hStringAt (hWordOf (List.replicate k Digit.two) true) (0, 0))) :
    y ∈ (AltRotStep.B (List.replicate k Digit.two)).2 := by
  have hw : hWordOf (List.replicate k Digit.two) true = nlaWord k := BaseHpNearEven.hWordOf_two_true k
  rw [hw] at hp
  have e : (AltRotStep.B (List.replicate k Digit.two)).2 =
      shift (PaperAltBase.nearLadderAltF (2 * (k : ℤ) + 2)) ((0 : ℤ), (-1 : ℤ)) := by
    show (PaperAltBase.paperAltBaseTiles (List.replicate k Digit.two)).2 = _
    unfold PaperAltBase.paperAltBaseTiles
    have h1 : List.replicate k Digit.two ≠ [] := by simp; omega
    have h2 : List.replicate k Digit.two ≠ List.replicate (List.replicate k Digit.two).length Digit.three := by
      rw [List.length_replicate]
      intro h
      have := congrArg List.head? h
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [List.replicate_succ] at this
    rw [if_neg h1, if_neg h2, List.length_replicate]
  rw [e, PaperAltDomains.mem_shift_down, PaperAltDomains.nearLadderAltF_iff _ (by omega)]
  apply nla_inside k hk
  rw [hPartialTiles, placedSites_append, List.mem_append]
  left
  have e2 : ((0 : ℤ), (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)) := by simp
  rw [e2, ← GlueChain.hStringAt_shift]
  exact (mem_placed_map _ _ _).2 hp

/-- At every word the bottom walk of the even standard tile lies in the even alternate tile. -/
theorem alt_bottom_mem_all (u : Word) :
    ∀ y, y ∈ evenTile u → y + texV2 (StandardClause.fracEven u) ∈ evenTile u → y ∈ altEvenTile AltRotStep.B u := by
  by_cases hu : IsBase u
  · intro y h1 h2
    have hb := OverlapSides.even_bottom_of_overlap u y h1 (by rwa [sub_neg_eq_add])
    have hs := HBottom.hB_even u y hb
    have hp := (StdPseudoAnchoredSets.placed_hStringAt_iff _ y).2 hs
    rw [PaperAltDomains.altEvenTile_base u hu]
    rcases SiteBase.isBase_cases hu with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact stair_mem k y hp
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact stair_mem 0 y hp
      · exact nla_mem k hk y hp
  · exact alt_bottom_mem u hu

/-- The even register of `u x` (`x = 1, 3`) is `u`. -/
theorem regs2_snoc (u : Word) (xd : Digit) (hx : xd ≠ Digit.two) : (SurgicalWeak.regsAt (u ++ [xd])).2 = some u := by
  cases xd with
  | one => rw [ConnectedAltL.regs_snoc_one]
  | two => exact absurd rfl hx
  | three => exact ConnectedAltL.regs_snoc_three u

/-- **The decomposition of the odd alternate tile odometer at `u x`** (`x = 1, 3`) is `pieces7`: no L-correction, and the
alternate parent `ô(q₁)` of `u` at `c_H`. -/
theorem tileAltOdd_eq (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer)
    (lO : Word → Bool → Bool → PartialOdometer) (u : Word) (xd : Digit) (hx : xd ≠ Digit.two) :
    JointFamily.tileAltOddPieces S pO pE aO aE lO (u ++ [xd]) =
      AltGlueOdd.pieces7 (u ++ [xd]) (SurgicalWeak.regOdo S pO pE (SurgicalWeak.regsAt (u ++ [xd])).1 true) (pE u) (aE u) := by
  have hc : decide ((u ++ [xd]).getLast? = some Digit.two) = false := by simpa using hx
  have ht : (SurgicalAlt.altTypeOf (u ++ [xd])).bind (fun ty => SurgicalAlt.altQ1Coeff (JointFamily.W1Odd (u ++ [xd])) ty) =
      some (AltGlueOdd.cH (u ++ [xd])) := by
    rw [AltRotStep.altTypeOf_snoc]
    simp only [Option.bind_some, SurgicalAlt.altQ1Coeff, if_neg hx, AltGlueOdd.cH]
    split_ifs <;> rfl
  simp only [JointFamily.tileAltOddPieces, hc, regs2_snoc u xd hx, ht, SurgicalWeak.regOdo, Bool.false_eq_true, if_false,
    AltGlueOdd.pieces7, List.cons_append, List.nil_append]

/-- **The data of the alternate parent piece from the family**: at a word `u` of the family, with the printed alternate tiles,
the alternate anchor `c(T̂) = 0` of the even alternate child and slope zero, the even alternate tile odometer is defined on
`altEvenTile u`, contains `0`, has the normalised half-turn about `D̂_u`, and is `β_H` on the bottom walk of `T(q₀(u))`. -/
theorem alt_parent_data (D : JointFamily.JointData) (hAB : JointFamily.PaperAltBdry D) (f : Word → JointFamily.JSlice)
    (u : Word) (hJ : JointFamily.IsJointSlice D f u) (hP : JointFamily.JointProps f u)
    (hs : JointRot.SlopeZero (f u).aEven) (hAnc : D.anc.cHat u true = 0) :
    ∃ βH : ℤ, (f u).aEven.dom = altEvenTile AltRotStep.B u ∧ ((0 : ℤ), (0 : ℤ)) ∈ (f u).aEven.dom ∧
      (∀ z ∈ (f u).aEven.dom, JointFamily.altD u false - z ∈ (f u).aEven.dom ∧
        2 * ((f u).aEven.val (JointFamily.altD u false - z) - (f u).aEven.val z) =
          dotS (JointFamily.altE u) (JointFamily.altD u false) - 2 * dotS (JointFamily.altE u) z) ∧
      (∀ y, y ∈ evenTile u → y + texV2 (StandardClause.fracEven u) ∈ evenTile u →
        y ∈ (f u).aEven.dom ∧ (f u).aEven.val y = βH) := by
  obtain ⟨β0, hN⟩ := hs
  obtain ⟨-, -, hT, -⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, hRH, -, -, -, hdom⟩ := hT
  rw [(hAB u).2] at hdom
  obtain ⟨-, hTP, -, -, -⟩ := hP
  obtain ⟨-, -, -, -, -, ⟨α, β, hN', hH⟩⟩ := hTP
  obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN' hN
  refine ⟨β, hdom, (hN _ (by simp [tileShape])).1, fun z hz => ⟨(hH z hz).1, ?_⟩, fun y h1 h2 => ⟨?_, ?_⟩⟩
  · have e := (hH z hz).2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at e ⊢
    linarith
  · rw [hdom]; exact alt_bottom_mem_all u y h1 h2
  · have hR := hRH.1
    rw [SurgicalAlt.altFwdHAnchor, hAnc] at hR
    exact bot_even u _ β hR hN y h1 h2

end FLatticePaper.Tiles.AltLatticeOddWFamily
