import FLatticePaper.Tiles.JointInduction
import FLatticePaper.Tiles.ChildGlue
import FLatticePaper.Tiles.ClosedPathStandard

/-! # The weak step of the joint induction for the paper's data

The registers of the nodes (`regsAt`) are the registers of the standard tiles (`stateAt`): the register word `u` of `w` carries
the tile `oddTile u` (resp. `evenTile u`), and the empty register the initial tile `T_{0/1}` (resp. `T_{1/1}`)
(`regsAt_tiles`). This is the bridge between the nodes of `SurgicalWeak` and the copies of `ChildGlue`. -/

namespace FLatticePaper.Tiles.WeakStepPaper

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.Standard (stateAt oddTile evenTile zeroTile oneTile stepState)

theorem regRun_append (pre rest : Word) (d : Digit) (r : Option Word × Option Word) :
    regRun pre (rest ++ [d]) r = regStep (pre ++ rest) (regRun pre rest r) d := by
  induction rest generalizing pre r with
  | nil => simp [regRun]
  | cons a rest ih =>
    show regRun (pre ++ [a]) (rest ++ [d]) (regStep pre r a) = _
    rw [ih]
    simp [regRun, List.append_assoc]

theorem regsAt_snoc (u : Word) (d : Digit) : regsAt (u ++ [d]) = regStep u (regsAt u) d := by
  unfold regsAt
  rw [regRun_append]
  rfl

/-- The registers of `regsAt` carry the register tiles of `stateAt`. -/
theorem regsAt_tiles (w : Word) :
    (∀ u, (regsAt w).1 = some u → (stateAt w).tOdd = oddTile u) ∧ ((regsAt w).1 = none → (stateAt w).tOdd = zeroTile) ∧
    (∀ u, (regsAt w).2 = some u → (stateAt w).tEven = evenTile u) ∧ ((regsAt w).2 = none → (stateAt w).tEven = oneTile) := by
  induction w using List.reverseRecOn with
  | nil => refine ⟨fun u h => by simp [regsAt, regRun] at h, fun _ => rfl, fun u h => by simp [regsAt, regRun] at h,
      fun _ => rfl⟩
  | append_singleton v d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [regsAt_snoc]
    cases d
    · refine ⟨fun u h => ?_, fun h => ?_, fun u h => ?_, fun h => ?_⟩
      · simp only [regStep, Option.some.injEq] at h; subst h; exact Standard.tOdd_snoc_one v
      · simp [regStep] at h
      · simp only [regStep, Option.some.injEq] at h; subst h; exact Standard.tEven_snoc_one v
      · simp [regStep] at h
    · refine ⟨fun u h => ?_, fun h => ?_, fun u h => ?_, fun h => ?_⟩
      · simp only [regStep, Option.some.injEq] at h; subst h; exact Standard.tOdd_snoc_two v
      · simp [regStep] at h
      · rw [Standard.tEven_snoc_two]; exact h3 u h
      · rw [Standard.tEven_snoc_two]; exact h4 h
    · refine ⟨fun u h => ?_, fun h => ?_, fun u h => ?_, fun h => ?_⟩
      · rw [Standard.tOdd_snoc_three]; exact h1 u h
      · rw [Standard.tOdd_snoc_three]; exact h2 h
      · simp only [regStep, Option.some.injEq] at h; subst h; exact Standard.tEven_snoc_three v
      · simp [regStep] at h

/-! ### The weak data of the paper and the copies of the odd child -/

open FLatticePaper.Tiles.ChildGlue (keptSet dblOdd oddP oddQ tOddSet tEvenSet pieceSet pieceFlag)

/-- The tile of a register: the initial tiles `T_{0/1}`, `T_{1/1}`, or the standard tile of the register word. -/
def regTile : Option Word → Bool → Finset Site
  | none, true => zeroTile
  | none, false => oneTile
  | some u, true => oddTile u
  | some u, false => evenTile u

/-- The weak data of the paper: the zero-one odometers, the standard tiles of the registers as boundary and partial tiles (both
copies of a doubled piece full, Step 1), and the base condition of Section 6. -/
def paperS : WeakData :=
  { zeroO := ⟨zeroTile, zeroOdometer⟩, oneO := ⟨oneTile, oneOdometer⟩, bdry := regTile,
    partialT := fun r b _ => regTile r b, base := PaperBaseCond }

/-- The copies of the odd child of the nodes are the pieces of `ChildGlue`. -/
theorem oddCopies_eq (w u1 u2 : Word) (i : ℕ) (hi : i < 6) :
    oddCopies w (oddTile u1) (evenTile u2) (evenTile u2) (evenTile u2) i =
      pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) i := by
  have hb : (phase w == 1) = true ∨ (phase w == 1) = false := by cases (phase w == 1) <;> simp
  obtain _ | _ | _ | _ | _ | _ | i := i
  rotate_left 6
  · omega
  all_goals rcases hb with hb | hb <;>
    simp [oddCopies, pieceSet, oddP, oddQ, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, SurgicalDict.offsetP0, hb,
      SiteInduction.shiftS, Finset.coe_image, tOddSet, tEvenSet, add_comm]

/-- The kept parts of the copies of the odd child are those of `ChildGlue`. -/
theorem oddKept_eq (w u1 u2 : Word) (i : ℕ) (hi : i < 6) :
    keptPart (oddCopies w (oddTile u1) (evenTile u2) (evenTile u2) (evenTile u2)) (fun i => decide (2 ≤ i))
        (fun i j => (i = 2 ∧ j = 3) ∨ (i = 4 ∧ j = 5)) i =
      keptSet (pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2)) (pieceFlag (oddP w)) (dblOdd w) i := by
  ext z
  simp only [keptPart, keptSet, Set.mem_setOf_eq, pieceFlag, dblOdd, ClosedPathCycle.oddP_length]
  rw [oddCopies_eq w u1 u2 i hi]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ⟨j, hj, hf, hd, hz⟩ => h2 ⟨j, hj, hf, by omega, ?_⟩⟩
    rw [oddCopies_eq w u1 u2 j (by omega)]; exact hz
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ⟨j, hj, hf, hd, hz⟩ => h2 ⟨j, hj, hf, by omega, ?_⟩⟩
    rw [← oddCopies_eq w u1 u2 j (by omega)]; exact hz

theorem mem_shift_of {T : Finset Site} {y z a : Site} (hy : y ∈ T) (h : y + a = z) : z ∈ Standard.shift T a := by
  rw [Standard.mem_shift, ← h]
  simpa using hy

/-- Every copy of the odd child lies in the odd tile. -/
theorem oddCopy_sub (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hT1 : (stateAt w).tOdd = oddTile u1)
    (hT2 : (stateAt w).tEven = evenTile u2) (i : ℕ) (hi : i < 6) :
    oddCopies w (oddTile u1) (evenTile u2) (evenTile u2) (evenTile u2) i ⊆ ↑(oddTile w) := by
  intro z hz
  have ho : oddTile w = Standard.oddChildB (phase w == 1) (oddTile u1) (evenTile u2) (parentsAt w).odd
      (parentsAt w).even := by
    show (Standard.childTiles w (stateAt w)).1 = _
    rw [SiteInduction.childTiles_nonbase w hw, hT1, hT2, Standard.stateAt_par]
  rw [Finset.mem_coe, ho]
  have hb : (phase w == 1) = true ∨ (phase w == 1) = false := by cases (phase w == 1) <;> simp
  obtain _ | _ | _ | _ | _ | _ | i := i
  rotate_left 6
  · omega
  all_goals
    rcases hb with hb | hb <;>
    simp only [oddCopies, hb, SurgicalDict.offsetP0, if_true, if_false, Bool.false_eq_true, Finset.coe_image,
      Set.mem_image, Finset.mem_coe] at hz <;>
    obtain ⟨y, hy, rfl⟩ := hz <;>
    simp only [Standard.oddChildB, Finset.mem_union, Standard.mem_shift, hb] <;>
    (try abel_nf) <;>
    simp [hy]

/-! ### The doubled pieces of the glued odometer -/

/-- A doubled piece from the register odometer `o`: `o` on its first copy and the translate `o(y - v) + k` on the second. -/
def dblPiece (o : PartialOdometer) (v : Site) (k : ℤ) : PartialOdometer :=
  ⟨o.dom ∪ o.dom.image (· + v), fun y => if y ∈ o.dom then o.val y else o.val (y - v) + k⟩

/-- The second copy of `dblPiece`. -/
def dblSecond (o : PartialOdometer) (v : Site) (k : ℤ) : PartialOdometer := ⟨o.dom.image (· + v), fun y => o.val (y - v) + k⟩

theorem dbl_on (o : PartialOdometer) (v : Site) (k : ℤ)
    (hcons : ∀ y ∈ o.dom, y - v ∈ o.dom → o.val y = o.val (y - v) + k) :
    IsWeakDoublingOn o.dom o.dom v o (dblPiece o v k) (dblSecond o v k) := by
  refine ⟨rfl, rfl, rfl, fun x hx => by simp [dblPiece, hx], fun x hx => ?_⟩
  simp only [dblSecond, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [dblPiece, dblSecond]
  split_ifs with h
  · exact hcons _ h (by simpa using hy)
  · rfl

theorem dbl_respects (n d : ℤ) (wh wv : BinaryWord) (s : Side) (o : PartialOdometer) (v : Site) (k : ℤ)
    (hin : ∀ t ∈ sideString wh wv (0, 0) s, ∀ x ∈ tileShape t.1, x + t.2 ∈ o.dom) :
    DoublingRespect.RespectsSideTranslation n d false wh wv s v o (dblSecond o v k) := by
  intro t ht
  refine ⟨hin t ht, fun x hx => ?_, ?_⟩
  · simp only [dblSecond, Finset.mem_image]
    exact ⟨x + t.2, hin t ht x hx, by abel⟩
  · have hmap : (tileShape t.1).map (· + (t.2 + v)) = ((tileShape t.1).map (· + t.2)).map (· + v) := by
      rw [List.map_map]; congr 1; funext y; simp [add_assoc]
    have hne : unitSquares ((tileShape t.1).map (· + t.2)) ≠ [] := by
      rw [chain_unitSquares_map_add]; simpa using unitSquares_tileShape_ne t.1
    have hfun : (dblSecond o v k).val = fun y => o.val (y - v) + (0 : Site).1 * y.1 + (0 : Site).2 * y.2 + k := by
      funext y; simp [dblSecond]
    rw [hmap, hfun, slopeOf_translate_affine o.val _ v 0 k hne]
    simp [offsetA]

theorem dbl_std (oddChild sideSign fp : Bool) (n d : ℤ) (wh wv : BinaryWord) (o : PartialOdometer) (v : Site) (k : ℤ)
    (hcons : ∀ y ∈ o.dom, y - v ∈ o.dom → o.val y = o.val (y - v) + k)
    (hin : ∀ t ∈ sideString wh wv (0, 0) (DoublingRespect.doublingSide oddChild sideSign), ∀ x ∈ tileShape t.1,
      x + t.2 ∈ o.dom) :
    IsWeakDoublingStd oddChild sideSign fp n d false wh wv o.dom o.dom v o (dblPiece o v k) := by
  cases fp
  · exact ⟨dblSecond o v k, by simpa using ⟨dbl_on o v k hcons, dbl_respects n d wh wv _ o v k hin⟩⟩
  · refine ⟨o, ?_⟩
    simp only [if_true]
    refine ⟨dblSecond o v k, k, trivial, ⟨rfl, fun x hx => ?_⟩, dbl_on o v k hcons, dbl_respects n d wh wv _ o v k hin⟩
    simp [offsetA, dblSecond]

/-! ### The odd weak node from the glue of the existence step -/

open FLatticePaper.Tiles.ClosedPathAssembly (placedOdd affOdd)
open FLatticePaper.Tiles.ClosedPathSum (dot2)
open FLatticePaper.Tiles.SurgicalDict (offsetP0)
open FLatticePaper.Construction (texV1Odd texV1Even texV2)

theorem oddOffsets (w : Word) :
    (oddP w).getD 0 0 = offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .p1Plus ∧
    (oddP w).getD 1 0 = offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .p1Minus ∧
    (oddQ w).getD 0 0 = offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DPlus ∧
    (oddQ w).getD 1 0 = texV1Even (parentsAt w).even + offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd)
        (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DPlus ∧
    (oddQ w).getD 2 0 = offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DMinus ∧
    (oddQ w).getD 3 0 = texV1Even (parentsAt w).even + offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd)
        (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DMinus := by
  cases h : (phase w == 1) <;>
    simp only [oddP, oddQ, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, SurgicalDict.offsetP0, h, if_true,
      if_false, Bool.false_eq_true, List.getD_cons_zero, List.getD_cons_succ] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | abel

theorem oddAffs (w : Word) :
    affOdd (parentsAt w).odd (parentsAt w).even 0 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .p1Plus ∧
    affOdd (parentsAt w).odd (parentsAt w).even 1 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .p1Minus ∧
    affOdd (parentsAt w).odd (parentsAt w).even 2 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .q1DPlus ∧
    affOdd (parentsAt w).odd (parentsAt w).even 3 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .q1DPlus ∧
    affOdd (parentsAt w).odd (parentsAt w).even 4 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .q1DMinus ∧
    affOdd (parentsAt w).odd (parentsAt w).even 5 = p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den
        (parentsAt w).even.num (parentsAt w).even.den .q1DMinus := by
  cases h : (phase w == 1) <;>
    simp [affOdd, p0AffTab, pairAffine, offsetA] <;> rfl

theorem mem_piece_q (w u1 u2 : Word) (j : ℕ) (hj : 2 ≤ j) (y : Site) (hy : y ∈ evenTile u2) :
    y + (oddQ w).getD (j - 2) 0 ∈ pieceSet (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) j := by
  unfold pieceSet
  rw [if_neg (by rw [ClosedPathCycle.oddP_length]; omega), ClosedPathCycle.oddP_length]
  exact ⟨y, by simpa [tEvenSet] using hy, rfl⟩

/-- The two copies of a doubled piece of the glue agree on their overlap: the glued values of the two copies of the even register
differ by the constant `κ (j + 1) - κ j`. -/
theorem glue_cons (w u1 u2 : Word) (tO tE : Word → PartialOdometer) (hdE : (tE u2).dom = evenTile u2) (κ : ℕ → ℤ)
    (hD : ChildGlue.DoubledAgreeOdd w u1 u2 (dblOdd w) (fun i z => placedOdd w (tO u1).val (tE u2).val 0 i z + κ i))
    (j : ℕ) (hj : j = 2 ∨ j = 4)
    (hoff : (oddQ w).getD (j + 1 - 2) 0 = texV1Even (parentsAt w).even + (oddQ w).getD (j - 2) 0)
    (haff : affOdd (parentsAt w).odd (parentsAt w).even j = affOdd (parentsAt w).odd (parentsAt w).even (j + 1))
    (y : Site) (hy : y ∈ (tE u2).dom) (hyv : y - texV1Even (parentsAt w).even ∈ (tE u2).dom) :
    (tE u2).val y = (tE u2).val (y - texV1Even (parentsAt w).even) + (κ (j + 1) - κ j) := by
  have hlen : (oddP w).length + (oddQ w).length = 6 := by rw [ClosedPathCycle.oddP_length, ClosedPathCycle.oddQ_length]
  have m1 := mem_piece_q w u1 u2 j (by omega) y (hdE ▸ hy)
  have m2 := mem_piece_q w u1 u2 (j + 1) (by omega) (y - texV1Even (parentsAt w).even) (hdE ▸ hyv)
  have e : y - texV1Even (parentsAt w).even + (oddQ w).getD (j + 1 - 2) 0 = y + (oddQ w).getD (j - 2) 0 := by
    rw [hoff]; abel
  rw [e] at m2
  have hP := ClosedPathCycle.oddP_length w
  have h := hD j (j + 1) (by omega) (by omega) (by omega)
    (by simp only [pieceFlag, hP, decide_eq_decide]; omega) ⟨rfl, by rw [hP]; omega⟩ _ m1 m2
  simp only [placedOdd, if_neg (show ¬ j < 2 by omega), if_neg (show ¬ j + 1 < 2 by omega), Pi.zero_apply,
    add_zero] at h
  rw [← e, haff] at h
  have e1 : y + (oddQ w).getD (j - 2) 0 - (oddQ w).getD (j - 2) 0 = y := by abel
  have e2 : y - texV1Even (parentsAt w).even + (oddQ w).getD (j + 1 - 2) 0 - (oddQ w).getD (j + 1 - 2) 0 =
      y - texV1Even (parentsAt w).even := by abel
  rw [← e] at e1
  rw [e1, e2] at h
  linarith

/-- The side strings of a tile lie in it, from `RespectsAnchored`. -/
theorem side_inside (T : Finset Site) (wh wv : BinaryWord) (S : GInt → ℤ) (hR : RespectsAnchored T wh wv S) (s : Side) :
    ∀ t ∈ sideString wh wv (0, 0) s, ∀ x ∈ tileShape t.1, x + t.2 ∈ T := by
  intro t ht x hx
  apply hR.1
  unfold placedSites
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨t, ?_, x, hx, rfl⟩
  cases s <;> simp only [sideString, List.mem_append] at ht ⊢ <;> tauto

/-- **The odd weak node from the existence glue**, for the paper's data (Step 1 of `lemma:weak_standard_odometer_properties`):
for a word `w` that is not a base word, with registers `u1`, `u2`, if the tile odometers of the registers have the standard tiles as
domains, the even one respects its boundary strings, copies of different parents meet only in the marks (`MixedPiecesInMarksOdd`,
claim (d)) and condition (C) holds for the placed subodometers (`ClosedPathOdd`), then the glued odometer on `T(p_0)` (the values of
the subodometers on the kept parts, `glue_kept_pieces`) satisfies `OddNodeP`: the doubled pieces are the even register odometer on
their first copy and its translate on the second. -/
theorem oddNode_of_glue (w u1 u2 : Word) (hw : ¬ Standard.IsBase w) (hreg : regsAt w = (some u1, some u2))
    (tO tE : Word → PartialOdometer) (hdO : (tO u1).dom = oddTile u1) (hdE : (tE u2).dom = evenTile u2)
    (hRQ : RespectsAnchored (tE u2).dom (SiteStrings.hWordOf u2 true) (SiteStrings.vWordOf u2 true) (tE u2).val)
    (hd : MixedPieces.MixedPiecesInMarksOdd w)
    (hC : ChildGlue.ClosedPathOdd w u1 u2 (placedOdd w (tO u1).val (tE u2).val 0)) :
    ∃ wo : PartialOdometer, wo.dom = oddTile w ∧ OddNodeP paperS wo tO tE w := by
  obtain ⟨hr1, -, hr3, -⟩ := regsAt_tiles w
  have hT1 : (stateAt w).tOdd = oddTile u1 := hr1 u1 (by rw [hreg])
  have hT2 : (stateAt w).tEven = evenTile u2 := hr3 u2 (by rw [hreg])
  obtain ⟨κ, hM, hD⟩ := hC
  obtain ⟨g, hg⟩ := ChildGlue.glue_kept_pieces (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (SiteInduction.marksOdd u1)
    (SiteInduction.marksEven u2) (dblOdd w) (fun i z => placedOdd w (tO u1).val (tE u2).val 0 i z + κ i)
    (fun a ha b hb z h1 h2 => hd u1 u2 hT1 hT2 a ha b hb z h1 h2) hM hD
  have hlen : (oddP w).length + (oddQ w).length = 6 := by rw [ClosedPathCycle.oddP_length, ClosedPathCycle.oddQ_length]
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := oddOffsets w
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := oddAffs w
  have hgk : ∀ i, i < 6 → ∀ z ∈ keptPart (oddCopies w (oddTile u1) (evenTile u2) (evenTile u2) (evenTile u2))
      (fun i => decide (2 ≤ i)) (fun i j => (i = 2 ∧ j = 3) ∨ (i = 4 ∧ j = 5)) i,
      z ∈ oddTile w ∧ g z = placedOdd w (tO u1).val (tE u2).val 0 i z + κ i := by
    intro i hi z hz
    refine ⟨oddCopy_sub w u1 u2 hw hT1 hT2 i hi hz.1, ?_⟩
    rw [oddKept_eq w u1 u2 i hi] at hz
    exact hg i (by rw [hlen]; exact hi) z hz
  have hcP := glue_cons w u1 u2 tO tE hdE κ hD 2 (Or.inl rfl) (by rw [show 2 + 1 - 2 = 1 from rfl, o3, o2])
    (by rw [a2, a3])
  have hcM := glue_cons w u1 u2 tO tE hdE κ hD 4 (Or.inr rfl) (by rw [show 4 + 1 - 2 = 3 from rfl, o5, o4])
    (by rw [a4, a5])
  have hin := side_inside _ _ _ _ hRQ
  refine ⟨⟨oddTile w, g⟩, rfl, ?_⟩
  simp only [OddNodeP, hreg, regOdo, paperS, regTile, hdO]
  refine ⟨dblPiece (tE u2) (texV1Even (parentsAt w).even) (κ 3 - κ 2),
    dblPiece (tE u2) (texV1Even (parentsAt w).even) (κ 5 - κ 4), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := dbl_std true true (phase w == 1) (parentsAt w).even.num (parentsAt w).even.den _ _ (tE u2) _ _
      (fun y hy hyv => hcP y hy hyv) (hin _)
    rwa [hdE] at h
  · have h := dbl_std true false (!(phase w == 1)) (parentsAt w).even.num (parentsAt w).even.den _ _ (tE u2) _ _
      (fun y hy hyv => hcM y hy hyv) (hin _)
    rwa [hdE] at h
  · refine ⟨κ 0, fun x hx => (hgk 0 (by omega) x hx).1, fun x hx => ?_⟩
    dsimp only
    rw [(hgk 0 (by omega) x hx).2]
    simp only [placedOdd, if_pos (show 0 < 2 by omega), o0, a0, dot2, Pi.zero_apply, add_zero]
  · refine ⟨κ 1, fun x hx => (hgk 1 (by omega) x hx).1, fun x hx => ?_⟩
    dsimp only
    rw [(hgk 1 (by omega) x hx).2]
    simp only [placedOdd, if_pos (show 1 < 2 by omega), o1, a1, dot2, Pi.zero_apply, add_zero]
  · refine ⟨κ 2, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hx with hx | hx
      · exact (hgk 2 (by omega) x hx).1
      · exact (hgk 3 (by omega) x hx).1
    · rcases hx with hx | hx
      · have hc := hx.1
        simp only [oddCopies, ite_self, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc
        obtain ⟨y, hy, rfl⟩ := hc
        dsimp only
        rw [(hgk 2 (by omega) _ hx).2]
        simp only [placedOdd, if_neg (show ¬ 2 < 2 by omega), show 2 - 2 = 0 from rfl, o2, a2, dot2, Pi.zero_apply,
          add_zero, add_sub_cancel_right, dblPiece, hdE, hy, if_true]
      · have hc := hx.1
        simp only [oddCopies, ite_self, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc
        obtain ⟨y, hy, rfl⟩ := hc
        dsimp only
        rw [(hgk 3 (by omega) _ hx).2]
        have e1 : y + (texV1Even (parentsAt w).even + offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd)
            (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DPlus) -
            offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)
              (texV2 (parentsAt w).even) .q1DPlus = y + texV1Even (parentsAt w).even := by abel
        simp only [placedOdd, if_neg (show ¬ 3 < 2 by omega), show 3 - 2 = 1 from rfl, o3, a3, dot2, Pi.zero_apply,
          add_zero, add_sub_cancel_right, dblPiece, e1]
        split_ifs with hm
        · have := hcP (y + texV1Even (parentsAt w).even) hm (by simpa using hdE ▸ hy)
          rw [add_sub_cancel_right] at this
          linarith
        · ring
  · refine ⟨κ 4, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hx with hx | hx
      · exact (hgk 4 (by omega) x hx).1
      · exact (hgk 5 (by omega) x hx).1
    · rcases hx with hx | hx
      · have hc := hx.1
        simp only [oddCopies, ite_self, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc
        obtain ⟨y, hy, rfl⟩ := hc
        dsimp only
        rw [(hgk 4 (by omega) _ hx).2]
        simp only [placedOdd, if_neg (show ¬ 4 < 2 by omega), show 4 - 2 = 2 from rfl, o4, a4, dot2, Pi.zero_apply,
          add_zero, add_sub_cancel_right, dblPiece, hdE, hy, if_true]
      · have hc := hx.1
        simp only [oddCopies, ite_self, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc
        obtain ⟨y, hy, rfl⟩ := hc
        dsimp only
        rw [(hgk 5 (by omega) _ hx).2]
        have e1 : y + (texV1Even (parentsAt w).even + offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd)
            (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) .q1DMinus) -
            offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)
              (texV2 (parentsAt w).even) .q1DMinus = y + texV1Even (parentsAt w).even := by abel
        simp only [placedOdd, if_neg (show ¬ 5 < 2 by omega), show 5 - 2 = 3 from rfl, o5, a5, dot2, Pi.zero_apply,
          add_zero, add_sub_cancel_right, dblPiece, e1]
        split_ifs with hm
        · have := hcM (y + texV1Even (parentsAt w).even) hm (by simpa using hdE ▸ hy)
          rw [add_sub_cancel_right] at this
          linarith
        · ring

end FLatticePaper.Tiles.WeakStepPaper
