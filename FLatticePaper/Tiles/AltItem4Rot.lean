import FLatticePaper.Tiles.AltItem4OddUp
import FLatticePaper.Tiles.AltItem4EvenUp

/-! # Item (4) of `lemma:alternate_tile_properties` in all eight directions

The quarter-turn `R z = i z` maps `T̂(p₀)` of `w` onto `T̂(q₀)` of `swapW w` and `T̂(q₀)` onto `T̂(p₀)` (w5's
`AltRotStep.altRot`), the copies of the decompositions onto copies (`rot_oddCopies`, `rot_evenCopies`), the lattice of each
standard tile onto the lattice of the rotated one (`latV_rot_even`, `latV_rot_odd`: `R v₁ = v₂'`, `R v₂ = -v₁'`), and
two lattice-adjacent translates of a standard tile onto two lattice-adjacent translates (`stackedAt_rot`). So the conclusion
of item (4) transports (`concl_rot`); with `v ↦ -v` (`concl_neg`) the directions treated directly (`k v₁ + v₂` for the even
child, `v₂` for the odd one) give all eight. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB rot swapW)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces

/-! ### Translations, half-turns and quarter-turns of the conclusion -/

theorem mem_rot_shift' (T : Tile) (a x τ : Site) (h : x ∈ shift T a) : mulI x + τ ∈ shift (shift (rot T) (mulI a)) τ := by
  rw [mem_shift, mem_shift, Standard.mem_rot]
  rw [mem_shift] at h
  convert h using 1; ext <;> (simp [mulI]; try ring)

theorem nbr_rot {i j : ℤ} (h : Nbr i j) : Nbr (-j) i := by
  unfold Nbr at h ⊢; omega

theorem latV_neg (u : Word) (par : Bool) (i j : ℤ) : latV u par (-i) (-j) = -latV u par i j := by
  unfold latV; ext <;> simp <;> ring

theorem stackedAt_shift (c x : Site) (h : StackedAt x) : StackedAt (x + c) := by
  obtain ⟨u, par, a, i, j, hn, h1, h2⟩ := h
  refine ⟨u, par, a + c, i, j, hn, ?_, ?_⟩
  · rw [mem_shift] at h1 ⊢; convert h1 using 1; abel
  · rw [mem_shift] at h2 ⊢; convert h2 using 1; abel

/-- **`v ↦ -v`.** -/
theorem concl_neg (C : List Tile) (v x : Site) (h : Concl C v (x + v)) : Concl C (-v) x := by
  rcases h with ⟨J, hJ, hx, hJv⟩ | h
  · refine Or.inl ⟨shift J (-v), hJv, ?_, ?_⟩
    · rw [mem_shift, sub_neg_eq_add]; exact hx
    · rw [shift_shift', neg_neg, neg_add_cancel, AltRotStep.shift_zero]; exact hJ
  · have := stackedAt_shift (-v) _ h
    exact Or.inr (by convert this using 1; abel)

/-! ### The lattices under the quarter-turn -/

theorem texV_rot_even (s : Fraction) (hs : s.Even) :
    texV2 s.rotate = mulI (texV1Even s) ∧ texV1Odd s.rotate = -mulI (texV2 s) := by
  have hp : (s.num + s.den) % 2 = 0 := hs
  rw [Fraction.rotate_of_even hs]
  constructor <;> ext <;> simp [texV1Odd, texV1Even, texV2, mulI] <;> omega

theorem texV_rot_odd (f : Fraction) (hf : f.Odd) :
    texV2 f.rotate = mulI (texV1Odd f) ∧ texV1Even f.rotate = -mulI (texV2 f) := by
  rw [Fraction.rotate_of_odd hf]
  constructor <;> ext <;> simp [texV1Odd, texV1Even, texV2, mulI] <;> ring

theorem curO_swapW (u : Word) : SiteInduction.curO (swapW u) = (SiteInduction.curE u).rotate := by
  show (parentsAt (swapW u)).current .odd = ((parentsAt u).current .even).rotate
  rw [Standard.parentsAt_swapW, (parentsAt_valid u).rotate_current_even]

theorem curE_swapW (u : Word) : SiteInduction.curE (swapW u) = (SiteInduction.curO u).rotate := by
  show (parentsAt (swapW u)).current .even = ((parentsAt u).current .odd).rotate
  rw [Standard.parentsAt_swapW, (parentsAt_valid u).rotate_current_odd]

/-- `R(i v₁ + j v₂) = -j v₁' + i v₂'` for the even tile of `u` and the odd tile of `swapW u`. -/
theorem latV_rot_even (u : Word) (i j : ℤ) : mulI (latV u true i j) = latV (swapW u) false (-j) i := by
  obtain ⟨e1, e2⟩ := texV_rot_even _ (parentsAt_valid u).current_even_parity
  simp only [latV, latV1, fracOf, if_true, Bool.false_eq_true, if_false, curO_swapW]
  rw [e1, e2]
  ext <;> (simp [mulI]; try ring)

/-- `R(i v₁ + j v₂) = -j v₁' + i v₂'` for the odd tile of `u` and the even tile of `swapW u`. -/
theorem latV_rot_odd (u : Word) (i j : ℤ) : mulI (latV u false i j) = latV (swapW u) true (-j) i := by
  obtain ⟨e1, e2⟩ := texV_rot_odd _ (parentsAt_valid u).current_odd_parity
  simp only [latV, latV1, fracOf, if_true, Bool.false_eq_true, if_false, curE_swapW]
  rw [e1, e2]
  ext <;> (simp [mulI]; try ring)

theorem tileOf_rot (u : Word) (par : Bool) :
    rot (SiteStrings.tileOf u par) = shift (SiteStrings.tileOf (swapW u) (!par)) (Standard.tF (fracOf u par)) := by
  cases par
  · simpa [SiteStrings.tileOf, fracOf] using (Standard.rot_standard_tiles u).1
  · simpa [SiteStrings.tileOf, fracOf] using (Standard.rot_standard_tiles u).2

/-- **The enclosure form is invariant under the quarter-turn.** -/
theorem stackedAt_rot (τ x : Site) (h : StackedAt x) : StackedAt (mulI x + τ) := by
  obtain ⟨u, par, a, i, j, hn, h1, h2⟩ := h
  have hL : mulI (latV u par i j) = latV (swapW u) (!par) (-j) i := by
    cases par
    · exact latV_rot_odd u i j
    · exact latV_rot_even u i j
  refine ⟨swapW u, !par, Standard.tF (fracOf u par) + mulI a + τ, -j, i, nbr_rot hn, ?_, ?_⟩
  · have := mem_rot_shift' _ _ _ τ h1
    rw [tileOf_rot, shift_shift', shift_shift'] at this
    convert this using 2; abel
  · have := mem_rot_shift' _ _ _ τ h2
    rw [tileOf_rot, shift_shift', shift_shift'] at this
    convert this using 2
    have e : mulI (a + latV u par i j) = mulI a + mulI (latV u par i j) := by ext <;> (simp [mulI]; try ring)
    rw [e, hL]; abel

/-- **The conclusion of item (4) transports along the quarter-turn**, given that the copies go to copies. -/
theorem concl_rot (C C' : List Tile) (τ : Site) (hC : ∀ K ∈ C, shift (rot K) τ ∈ C') (v x : Site) (h : Concl C v x) :
    Concl C' (mulI v) (mulI x + τ) := by
  rcases h with ⟨J, hJ, hx, hJv⟩ | h
  · refine Or.inl ⟨shift (rot J) τ, hC J hJ, ?_, ?_⟩
    · have := mem_rot_shift' J 0 x τ (by rw [mem_shift, sub_zero]; exact hx)
      rwa [show mulI (0 : Site) = 0 by ext <;> simp [mulI], AltRotStep.shift_zero] at this
    · have e : shift (shift (rot J) τ) (-mulI v) = shift (rot (shift J (-v))) τ := by
        rw [Standard.rot_shift, shift_shift', shift_shift']
        congr 1; ext <;> simp [mulI] <;> ring
      rw [e]; exact hC _ hJv
  · exact Or.inr (stackedAt_rot τ x h)

/-- The copies of the odd decomposition of `w` go to copies of the rotated decomposition of `swapW w`. -/
theorem rot_oddCopies {w : Word} (hw : ¬ IsBase w) (K : Tile) (hK : K ∈ oddCopies w) :
    shift (rot K) (AltRotStep.tauO w) ∈ evenCopies (swapW w) := by
  have h3 : ¬ ∀ d ∈ w, d = Digit.three := fun h => hw (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ w, d = Digit.two := fun h => hw (Or.inr (Or.inr h))
  have hRo := ((Standard.good_and_rot w).2.1).resolve_left h3
  have hRe := ((Standard.good_and_rot w).2.2).resolve_left h2
  have hV := parentsAt_valid w
  have hpo : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hqe : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  have hpar : parentsAt (swapW w) = ⟨(parentsAt w).even.rotate, (parentsAt w).odd.rotate⟩ :=
    Standard.parentsAt_swapW w
  have hph : (phase (swapW w) == 1) = (phase w == 1) := by rw [Standard.phase_swapW]
  simp only [oddCopies, List.mem_append, List.mem_map] at hK
  simp only [evenCopies, hpar, hph, Fraction.rotate_of_even hV.even_parity, Fraction.rotate_of_odd hV.odd_parity]
  unfold AltRotStep.tauO
  rcases hK with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [Standard.rot_shift, hRo, shift_shift', shift_shift']
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
    simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [evenQOffs, List.mem_cons, List.not_mem_nil, or_false]
    rcases AltBounds.phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at ha ⊢
    · rcases ha with rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inl ?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inr (Or.inr (Or.inr (?_)))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
    · rcases ha with rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inr (Or.inr (Or.inr (?_)))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inr (Or.inl ?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
  · rw [Standard.rot_shift, hRe, shift_shift', shift_shift']
    refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
    simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [evenPOffs, List.mem_cons, List.not_mem_nil, or_false]
    rcases AltBounds.phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at ha ⊢
    · rcases ha with rfl | rfl
      · refine Or.inr (?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
    · rcases ha with rfl | rfl
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inr (?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauOdd, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega

/-- The copies of the even decomposition of `w` go to copies of the rotated decomposition of `swapW w`. -/
theorem rot_evenCopies {w : Word} (hw : ¬ IsBase w) (K : Tile) (hK : K ∈ evenCopies w) :
    shift (rot K) (AltRotStep.tauE w) ∈ oddCopies (swapW w) := by
  have h3 : ¬ ∀ d ∈ w, d = Digit.three := fun h => hw (Or.inr (Or.inl h))
  have h2 : ¬ ∀ d ∈ w, d = Digit.two := fun h => hw (Or.inr (Or.inr h))
  have hRo := ((Standard.good_and_rot w).2.1).resolve_left h3
  have hRe := ((Standard.good_and_rot w).2.2).resolve_left h2
  have hV := parentsAt_valid w
  have hpo : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := hV.odd_parity
  have hqe : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := hV.even_parity
  have hpar : parentsAt (swapW w) = ⟨(parentsAt w).even.rotate, (parentsAt w).odd.rotate⟩ :=
    Standard.parentsAt_swapW w
  have hph : (phase (swapW w) == 1) = (phase w == 1) := by rw [Standard.phase_swapW]
  simp only [evenCopies, List.mem_append, List.mem_map] at hK
  simp only [oddCopies, hpar, hph, Fraction.rotate_of_even hV.even_parity, Fraction.rotate_of_odd hV.odd_parity]
  unfold AltRotStep.tauE
  rcases hK with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [Standard.rot_shift, hRo, shift_shift', shift_shift']
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
    simp only [evenPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false]
    rcases AltBounds.phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at ha ⊢
    · rcases ha with rfl | rfl
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inr (?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
    · rcases ha with rfl | rfl
      · refine Or.inr (?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
  · rw [Standard.rot_shift, hRe, shift_shift', shift_shift']
    refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
    simp only [evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false]
    rcases AltBounds.phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at ha ⊢
    · rcases ha with rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inr (Or.inr (Or.inr (?_)))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
      · refine Or.inr (Or.inl ?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauShort, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2] <;> omega
    · rcases ha with rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inl ?_)
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inl ?_
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inr (Or.inr (Or.inr (?_)))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext <;> simp [AltRotStep.offP0, AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, AltRotStep.tauEven, AltRotStep.tauLong, Standard.tF, Standard.tV, mulI, texV1Odd, texV1Even, texV2, Bool.false_eq_true] <;> omega

/-! ### The rotated directions -/

/-- The odd child of `w` in the direction `R v`, from the even child of `swapW w` in the direction `v`. -/
theorem odd_of_even_rot {w : Word} (hw : ¬ IsBase w) (v : Site)
    (H : ∀ y, y ∈ altEvenTile AltRotStep.B (swapW w) → y - v ∈ altEvenTile AltRotStep.B (swapW w) →
      Concl (evenCopies (swapW w)) v y)
    (x : Site) (h1 : x ∈ altOddTile AltRotStep.B w) (h2 : x - mulI v ∈ altOddTile AltRotStep.B w) :
    Concl (oddCopies w) (mulI v) x := by
  have hR := (AltRotStep.altRot (swapW w)).2
  rw [AltRotStep.swapW_swapW] at hR
  rw [← hR, mem_shift, Standard.mem_rot] at h1 h2
  have hw' := Standard.nonbase_swap hw
  have hC := concl_rot _ _ _ (fun K hK => by
    have := rot_evenCopies hw' K hK
    rwa [AltRotStep.swapW_swapW] at this) v _ (H _ h1 (by convert h2 using 1; ext <;> simp [mulI] <;> ring))
  convert hC using 1; ext <;> simp [mulI]

/-- The even child of `w` in the direction `R v`, from the odd child of `swapW w` in the direction `v`. -/
theorem even_of_odd_rot {w : Word} (hw : ¬ IsBase w) (v : Site)
    (H : ∀ y, y ∈ altOddTile AltRotStep.B (swapW w) → y - v ∈ altOddTile AltRotStep.B (swapW w) →
      Concl (oddCopies (swapW w)) v y)
    (x : Site) (h1 : x ∈ altEvenTile AltRotStep.B w) (h2 : x - mulI v ∈ altEvenTile AltRotStep.B w) :
    Concl (evenCopies w) (mulI v) x := by
  have hR := (AltRotStep.altRot (swapW w)).1
  rw [AltRotStep.swapW_swapW] at hR
  rw [← hR, mem_shift, Standard.mem_rot] at h1 h2
  have hw' := Standard.nonbase_swap hw
  have hC := concl_rot _ _ _ (fun K hK => by
    have := rot_oddCopies hw' K hK
    rwa [AltRotStep.swapW_swapW] at this) v _ (H _ h1 (by convert h2 using 1; ext <;> simp [mulI] <;> ring))
  convert hC using 1; ext <;> simp [mulI]

/-- The directions `k v₁ + s v₂`, `s = ±1`, of the even child. -/
theorem item4_even_vert {w : Word} (hw : ¬ IsBase w) (k s : ℤ) (hk : k = -1 ∨ k = 0 ∨ k = 1) (hs : s = 1 ∨ s = -1)
    (x : Site) (h1 : x ∈ altEvenTile AltRotStep.B w) (h2 : x - latV w true k s ∈ altEvenTile AltRotStep.B w) :
    Concl (evenCopies w) (latV w true k s) x := by
  rcases hs with rfl | rfl
  · exact item4_even_up hw k hk x h1 h2
  · have e : latV w true k (-1) = -latV w true (-k) 1 := by rw [← latV_neg, neg_neg]
    rw [e] at h2 ⊢
    exact concl_neg _ _ _ (item4_even_up hw (-k) (by omega) _ (by rwa [sub_neg_eq_add] at h2) (by simpa using h1))

/-- The directions `s v₂`, `s = ±1`, of the odd child. -/
theorem item4_odd_vert {w : Word} (hw : ¬ IsBase w) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (x : Site) (h1 : x ∈ altOddTile AltRotStep.B w) (h2 : x - latV w false 0 s ∈ altOddTile AltRotStep.B w) :
    Concl (oddCopies w) (latV w false 0 s) x := by
  rcases hs with rfl | rfl
  · exact item4_odd_up hw x h1 h2
  · have e : latV w false 0 (-1) = -latV w false 0 1 := by rw [← latV_neg, neg_zero]
    rw [e] at h2 ⊢
    exact concl_neg _ _ _ (item4_odd_up hw _ (by rwa [sub_neg_eq_add] at h2) (by simpa using h1))

/-- **Item (4), odd alternate child, all eight directions** `v = i v₁ + j v₂`. -/
theorem item4_odd {w : Word} (hw : ¬ IsBase w) (i j : ℤ) (hi : i = -1 ∨ i = 0 ∨ i = 1) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (hij : ¬ (i = 0 ∧ j = 0)) (x : Site) (h1 : x ∈ altOddTile AltRotStep.B w)
    (h2 : x - latV w false i j ∈ altOddTile AltRotStep.B w) : Concl (oddCopies w) (latV w false i j) x := by
  have hw' := Standard.nonbase_swap hw
  rcases hi with rfl | rfl | rfl
  · have e : latV w false (-1) j = mulI (latV (swapW w) true j 1) := by
      rw [latV_rot_even, AltRotStep.swapW_swapW]
    rw [e] at h2 ⊢
    exact odd_of_even_rot hw _ (fun y hy1 hy2 => item4_even_vert hw' j 1 hj (Or.inl rfl) y hy1 hy2) x h1 h2
  · exact item4_odd_vert hw j (by omega) x h1 h2
  · have e : latV w false 1 j = mulI (latV (swapW w) true j (-1)) := by
      rw [latV_rot_even, AltRotStep.swapW_swapW, neg_neg]
    rw [e] at h2 ⊢
    exact odd_of_even_rot hw _ (fun y hy1 hy2 => item4_even_vert hw' j (-1) hj (Or.inr rfl) y hy1 hy2) x h1 h2

/-- **Item (4), even alternate child, all eight directions** `v = i v₁ + j v₂`. -/
theorem item4_even {w : Word} (hw : ¬ IsBase w) (i j : ℤ) (hi : i = -1 ∨ i = 0 ∨ i = 1) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (hij : ¬ (i = 0 ∧ j = 0)) (x : Site) (h1 : x ∈ altEvenTile AltRotStep.B w)
    (h2 : x - latV w true i j ∈ altEvenTile AltRotStep.B w) : Concl (evenCopies w) (latV w true i j) x := by
  have hw' := Standard.nonbase_swap hw
  rcases hj with rfl | rfl | rfl
  · exact item4_even_vert hw i (-1) hi (Or.inr rfl) x h1 h2
  · rcases hi with rfl | rfl | rfl
    · have e : latV w true (-1) 0 = mulI (latV (swapW w) false 0 1) := by
        rw [latV_rot_odd, AltRotStep.swapW_swapW]
      rw [e] at h2 ⊢
      exact even_of_odd_rot hw _ (fun y hy1 hy2 => item4_odd_vert hw' 1 (Or.inl rfl) y hy1 hy2) x h1 h2
    · exact absurd ⟨rfl, rfl⟩ hij
    · have e : latV w true 1 0 = mulI (latV (swapW w) false 0 (-1)) := by
        rw [latV_rot_odd, AltRotStep.swapW_swapW, neg_neg]
      rw [e] at h2 ⊢
      exact even_of_odd_rot hw _ (fun y hy1 hy2 => item4_odd_vert hw' (-1) (Or.inr rfl) y hy1 hy2) x h1 h2
  · exact item4_even_vert hw i 1 hi (Or.inl rfl) x h1 h2

end FLatticePaper.Tiles.AltItem4
