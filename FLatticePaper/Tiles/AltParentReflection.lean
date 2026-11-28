import FLatticePaper.Tiles.AltParentBase
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.JointRot

/-! The half-turn pairs the six standard entries around the seventh entry of an alternate child. -/

namespace FLatticePaper.Tiles.AltParentReflection

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SurgicalAlt SurgicalDict JointFamily JointInduction JointGlue TileCompatInputs

private def law (o : PartialOdometer) (C e : Site) : Prop :=
  ∀ x ∈ o.dom, C-x ∈ o.dom ∧ 2*(o.val (C-x)-o.val x) = dotS e C - 2 * dotS e x

private theorem unnormalize {o : PartialOdometer} {C e : Site} (hf : AltHalfTurn o C e) (hz : JointRot.SlopeZero o) :
    law o C e := by
  obtain ⟨a,b,hn,h⟩ := hf
  obtain ⟨b',hn'⟩ := hz
  obtain ⟨rfl,-⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hn hn'
  intro x hx
  exact ⟨(h _ hx).1, by simpa [normed, dotS, mul_sub] using (h _ hx).2⟩

private def reflects (C e : Site) (p q : Piece) : Prop :=
  ∃ K : ℤ, ∀ z ∈ q.placed, C-z ∈ p.placed ∧ 2*(pieceVal p (C-z) - pieceVal q z) = K - 2*dotS e z

private theorem std_reflects {o : PartialOdometer} {D a C e : Site} (h : law o D a) (v w s t : Site)
    (hC : D+v+w = C) (he : a+s+t = e) : reflects C e (stdPiece o v s) (stdPiece o w t) := by
  refine ⟨dotS a D + 2*dotS a w + 2*dotS s C, ?_⟩
  rintro z hz
  have hx := (mem_shift.mp (show z ∈ shift o.dom w from hz))
  obtain ⟨hd,hv⟩ := h _ hx
  have k : C-z-v = D-(z-w) := by rw [←hC]; abel
  constructor
  · change C-z ∈ shift o.dom v
    rwa [mem_shift,k]
  · change 2*(o.val (C-z-v) + dotS s (C-z) - (o.val (z-w) + dotS t z)) = _
    rw [k, ← he]
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    linear_combination hv

private def mirrorsAt (ps : List Piece) (C e : Site) (i j : ℕ) : Prop :=
  ∀ q : Piece, ps[j]? = some q → ∃ p : Piece, ps[i]? = some p ∧ p.exc = ∅ ∧ reflects C e p q

private theorem at_std {ps : List Piece} {C e D a : Site} {i j : ℕ} {o : PartialOdometer} {v w s t : Site}
    (hi : ps[i]? = some (stdPiece o v s)) (hj : ps[j]? = some (stdPiece o w t))
    (h : law o D a) (hC : D+v+w = C) (he : a+s+t = e) : mirrorsAt ps C e i j := by
  intro q hq
  rw [hj, Option.some.injEq] at hq
  subst q
  exact ⟨_, hi, rfl, std_reflects h _ _ _ _ hC he⟩

private theorem pair_of_mirrors {ps : List Piece} {C e : Site} {i j : ℕ}
    (hH : mirrorsAt ps C e 6 6) (hs : mirrorsAt ps C e i j) (h : PairCompat ps 6 i) : PairCompat ps 6 j := by
  intro p q hp hq
  obtain ⟨P,hP,exP,K,flipP⟩ := hH _ hp
  obtain ⟨Q,hQ,exQ,L,flipQ⟩ := hs _ hq
  obtain ⟨c,hc⟩ := h _ _ hP hQ
  refine ⟨c + (L-K)/2, fun z zp zq _ _ => ?_⟩
  obtain ⟨xp,ep⟩ := flipP z zp
  obtain ⟨xq,eq⟩ := flipQ z zq
  have g := hc _ xp xq (by simp [exP]) (by simp [exQ])
  omega

private abbrev pLaw (w : Word) (o : PartialOdometer) := law o (vP1 w + vP2 w + (1,-1)) (aP2 w)
private abbrev qLaw (w : Word) (o : PartialOdometer) := law o (vQ1 w + vQ2 w + (1,-1)) (aQ2 w)

private theorem register_laws (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w) :
    let reg := regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    pLaw w (reg (regsAt w).1 true) ∧ qLaw w (reg (regsAt w).2 false) := by
  dsimp only
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := JointRot.regs_some w hw
  have lu := regsAt_lt _ _ (Or.inl hu)
  have lv := regsAt_lt _ _ (Or.inr hv)
  have sl (t : Word) (ht : t.length < w.length) := JointRot.family_slopes D f t.length
    (fun l hl => (hg l (lt_of_le_of_lt hl ht)).1) (JointRot.baseSlopes_paper D hS hA) t le_rfl
  have pu := ((JointRot.parents_of_regs w).1 _ hu).symm
  have qv := ((JointRot.parents_of_regs w).2 _ hv).symm
  simp only [hu, hv, regOdo, JointRot.below_of_lt f w u lu, JointRot.below_of_lt f w v lv,
    pLaw, qLaw, vP1, vP2, vQ1, vQ2, aP2, aQ2, pu, qv]
  exact ⟨unnormalize (hg u lu).2.2.1.2.2.1 (sl u lu).1, unnormalize (hg v lv).2.2.1.2.2.2.1 (sl v lv).2.1⟩

private abbrev oddPieces (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileAltOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w
private abbrev evenPieces (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w

private abbrev reg (D : JointData) (f : Word → JSlice) (w : Word) (odd : Bool) :=
  regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    (if odd then (regsAt w).1 else (regsAt w).2) odd

private def threePairs (ps : List Piece) (C e : Site) : Prop :=
  mirrorsAt ps C e 0 3 ∧ mirrorsAt ps C e 2 1 ∧ mirrorsAt ps C e 4 5

private theorem odd_three (D : JointData) (f : Word → JSlice) (w : Word) (hn : w.getLast? ≠ some .two)
    (hp : pLaw w (reg D f w true)) (hq : qLaw w (reg D f w false)) : threePairs (oddPieces D f w) (altD w true) (altE w) := by
  unfold threePairs
  simp only [oddPieces, tileAltOddPieces, hn, decide_false, Bool.false_eq_true, if_false]
  refine ⟨at_std rfl rfl hp ?_ ?_, at_std rfl rfl hp ?_ ?_, at_std rfl rfl hq ?_ ?_⟩
  all_goals cases ho : W1Odd w <;> ext <;> simp [altD, altE, altOff, altAff, altShifts, altP0Coeff, coeffOff, coeffAffine,
    vP1, vP2, vQ1, vQ2, aP2, aQ2, texV1Odd, texV1Even, texV2, offsetA, ho] <;> ring

private theorem even_three (D : JointData) (f : Word → JSlice) (w : Word) (hn : w.getLast? ≠ some .three)
    (hp : pLaw w (reg D f w true)) (hq : qLaw w (reg D f w false)) : threePairs (evenPieces D f w) (altD w false) (altE w) := by
  unfold threePairs
  simp only [evenPieces, tileAltEvenPieces, hn, decide_false, Bool.false_eq_true, if_false]
  refine ⟨at_std rfl rfl hq ?_ ?_, at_std rfl rfl hq ?_ ?_, at_std rfl rfl hp ?_ ?_⟩
  all_goals cases ho : W1Odd w <;> ext <;> simp [altD, altE, altOff, altAff, altShifts, altQ0Coeff, coeffOff, coeffAffine,
    vP1, vP2, vQ1, vQ2, aP2, aQ2, texV1Odd, texV1Even, texV2, offsetA, ho] <;> ring

private theorem flag_snoc (u : Word) (d : Digit) :
    W1Odd (u++[d]) = (if d = .one then !W1Odd u else W1Odd u) := by
  cases d
  exacts [AltRotStep.phase_snoc_one u, AltRotStep.phase_snoc_two u, AltRotStep.phase_snoc_three u]

private theorem odd_centre (u : Word) (d : Digit) (c : AltCoeff)
    (hc : altQ1Coeff (W1Odd (u++[d])) d = some c) :
    altD u false + altOff (u++[d]) c + altOff (u++[d]) c = altD (u++[d]) true ∧
    altE u + altAff (u++[d]) c + altAff (u++[d]) c = altE (u++[d]) := by
  cases d <;> cases ho : W1Odd u <;>
    simp [flag_snoc, ho, altQ1Coeff] at hc
  all_goals subst c; constructor <;> ext <;>
    simp [altD, altE, altOff, altAff, coeffOff, coeffAffine, vP1, vP2, vQ1, vQ2, aP2, aQ2, texV1Odd, texV1Even,
      texV2, offsetA, flag_snoc, ho,
      parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine] <;> ring

private theorem even_centre (u : Word) (d : Digit) (c : AltCoeff)
    (hc : altP1Coeff (W1Odd (u++[d])) d = some c) :
    altD u true + altOff (u++[d]) c + altOff (u++[d]) c = altD (u++[d]) false ∧
    altE u + altAff (u++[d]) c + altAff (u++[d]) c = altE (u++[d]) := by
  cases d <;> cases ho : W1Odd u <;>
    simp [flag_snoc, ho, altP1Coeff] at hc
  all_goals subst c; constructor <;> ext <;>
    simp [altD, altE, altOff, altAff, coeffOff, coeffAffine, vP1, vP2, vQ1, vQ2, aP2, aQ2, texV1Odd, texV1Even,
      texV2, offsetA, flag_snoc, ho,
      parentsAt_append_singleton, Parents.step, Parents.current, Parents.combine] <;> ring

private theorem centres (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (u : Word) (d : Digit) (hg : GoodBelow D f (u++[d]).length) :
    let w := u++[d]
    mirrorsAt (oddPieces D f w) (altD w true) (altE w) 6 6 ∧
    mirrorsAt (evenPieces D f w) (altD w false) (altE w) 6 6 := by
  dsimp only
  have hu : u.length < (u++[d]).length := by simp
  have z := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  have prop := (hg u hu).2.2.1
  constructor
  · cases hc : altQ1Coeff (W1Odd (u++[d])) d with
    | none =>
      intro q hq
      simp [oddPieces, tileAltOddPieces, altTypeOf, hc] at hq
    | some c =>
      have hr : (regsAt (u++[d])).2 = some u := by
        cases d <;> simp only [WeakStepPaper.regsAt_snoc, regStep]
        simp [altQ1Coeff] at hc
      have hi : (oddPieces D f (u++[d]))[6]? = some (stdPiece (f u).aEven (altOff (u++[d]) c) (altAff (u++[d]) c)) := by
        simp [oddPieces, tileAltOddPieces, altTypeOf, hc, hr, regOdo, JointRot.below_of_lt _ _ _ hu]
      obtain ⟨te, ae⟩ := odd_centre u d c hc
      exact at_std hi hi (unnormalize prop.2.2.2.2.2 z.2.2.2) te ae
  · cases hc : altP1Coeff (W1Odd (u++[d])) d with
    | none =>
      intro q hq
      simp [evenPieces, tileAltEvenPieces, altTypeOf, hc] at hq
    | some c =>
      have hr : (regsAt (u++[d])).1 = some u := by
        cases d <;> simp only [WeakStepPaper.regsAt_snoc, regStep]
        cases W1Odd (u++[.three]) <;> simp_all [altP1Coeff]
      have hi : (evenPieces D f (u++[d]))[6]? = some (stdPiece (f u).aOdd (altOff (u++[d]) c) (altAff (u++[d]) c)) := by
        simp [evenPieces, tileAltEvenPieces, altTypeOf, hc, hr, regOdo, JointRot.below_of_lt _ _ _ hu]
      obtain ⟨te, ae⟩ := even_centre u d c hc
      exact at_std hi hi (unnormalize prop.2.2.2.2.1 z.2.2.1) te ae

private theorem complete {ps : List Piece} {C e : Site} (hH : mirrorsAt ps C e 6 6) (h : threePairs ps C e)
    (hrep : ∀ j ∈ [0,2,4], PairCompat ps 6 j) (j : ℕ) (hj : j < 6) : PairCompat ps 6 j := by
  have h0 := hrep 0 (by simp)
  have h2 := hrep 2 (by simp)
  have h4 := hrep 4 (by simp)
  obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  exacts [h0, pair_of_mirrors hH h.2.1 h2, h2, pair_of_mirrors hH h.1 h0, h4, pair_of_mirrors hH h.2.2 h4]

/-- The seventh entry against all six at any non-base child follows from the three representatives
`0, 2, 4` in each alternate decomposition. All reflection laws use only shorter words. -/
theorem three_representatives (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    : ((∀ i ∈ [0,2,4], PairCompat (oddPieces D f w) 6 i) → ∀ j < 6, PairCompat (oddPieces D f w) 6 j) ∧
      ((∀ i ∈ [0,2,4], PairCompat (evenPieces D f w) 6 i) → ∀ j < 6, PairCompat (evenPieces D f w) 6 j) := by
  obtain ⟨u,d,rfl⟩ : ∃ (u : Word) (d : Digit), w = u++[d] := by
    cases w using List.reverseRecOn with
    | nil => exact (hw (Or.inl rfl)).elim
    | append_singleton u d => exact ⟨u,d,rfl⟩
  obtain ⟨P,Q⟩ := register_laws D hS hA f _ hg hw
  obtain ⟨H,J⟩ := centres D hS hA f u d hg
  constructor
  · intro hrep j hj
    by_cases hn : (u++[d]).getLast? = some .two
    · exact AltParentBase.odd_after_two _ _ _ _ _ _ _ hn j
    · exact complete H (odd_three D f _ hn P Q) hrep j hj
  · intro hrep j hj
    by_cases hn : (u++[d]).getLast? = some .three
    · exact AltParentBase.even_after_three _ _ _ _ _ _ _ hn j
    · exact complete J (even_three D f _ hn P Q) hrep j hj

/-- The three representative overlaps suffice for the alternate-parent input of the tile step. -/
theorem altParentCompatInput_of_three (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (hrep : ∀ f w, GoodBelow D f w.length → ¬ IsBase w → ∀ j ∈ [0,2,4],
      PairCompat (oddPieces D f w) 6 j ∧ PairCompat (evenPieces D f w) 6 j) : AltParentCompatInput D :=
  fun f w hg hw j hj =>
    let h := three_representatives D hS hA f w hg hw
    ⟨h.1 (fun i hi => (hrep f w hg hw i hi).1) j hj, h.2 (fun i hi => (hrep f w hg hw i hi).2) j hj⟩

end FLatticePaper.Tiles.AltParentReflection
