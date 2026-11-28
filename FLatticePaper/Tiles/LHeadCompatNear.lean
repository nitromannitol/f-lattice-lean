import FLatticePaper.Tiles.CorrectedCellsNear
import FLatticePaper.Tiles.TileCompatInputs

/-! The adjacent alternate heads on the overlap of the two ordinary L-corrections at a pure-two exit. -/

namespace FLatticePaper.Tiles.LHeadCompatNear

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SurgicalAlt JointFamily JointInduction JointGlue TileCompatInputs
open BaseTileProps PaperAltBase LCorrecProps JointRot SurgicalDict

private def term (d x y : ℤ) := min (d-y-1) 0 + min (2*d-1-y) 0 + max (y-x-d+1) 0 +
  if (-1 ≤ x ∧ x ≤ 0 ∧ y=2*d) ∨ (d ≤ x ∧ x ≤ d+1 ∧ y=d-2) ∨ (y-x=d-1 ∧ 0<x ∧ x<d) then 1 else 0

set_option maxHeartbeats 400000 in
private theorem term_step (d x y : ℤ) (hd : 3 ≤ d) (h : (x,y) ∈ paperNearStairAltTile d)
    (h' : (x+1,y-d) ∈ paperNearStairAltTile d) : term d x y - term d (x+1) (y-d) = -x := by
  rw [mem_nsAlt] at h h'
  simp only [term,min_def,max_def]
  grind (splits := 24)

private theorem square_shift (z t : ℤ) : (z-2*t)^2/4 = z^2/4 + (t^2-t*z) := by
  rw [show (z-2*t)^2 = z^2 + (t^2-t*z)*4 by ring,Int.add_mul_ediv_right _ _ (by decide)]

/-- Adjacent alternate staircase heads agree with the transverse affine factor throughout their overlap. -/
theorem near_head_period (k x y : ℤ) (hk : 0 ≤ k) :
    let d := 2*k+3
    (x,y) ∈ paperNearStairAltTile d → (x+1,y-d) ∈ paperNearStairAltTile d →
    paperNearStairAltValue d (x,y) - paperNearStairAltValue d (x+1,y-d) =
      (k+1)*x - (k+2)*y + (k+2)^2 := by
  let d := 2*k+3
  change (x,y) ∈ paperNearStairAltTile d → _
  intro h h'
  have ht := term_step d x y (by dsimp [d]; omega) h h'
  have eq (a b : ℤ) : paperNearStairAltValue d (a,b) = -((b-a)^2/4) + term d a b := by
    rw [pnsA]; unfold term; abel
  rw [eq,eq]
  have sh : y-d-(x+1) = (y-x)-2*(k+2) := by dsimp [d]; ring
  rw [sh,square_shift]
  linear_combination ht

private abbrev twos (k : ℕ) := List.replicate k Digit.two
private abbrev den (k : ℕ) := 2*(k : ℤ)+3
private abbrev foot (d : ℤ) (s : Bool) : Site := if s then (1,1) else (-1,d+2)
private abbrev top (s : Bool) : Site := if s then (0,2) else (1,3)

private def headPiece (d : ℤ) (s : Bool) (footTile : Tile) (H : PartialOdometer) : Piece :=
  { odo := H, off := top s, aff := (1,-1),
    exc := {x | x-top s+(0,1) ∈ paperNearStairAltA d ∧ x-foot d s ∈ footTile} }

private theorem two_regs (k : ℕ) : regsAt (twos (k+1)) = (some (twos k), none) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show twos (k+1+1) = twos (k+1)++[.two] from List.replicate_succ', WeakStepPaper.regsAt_snoc,ih]; rfl

private theorem prefix_data (k : ℕ) :
    stripTrailing .three (twos (k+1)) = twos (k+1) ∧ trailingCount .three (twos (k+1)) = 0 ∧
    (twos (k+1)).getLast? = some .two ∧ W1Odd (twos (k+1)) = false ∧
    (!(twos (k+1)).isEmpty && (twos (k+1)).all (fun d => decide (d = Digit.two))) = true := by
  have es : twos (k+1) = twos k++[.two] := List.replicate_succ'
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [es,stripTrailing_snoc]; rfl
  · rw [es,trailingCount_snoc]; rfl
  · rw [es]; simp
  · simp [W1Odd,twos,phase_two]
  · simp [twos,List.replicate_succ]

private theorem short_description (k : ℕ) (s : Bool) (S : WeakData) (P Q H J : Word → PartialOdometer) :
    let v := twos (k+1)
    let d := den k
    let ps := evenLPieces S P Q H J v s false
    headPiece d s (P (twos k)).dom (H (twos k)) ∈ ps ∧
    ((P (twos k)).dom = oddTile (twos k) → (H (twos k)).dom = altOddT (twos k) → S.oneO.dom = oneTile →
      pieceUnion ps = evenLCells v s false) := by
  dsimp only
  obtain ⟨hs,ht,hl,ho,hdb⟩ := prefix_data k
  have one (a : Site) (T : Tile) (x : Site) : x ∈ T.image (· + a) ↔ x-a ∈ T := mem_shift
  constructor
  · cases s <;> simp only [evenLPieces,hs,ht,hl,ho,hdb,two_regs,regOdo,Bool.not_false,Bool.not_true,
      Bool.true_and,Bool.false_eq_true,if_true,if_false,decide_true,zero_smul,zero_add,Int.natCast_zero,
      List.range_succ,List.range_zero,List.nil_append,List.cons_append,List.map_cons,List.map_nil,
      one_smul, Nat.reduceMul, Nat.reduceSub, headPiece, top, foot]
    all_goals
      simp [evenLInitOff,evenLInitAff,q0Off,q0Aff,ho,evenKCoeff,SurgicalDict.offsetQ0,
        altOff,altAff,coeffOff,coeffAffine,vP1,vP2,vQ1,vQ2,aP2,pairAffine,
        texV1Odd,texV1Even,texV2,offsetA,twos,parents_two,one,den,Prod.mk_add_mk]
      ring_nf
      simp [sub_eq_add_neg,add_comm,add_left_comm]
  · intro hp hh hb
    cases s <;> simp [evenLPieces,evenLCells,hs,ht,hl,ho,two_regs,regOdo,
      pieceUnion, Piece.placed,stdPiece,cellData,domOdo,hp,hh,hb]

private theorem alt_base_shape (k : ℕ) :
    altOddT (twos k) = shift (nearStairAltF (den k)) (0,-1) := by
  unfold altOddT
  rw [AltRotStep.altOddTile_of_base _ (AltRotStep.isBase_replicate_two k)]
  change (AltRotStep.B (twos k)).1 = _
  cases k with
  | zero => rfl
  | succ k => rw [AltRotStep.B_two _ (by omega)]

private theorem dom_head (k : ℕ) (z : Site) :
    z ∈ altOddT (twos k) ↔ z+(0,1) ∈ paperNearStairAltTile (den k) := by
  obtain ⟨x,y⟩ := z
  have hd : 3 ≤ den k := by unfold den; omega
  simp only [alt_base_shape,mem_shift,Prod.mk_sub_mk,Prod.mk_add_mk,sub_zero,sub_neg_eq_add,
    add_zero,AltRotBase.mem_nearStairAltF_iff,AltRotBase.nearP,AltRotBase.boxP,mem_nsAlt]
  omega

private theorem base_head (k : ℕ) (P Q H J : PartialOdometer) (hp : PaperBaseCond (twos k) P Q)
    (ha : PaperAltBaseCond (twos k) H J) :
    P.dom = oddTile (twos k) ∧ H.dom = altOddT (twos k) ∧
    ∀ x ∈ H.dom, H.val x = paperNearStairAltValue (den k) (x+(0,1)) := by
  have spec : (P.dom = nstairN (den k)) ∧ (∀ x, x ∈ H.dom ↔ x+(0,1) ∈ paperNearStairAltTile (den k)) ∧
      ∀ x ∈ H.dom, H.val x = paperNearStairAltValue (den k) (x+(0,1)) := by
    cases k with
    | zero => exact ⟨(hp.1 rfl).1,(ha.1 rfl).1,(ha.1 rfl).2.1⟩
    | succ k => exact ⟨(hp.2.2 _ (by omega) rfl).1,(ha.2.2 _ (by omega) rfl).1,(ha.2.2 _ (by omega) rfl).2.1⟩
  refine ⟨spec.1.trans (SiteBase.oddTile_rep_two _).symm,?_,spec.2.2⟩
  ext z
  exact (spec.2.1 z).trans (dom_head k z).symm

private abbrev L (f : Word → JSlice) (k : ℕ) (s : Bool) := (f (twos (k+1))).lEven s false
private abbrev H (f : Word → JSlice) (k : ℕ) := (f (twos k)).aOdd
private abbrev exitWord (k : ℕ) := twos (k+1) ++ [Digit.three]
private abbrev pieces (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).lEven) w

private theorem heads (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hg : GoodBelow D f (exitWord k).length) (s : Bool) :
    (L f k s).dom = evenLCells (twos (k+1)) s false ∧
    ∃ c : ℤ, ∀ z : Site, z-top s+(0,1) ∈ paperNearStairAltTile (den k) →
      ¬(z-top s+(0,1) ∈ paperNearStairAltA (den k) ∧ z-foot (den k) s ∈ nstairN (den k)) →
      (L f k s).val z = paperNearStairAltValue (den k) (z-top s+(0,1)) + dotS (1,-1) z + c := by
  let t := twos k
  let v := twos (k+1)
  have lt : t.length < v.length := by simp [t,v,twos]
  have lv : v.length < (exitWord k).length := by simp [exitWord,v,twos]
  have hJ := (hg t (lt_trans lt lv)).1
  have hb := AltRotStep.isBase_replicate_two k
  obtain ⟨eo,ee,ao,ae⟩ := hJ.2.2.1.1 hb
  have emp := hJ.1.2.2.1 hb
  have emb := hJ.2.1.2.2.1 hb
  rw [hS] at emp
  rw [hA] at emb
  have sp : PaperBaseCond t (f t).tOdd (f t).tEven := by rwa [eo,ee]
  have sa : PaperAltBaseCond t (f t).aOdd (f t).aEven := by rwa [ao,ae]
  obtain ⟨pd,ad,height⟩ := base_head k _ _ _ _ sp sa
  have defv : EvenLDefined v := ⟨twos k,.two,0,by decide,by simp [v,twos,List.replicate_succ']⟩
  have hl := ((hg v lv).1.2.2.2.2 s false defv).1
  have hs := short_description k s D.S (fun u => (below f v u).tOdd) (fun u => (below f v u).tEven)
    (fun u => (below f v u).aOdd) (fun u => (below f v u).aEven)
  dsimp only at hs
  have bt : below f v (twos k) = f t := below_of_lt _ _ _ lt
  rw [bt] at hs
  have md := hs.2 pd ad (by rw [hS]; rfl)
  obtain ⟨b,hb'⟩ := hl.2 _ hs.1
  refine ⟨hl.1.trans md, b, fun z hz he => ?_⟩
  have mem : z-top s ∈ (f t).aOdd.dom := ad ▸ (dom_head k _).2 hz
  have mp : z ∈ (headPiece (den k) s (f t).tOdd.dom (f t).aOdd).placed := JointRot.mem_placed.mpr mem
  have ex : z ∉ (headPiece (den k) s (f t).tOdd.dom (f t).aOdd).exc := by
    change ¬(_ ∧ _ ∈ (f t).tOdd.dom)
    rwa [pd,SiteBase.oddTile_rep_two]
  have eq := hb' z mp ex
  change (L f k s).val z = (f t).aOdd.val (z-top s) + dotS (1,-1) z + b at eq
  rwa [height _ mem] at eq

private abbrev u (d : ℤ) : Site := (d+2,d)
private abbrev b (d : ℤ) : Site := (d,2*d-1)
private abbrev ap (k : ℕ) : Site := ((k:ℤ)+1,-((k:ℤ)+2))

private theorem outer (D : JointData) (f : Word → JSlice) (k : ℕ) :
    (pieces D f (exitWord k))[3]? = some (stdPiece (L f k true) (u (den k)) 0) ∧
    (pieces D f (exitWord k))[4]? = some (stdPiece (L f k false) (b (den k)) (ap k)) := by
  let v := twos (k+1)
  let w := exitWord k
  have ho : W1Odd w = false := by simp [w,exitWord,twos,W1Odd,phase,List.count_replicate]
  have last : w.getLast? = some Digit.three := by simp [w,exitWord]
  have drop : w.dropLast = v := by simp [w,exitWord,v]
  have lt : v.length < w.length := by simp [w,v,exitWord]
  have p : (parentsAt w).odd = ⟨(k : ℤ)+1,(k : ℤ)+2⟩ := by
    change (parentsAt (v++[.three])).odd = _
    rw [parentsAt_append_singleton]; change (parentsAt v).odd = _
    simp [v,twos,parents_two,add_assoc]
  have q : (parentsAt w).even = ⟨2*((k+1 : ℕ) : ℤ)+1,2*((k+1 : ℕ) : ℤ)+3⟩ := by
    change (parentsAt (v++[.three])).even = _
    rw [parentsAt_append_singleton]; exact cur_even_two (k+1)
  have uq : vQ1 w = u (den k) := by ext <;> simp [vQ1,q,texV1Even,den] <;> ring
  have bp : vP1 w + vP2 w = b (den k) := by ext <;> simp [vP1,vP2,p,texV1Odd,texV2,den] <;> ring
  change (pieces D f w)[3]? = _ ∧ (pieces D f w)[4]? = _
  simp [pieces,tileOddPieces,ho,last,drop,p0Off,offsetP0,p0Aff,pairAffine,offsetA,p,bp,uq,below_of_lt f w v lt,L,v,ap]
  rfl

/-- The two ordinary L entries are compatible on their entire overlap at every positive pure-two exit. -/
theorem ordinary_L_pair (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (hg : GoodBelow D f (exitWord k).length) :
    PairCompat (pieces D f (exitWord k)) 3 4 ∧ PairCompat (pieces D f (exitWord k)) 4 3 := by
  let d := den k
  obtain ⟨hp,hm⟩ := outer D f k
  obtain ⟨dp,cp,vp⟩ := heads D hS hA f k hg true
  obtain ⟨dm,cm,vm⟩ := heads D hS hA f k hg false
  let zp : Site := (d+2,d+2)
  let zm : Site := (d+1,2*d+2)
  have plus (z : Site) : z-u d-top true = z-zp := by ext <;> simp [u,top,zp]; ring
  have minus (z : Site) : z-b d-top false = z-zm := by ext <;> simp [b,top,zm] <;> ring
  have pair : PairCompat (pieces D f (exitWord k)) 3 4 := by
    intro p q ep eq
    rw [hp,Option.some.injEq] at ep; subst p
    rw [hm,Option.some.injEq] at eq; subst q
    refine ⟨dotS (ap k) (((0,1) : Site)-zp) + ((k:ℤ)+2)^2 + dotS (1,-1) (b d-u d) + cp-cm, ?_⟩
    intro z h₁ h₂ _ _
    have μp : z ∈ shift (evenLCells (twos (k+1)) true false) (u d) := by
      change z ∈ shift (L f k true).dom (u d) at h₁
      rwa [dp] at h₁
    have μm : z ∈ shift (evenLCells (twos (k+1)) false false) (b d) := by
      change z ∈ shift (L f k false).dom (b d) at h₂
      rwa [dm] at h₂
    obtain ⟨⟨ph,pe⟩,⟨mh,me⟩⟩ := CorrectedCellsNear.common_heads k z μp μm
    change z-zp+(0,1) ∈ paperNearStairAltTile d at ph
    change z-zm+(0,1) ∈ paperNearStairAltTile d at mh
    have v₁ := vp (z-u d) (by rw [plus];exact ph) (by
      rw [plus,sub_sub]; exact pe)
    have v₂ := vm (z-b d) (by rw [minus];exact mh) (by
      rw [minus,sub_sub]; exact me)
    rw [plus] at v₁
    rw [minus] at v₂
    obtain ⟨x,y⟩ := z
    let xx := x-(d+2)
    let yy := y-(d+2)+1
    have sp : (x,y)-zp+((0,1):Site) = (xx,yy) := by ext <;> simp [zp,xx,yy]
    have sm : (x,y)-zm+((0,1):Site) = (xx+1,yy-d) := by ext <;> simp [zm,xx,yy] <;> ring
    rw [sp] at ph v₁
    rw [sm] at mh v₂
    have vh := near_head_period (k:ℤ) xx yy (by omega) ph mh
    change (L f k true).val ((x,y)-u d) + dotS 0 (x,y) -
      ((L f k false).val ((x,y)-b d) + dotS (ap k) (x,y)) = _
    rw [v₁,v₂]
    simp only [dotS,Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,zero_mul,add_zero,
      u,b,zp,xx,yy] at vh ⊢
    linear_combination vh
  refine ⟨pair, fun q p eq ep => ?_⟩
  obtain ⟨c,h⟩ := pair p q ep eq
  exact ⟨-c, fun x hq hp eq ep => by have := h x hp hq ep eq; omega⟩

end FLatticePaper.Tiles.LHeadCompatNear
