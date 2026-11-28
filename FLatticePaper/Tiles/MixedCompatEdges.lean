import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.HBottom

/-! On the bottom walk of a horizontal boundary word each vertex is on a zero
of the local odometer. The half-turn gives the affine values on the top walk, and the quarter turn
gives the height correction on the vertical walks. -/

namespace FLatticePaper.Tiles.MixedCompatEdges

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.HBottom
open FLatticePaper.Tiles.HorizontalStepOne FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings

private def zeroAt (t : ZTile) (x : GInt) : Prop := x ∈ tileShape t ∧ zTileOdo t x = 0

private instance (t : ZTile) (x : GInt) : Decidable (zeroAt t x) := by
  unfold zeroAt
  infer_instance

private theorem pair_zero (a b : ZTile) (hab : ValidPair a b) (x : GInt)
    (hx : x ∈ F2Word.walk (anchorOff a) (gPair a b)) : zeroAt a x ∨ zeroAt b (x - incr b) := by
  have check : ∀ a b : ZTile, ValidPair a b →
      ∀ x ∈ F2Word.walk (anchorOff a) (gPair a b), zeroAt a x ∨ zeroAt b (x - incr b) := by
    intro t t' h
    cases t <;> cases t' <;> first | exact (h (by decide)).elim | decide
  exact check a b hab x hx

private theorem aux_head (pr : Option Letter) (a : Letter) (rest : BinaryWord) (c : GInt) :
    (zTileOf pr a, c) ∈ hAuxG fwdStr pr (a :: rest) c := by
  have eq : tileFor pr a = zTileOf pr a := by rcases pr with _ | ⟨_ | _⟩ <;> cases a <;> rfl
  rw [← eq]
  cases rest <;> exact List.mem_cons_self

private theorem chain_zero (ls : BinaryWord) : ∀ (pr : Option Letter) (a : Letter) (c : GInt),
    (a :: ls).getLast? = some .p →
    ∀ x ∈ F2Word.walk (c + anchorOff (zTileOf pr a))
        (chainOf (zTileOf pr a :: tileSeqAux (some a) ls) ++ [Unit4.one]),
      ∃ t ∈ hAuxG fwdStr pr (a :: ls) c, zeroAt t.1 (x - t.2) := by
  induction ls with
  | nil =>
    intro pr a c hp x hx
    have ha : a = .p := by simpa using hp
    subst a
    have he : chainOf (zTileOf pr .p :: tileSeqAux (some .p) []) = [] := rfl
    rw [he, List.nil_append, walk_shift, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨(zTileOf pr .p, c), aux_head pr .p [] c, ?_⟩
    simp only [add_sub_cancel_left]
    have h : ∀ y ∈ F2Word.walk (anchorOff .zero) [Unit4.one], zeroAt .zero y := by decide
    exact h u hu
  | cons b ls ih =>
    intro pr a c hp x hx
    have hp' : (b :: ls).getLast? = some .p := by simpa using hp
    have hstep : fwdStr.step a b = incr (zTileOf (some a) b) := by cases a <;> cases b <;> rfl
    rw [HBottom.tileSeqAux_cons (some a) b ls, chainOf_cons_cons, List.append_assoc,
      WalkDecomp.walk_append, List.mem_append] at hx
    have hv := validPair_zTileOf pr a b
    rcases hx with here | later
    · rw [walk_shift, List.mem_map] at here
      obtain ⟨u, hu, rfl⟩ := here
      rcases pair_zero _ _ hv u hu with h | h
      · exact ⟨_, aux_head pr a (b :: ls) c, by simpa using h⟩
      · refine ⟨(zTileOf (some a) b, c + fwdStr.step a b),
          List.mem_cons_of_mem _ (aux_head (some a) b ls _), ?_⟩
        simpa [hstep] using h
    · have he : c + anchorOff (zTileOf pr a) + F2Word.sum (gPair (zTileOf pr a) (zTileOf (some a) b)) =
          (c + fwdStr.step a b) + anchorOff (zTileOf (some a) b) := by rw [sum_gPair _ _ hv, hstep]; abel
      rw [he] at later
      obtain ⟨t, ht, hz⟩ := ih (some a) b (c + fwdStr.step a b) hp' x (List.mem_of_mem_tail later)
      exact ⟨t, List.mem_cons_of_mem _ ht, hz⟩

private theorem walk_zero (w : BinaryWord) (hp : w.getLast? = some .p) (x : GInt)
    (hx : x ∈ F2Word.walk 0 (gH w)) : ∃ t ∈ hStringAt w 0, zeroAt t.1 (x - t.2) := by
  cases w with
  | nil => simp at hp
  | cons a ls =>
    have ha : (0 : GInt) + anchorOff (zTileOf none a) = 0 := by cases a <;> rfl
    rw [gH_unfold, tileSeq, HBottom.tileSeqAux_cons] at hx
    rw [hStringAt_eq]
    exact chain_zero ls none a 0 hp x (ha.symm ▸ hx)

/-- The height on every vertex of the bottom walk equals the constant of the first tile. -/
theorem bottom (o : PartialOdometer) (w : BinaryWord) (hq : w.head? = some .q) (hp : w.getLast? = some .p)
    (hR : RespectsTiles .horizontal false (hStringAt w 0) o.val)
    (β : ℤ) (hN : FirstTileNormal o 0 β) :
    ∀ x ∈ F2Word.walk 0 (gH w), o.val x = β := by
  obtain ⟨α, K, hf⟩ := horizontal_formula w 0 o.val hR
  obtain ⟨ls, rfl⟩ : ∃ ls, w = .q :: ls := by
    cases w with
    | nil => simp at hq
    | cons a ls => simp only [List.head?_cons, Option.some.injEq] at hq; exact ⟨ls, by rw [hq]⟩
  let ts := hStringAt (.q :: ls) 0
  have hfirst : ts.getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    dsimp [ts]; rw [hStringAt_eq, hAuxG_head]; rfl
  have hlen : 0 < ts.length := by dsimp [ts]; rw [hStringAt_eq]; cases ls <;> simp [hAuxG]
  have hN' : FirstTileNormal o α K := by
    intro x hx
    have h := hf 0 hlen x (by rw [mem_dom_iff, famOf_tile, hfirst]; simpa using hx)
    rw [hfirst] at h
    refine ⟨(hN x hx).1, ?_⟩
    dsimp [normed, dotS, ptDot] at h ⊢
    simp only [sub_zero] at h
    linarith
  obtain ⟨rfl, rfl⟩ := WeakStepAssembly.normal_unique o α 0 K β hN' hN
  intro x hx
  obtain ⟨t, ht, hz, hv⟩ := walk_zero _ hp x hx
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 ht
  have H : ts.getD k (ZTile.zero, 0) = t := by simp [ts, List.getD_eq_getElem?_getD, hk, he]
  have := hf k hk x (by rw [mem_dom_iff, famOf_tile, H]; exact hz)
  rw [H, hv] at this
  simpa [ptDot] using this

private theorem h0_rot (z : GInt) : h0 (mulI z - ((0, 1) : GInt)) = -h0 z := by
  have h := FLatticePaper.Construction.four_mul_centeredQuarterTurnCorrection (mulI z - (0, 1))
  have h' := FLatticePaper.Construction.four_mul_centeredQuarterTurnCorrection z
  have hp : ((mulI z - ((0, 1) : GInt)).1 + (mulI z - ((0, 1) : GInt)).2) % 2 =
      1 - (z.1 + z.2) % 2 := by simp [mulI]; omega
  rw [hp] at h
  simp only [mulI, Prod.fst_sub, Prod.snd_sub, sub_zero] at h
  simp only [h0, mulI]
  nlinarith only [h, h']

private theorem h0_flip (x : GInt) : h0 (((1, -1) : GInt) - x) = h0 x := by
  have h := FLatticePaper.Construction.four_mul_centeredQuarterTurnCorrection (((1,-1) : GInt) - x)
  have h' := FLatticePaper.Construction.four_mul_centeredQuarterTurnCorrection x
  have hp : (((1,-1) - x).1 + ((1,-1) - x).2) % 2 = (x.1 + x.2) % 2 := by
    simp only [Prod.fst_sub, Prod.snd_sub]; omega
  rw [hp] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  unfold h0
  nlinarith only [h, h']

/-- Four sides obtained from two sets of bottom points by the half turn and the quarter turn. -/
def onSide (S SR : GInt → Prop) (X Y : GInt) (s : Side) (z : GInt) : Prop :=
  match s with
  | .hPlus => S z
  | .hMinus => S (X + Y + ((1,-1) : GInt) - z)
  | .vPlus => ∃ y, SR y ∧ z = mulI y + (X - (0,1))
  | .vMinus => ∃ y, SR y ∧ X + Y + ((1,-1) : GInt) - z = mulI y + (X - (0,1))

/-- The four boundary walks, with the right walk obtained by turning the bottom walk of the rotated tile. -/
def edge (w wr : BinaryWord) (X Y : GInt) (s : Side) (z : GInt) : Prop :=
  onSide (fun y => y ∈ F2Word.walk 0 (gH w)) (fun y => y ∈ F2Word.walk 0 (gH wr)) X Y s z

/-- The function to subtract from the odometer on each walk. -/
def edgeHeight (X a : GInt) (s : Side) (z : GInt) : ℤ :=
  match s with
  | .hPlus => 0
  | .hMinus => dotS a z
  | .vPlus => -h0 (z-X)
  | .vMinus => -h0 z

/-- Transport constant bottom heights on two sets of sites to their four sides. -/
theorem four_traces (o oR : PartialOdometer) (S SR : GInt → Prop) (X : GInt) (n d β βr : ℤ)
    (hβ : FirstTileNormal o 0 β) (hβr : FirstTileNormal oR 0 βr)
    (bot : ∀ z, S z → o.val z = β) (botR : ∀ z, SR z → oR.val z = βr)
    (inside : ∀ z, SR z → z ∈ oR.dom)
    (hf : TileHalfTurn o X (n-d,n+d) (n,-d)) (hr : TileRotation o oR X) (s : Side) :
    ∃ k : ℤ, ∀ z ∈ o.dom, onSide S SR X (n-d,n+d) s z →
      o.val z - edgeHeight X (n,-d) s z = k := by
  obtain ⟨α, β₀, hN, flip⟩ := hf
  obtain ⟨rfl, -⟩ := WeakStepAssembly.normal_unique o α 0 β₀ β hN hβ
  let Y : GInt := (n-d,n+d)
  let a : GInt := (n,-d)
  let D := X + Y + ((1,-1) : GInt)
  have F (z : GInt) (hd : z ∈ o.dom) :
      2 * (o.val (D-z) - o.val z) = dotS a D - 2 * dotS a z := by
    have H := (flip z hd).2
    simpa [D, Y, a, normed, dotS, mul_sub] using H
  obtain ⟨K, R⟩ := JointRot.rawRot_of_tileRotation_slopes o oR X hr ⟨β,hβ⟩ ⟨βr,hβr⟩
  have right (z : GInt) (he : onSide S SR X Y .vPlus z) : o.val z + h0 (z-X) = βr-K := by
    obtain ⟨y, hy, rfl⟩ := he
    have hv := (R y (inside y hy)).2
    have e : mulI y + (X - (0, 1)) - X = mulI y - (0, 1) := by abel
    rw [e, h0_rot]
    simp [dotS] at hv
    linarith [botR y hy]
  have ev : FLatticePaper.EvenSite Y := by change ((n-d)+(n+d)) % 2 = 0; omega
  have ha : JointRot.hHalf Y = a := by dsimp [Y, a, JointRot.hHalf]; ext <;> simp <;> omega
  have shift (z : GInt) : h0 (D-z-X) = h0 z + dotS a z - dotS a Y +
      FLatticePaper.Construction.centeredQuarterTurnCorrection Y := by
    have e : D-z-X = ((1,-1) : GInt) - (z-Y) := by dsimp [D]; abel
    rw [e, h0_flip]
    have h := JointRot.h0_sub z Y ev
    rw [ha] at h
    linarith
  -- Comparing any two sites avoids dividing the half-turn constant.
  classical
  by_cases h : ∃ z ∈ o.dom, onSide S SR X Y s z
  · obtain ⟨z₀, h₀, e₀⟩ := h
    refine ⟨o.val z₀ - edgeHeight X a s z₀, fun z hD he => ?_⟩
    cases s with
    | hPlus =>
      change o.val z - 0 = o.val z₀ - 0
      rw [bot z he, bot z₀ e₀]
    | hMinus =>
      change o.val z - dotS a z = o.val z₀ - dotS a z₀
      linarith only [F z hD, F z₀ h₀, bot (D-z) he, bot (D-z₀) e₀]
    | vPlus =>
      change o.val z - -h0 (z-X) = o.val z₀ - -h0 (z₀-X)
      simpa only [sub_neg_eq_add] using (right z he).trans (right z₀ e₀).symm
    | vMinus =>
      change o.val z - -h0 z = o.val z₀ - -h0 z₀
      linarith only [F z hD, F z₀ h₀, right (D-z) he, right (D-z₀) e₀, shift z, shift z₀]
  · exact ⟨0, fun z hd he => (h ⟨z,hd,he⟩).elim⟩

/-- The normalized height on each entire walk of a standard parent. -/
theorem four_edges (o oR : PartialOdometer) (w v wr vr : BinaryWord) (X : GInt) (n d : ℤ)
    (hh : w.head? = some .q) (ht : w.getLast? = some .p)
    (hhr : wr.head? = some .q) (htr : wr.getLast? = some .p)
    (ho : RespectsAnchored o.dom w v o.val) (hor : RespectsAnchored oR.dom wr vr oR.val)
    (hz : JointRot.SlopeZero o) (hzr : JointRot.SlopeZero oR)
    (hf : TileHalfTurn o X (n-d,n+d) (n,-d)) (hr : TileRotation o oR X) (s : Side) :
    ∃ k : ℤ, ∀ z ∈ o.dom, edge w wr X (n-d,n+d) s z →
      o.val z - edgeHeight X (n,-d) s z = k := by
  obtain ⟨β,hβ⟩ := hz
  obtain ⟨βr,hβr⟩ := hzr
  apply four_traces o oR _ _ X n d β βr hβ hβr
    (bottom o w hh ht ho.2.1 β hβ) (bottom oR wr hhr htr hor.2.1 βr hβr) _ hf hr s
  intro y hy
  obtain ⟨t, ht', hmem, -⟩ := walk_zero wr htr y hy
  have h := WeakStepPaper.side_inside oR.dom wr vr oR.val hor .hPlus t ht' (y-t.2) hmem
  simpa using h

end FLatticePaper.Tiles.MixedCompatEdges
