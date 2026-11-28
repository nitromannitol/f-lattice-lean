import FLatticePaper.Tiles.LStepAssembly
import FLatticePaper.Tiles.TileCompatInputs

/-! The short correction inherits the elongated correction's boundary values
on the part of each string that the short domain retains. -/

namespace FLatticePaper.Tiles.LRetainedSides

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles
open JointFamily JointInduction JointGlue LStepAssembly SiteStrings

private theorem heads_sub (stem : List Piece) (head : ℕ → Piece) (n : ℕ) :
    stem ++ (List.range (n-1)).map head ⊆ stem ++ (List.range n).map head := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_left _ h
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr
      (Nat.lt_of_lt_of_le (List.mem_range.mp hj) (Nat.sub_le _ _)),rfl⟩)

private theorem extension (ps qs : List Piece) (o o' : PartialOdometer)
    (h : RespectsPieces o ps) (h' : RespectsPieces o' qs) (sub : ps ⊆ qs)
    (cover : PiecesCovered ps) (conn : (overlapGraph (goodPart ps)).Connected) :
    ∃ k : ℤ, ∀ x ∈ o.dom, x ∈ o'.dom ∧ o.val x = o'.val x + k := by
  let values (i : Fin ps.length) (x : UnionPt ps) := pieceVal (ps.get i) x.val
  have localAgreement (O : PartialOdometer) (pieces : List Piece)
      (hO : RespectsPieces O pieces) (inc : ps ⊆ pieces) :
      ∀ i, CompatibleWith (fun x : UnionPt ps => O.val x.val) (goodPart ps i) (values i) := by
    intro i
    obtain ⟨b,hb⟩ := hO.2 _ (inc (List.get_mem ps i))
    refine ⟨b, fun x hx => ?_⟩
    have H := hb x.val hx.1 hx.2
    change O.val x.val - pieceVal (ps.get i) x.val = b
    unfold pieceVal
    omega
  have cover' (x : UnionPt ps) : ∃ i, x ∈ goodPart ps i := by
    obtain ⟨j,p,hj,hx,he⟩ := cover x.val x.property
    obtain ⟨hlt,rfl⟩ := List.getElem?_eq_some_iff.mp hj
    exact ⟨⟨j,hlt⟩, hx,he⟩
  obtain ⟨k,hk⟩ := compatible_unique _ values cover' conn (localAgreement o ps h (fun _ h => h))
    (localAgreement o' qs h' sub)
  refine ⟨k, fun x hx => ?_⟩
  have hu : x ∈ pieceUnion ps := h.1 ▸ hx
  obtain ⟨p,hp,hx'⟩ := mem_pieceUnion.mp hu
  exact ⟨h'.1.symm ▸ mem_pieceUnion.mpr ⟨p,sub hp,hx'⟩, hk ⟨x,hu⟩⟩

private theorem retained (short long tile : PartialOdometer) (wh wv : BinaryWord) (sides : List Side)
    (he : ∃ k : ℤ, ∀ x ∈ short.dom, x ∈ long.dom ∧ short.val x = long.val x + k)
    (hs : LSidesAgree long tile wh wv sides) :
    ∃ c : ℤ, ∀ s ∈ sides, ∀ x ∈ placedSites (sideString wh wv 0 s), x ∈ short.dom →
      x ∈ tile.dom ∧ short.val x = tile.val x + c := by
  obtain ⟨k,hk⟩ := he
  obtain ⟨b,hb⟩ := hs.2
  refine ⟨b+k, fun s h₁ x h₂ hx => ?_⟩
  obtain ⟨_,ht,eq⟩ := hb s h₁ x h₂
  exact ⟨ht, by rw [(hk x hx).2,eq,add_assoc]⟩

/-- The ordinary odd correction and the tile have one height difference on the portions
of both designated strings lying in the ordinary domain. -/
theorem odd_retained (D : JointData) (f : Word → JSlice) (w : Word) (plus : Bool) (hw : OddLDefined w)
    (h : IsJointSlice D f w) (conn : (overlapGraph (goodPart (oddPs D f w plus false))).Connected) :
    ∃ c : ℤ, ∀ s ∈ D.lSides true (W1Odd w) plus true,
      ∀ x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 s), x ∈ ((f w).lOdd plus false).dom →
        x ∈ (f w).tOdd.dom ∧ ((f w).lOdd plus false).val x = (f w).tOdd.val x + c := by
  have hs := h.2.2.2.1 plus false hw
  have hl := h.2.2.2.1 plus true hw
  apply retained _ _ _ _ _ _ _ hl.2
  apply extension (oddPs D f w plus false) (oddPs D f w plus true) _ _ hs.1 hl.1
    _ (oddLPieces_covered _ _ _ _ _ _ _ _) conn
  unfold oddPs oddLPieces
  simp only [Bool.false_eq_true, if_false, if_true, Nat.sub_zero]
  exact heads_sub _ _ _

/-- The ordinary even correction and the tile have one height difference on the portions
of both designated strings lying in the ordinary domain, including the pure-two bridge. -/
theorem even_retained (D : JointData) (f : Word → JSlice) (w : Word) (plus : Bool) (hw : EvenLDefined w)
    (h : IsJointSlice D f w) (conn : (overlapGraph (goodPart (evenPs D f w plus false))).Connected) :
    ∃ c : ℤ, ∀ s ∈ D.lSides false (W1Odd w) plus true,
      ∀ x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 s), x ∈ ((f w).lEven plus false).dom →
        x ∈ (f w).tEven.dom ∧ ((f w).lEven plus false).val x = (f w).tEven.val x + c := by
  have hs := h.2.2.2.2 plus false hw
  have hl := h.2.2.2.2 plus true hw
  apply retained _ _ _ _ _ _ _ hl.2
  apply extension (evenPs D f w plus false) (evenPs D f w plus true) _ _ hs.1 hl.1
    _ (evenLPieces_covered _ _ _ _ _ _ _ _) conn
  unfold evenPs evenLPieces
  simp only [Bool.false_eq_true, if_false, if_true, Nat.sub_zero]
  exact heads_sub _ _ _

/-- In an enclosing decomposition the retained part of an L has the same comparison
with a full copy as the original standard parent, up to the common change of constant. -/
theorem pair_on_retained (L T : PartialOdometer) (p a : Site) (q : Piece) (wh wv : BinaryWord) (sides : List Side)
    (hr : ∃ c : ℤ, ∀ s ∈ sides, ∀ x ∈ placedSites (sideString wh wv 0 s), x ∈ L.dom →
        x ∈ T.dom ∧ L.val x = T.val x + c)
    (full : TileCompatInputs.PairCompat [stdPiece T p a,q] 0 1) :
    ∃ k : ℤ, ∀ x ∈ (stdPiece L p a).placed, x ∈ q.placed → x ∉ q.exc →
      (∃ s ∈ sides, x-p ∈ placedSites (sideString wh wv 0 s)) →
      pieceVal (stdPiece L p a) x - pieceVal q x = k := by
  obtain ⟨c,hc⟩ := hr
  obtain ⟨b,hb⟩ := full _ _ rfl rfl
  refine ⟨b+c, fun x hL hq he hw => ?_⟩
  obtain ⟨s,hs,hx⟩ := hw
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hL
  change y ∈ L.dom at hy
  have ep : (y+p)-p = y := add_sub_cancel_right _ _
  change y+p-p ∈ placedSites (sideString wh wv 0 s) at hx
  rw [ep] at hx
  obtain ⟨ht,eq⟩ := hc s hs y hx hy
  have hstd : y+p ∈ (stdPiece T p a).placed := Finset.mem_image.mpr ⟨y,ht,rfl⟩
  have h := hb (y+p) hstd hq (by simp [stdPiece]) he
  change T.val ((y+p)-p) + dotS a (y+p) - pieceVal q (y+p) = b at h
  change L.val ((y+p)-p) + dotS a (y+p) - pieceVal q (y+p) = b+c
  rw [ep] at h ⊢
  omega

/-- The exact local comparison when the entire overlap with this full piece lies on the retained strings. -/
theorem pair_of_retained (ps : List Piece) (i j : ℕ) (L T : PartialOdometer) (p a : Site) (q : Piece)
    (wh wv : BinaryWord) (sides : List Side)
    (hi : ps[i]? = some (stdPiece L p a)) (hj : ps[j]? = some q)
    (hr : ∃ c : ℤ, ∀ s ∈ sides, ∀ x ∈ placedSites (sideString wh wv 0 s), x ∈ L.dom →
        x ∈ T.dom ∧ L.val x = T.val x + c)
    (full : TileCompatInputs.PairCompat [stdPiece T p a,q] 0 1)
    (covered : ∀ x ∈ (stdPiece L p a).placed, x ∈ q.placed → x ∉ q.exc →
        ∃ s ∈ sides, x-p ∈ placedSites (sideString wh wv 0 s)) :
    TileCompatInputs.PairCompat ps i j := by
  intro u v hu hv
  obtain rfl := Option.some.inj (hu.symm.trans hi)
  obtain rfl := Option.some.inj (hv.symm.trans hj)
  obtain ⟨k,hk⟩ := pair_on_retained L T p a _ wh wv sides hr full
  exact ⟨k, fun x hx hy _ he => hk x hx hy he (covered x hx hy he)⟩

end FLatticePaper.Tiles.LRetainedSides
