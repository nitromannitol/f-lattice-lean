import FLatticePaper.Tiles.JointGlue
import FLatticePaper.Tiles.AltGlueHalfTurn

/-! # The half-turn of an odometer glued from a decomposition

The argument of (b) in the proof of `lemma:tile-odometer-existence` (Cases 1-4). Let `o` respect a decomposition `ps` and `o'`
respect `ps'`, and let `y ↦ D - y` send each piece `i` of `ps` into the piece `σ i` of `ps'` so that the two placed odometers
satisfy `2(g'_{σ i}(D - y) - g_i(y)) = -2Eᵀy + M_i` (for copies of a parent with the half-turn identity this is
`AltGlueHalfTurn.piece_halfTurn`). Then `Ψ(y) = 2(o'(D - y) - o(y)) + 2Eᵀy` is constant on each piece; two overlapping pieces
have the same constant, so on a connected overlap graph `Ψ` is one constant `c` (`glue_halfTurn`). When `o' = o`, applying the
identity at `D - y` gives `c = EᵀD` (`glue_halfTurn_self`). -/

namespace FLatticePaper.Tiles.TileHalfTurnGlue

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal PiecesCovered goodPart)

/-- A function that agrees across the edges of a connected graph is constant. -/
theorem const_of_connected {V : Type*} {G : SimpleGraph V} (hc : G.Connected) (K : V → ℤ)
    (h : ∀ i j, G.Adj i j → K i = K j) (i j : V) : K i = K j := by
  obtain ⟨p⟩ := hc.preconnected i j
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

/-- **The half-turn of a glued odometer**, from the half-turn relations of the pieces and the connectivity of the overlap graph. -/
theorem glue_halfTurn (ps ps' : List Piece) (o o' : PartialOdometer) (hR : RespectsPieces o ps)
    (hR' : RespectsPieces o' ps') (hcov : PiecesCovered ps) (hconn : (overlapGraph (goodPart ps)).Connected)
    (σ : ℕ → ℕ) (D E : Site)
    (hpair : ∀ (i : ℕ) (p : Piece), ps[i]? = some p → ∃ q : Piece, ps'[σ i]? = some q ∧ ∃ M : ℤ, ∀ y ∈ p.placed, y ∉ p.exc →
      D - y ∈ q.placed ∧ D - y ∉ q.exc ∧ 2 * (pieceVal q (D - y) - pieceVal p y) = dotS (-(2 : ℤ) • E) y + M) :
    ∃ c : ℤ, ∀ y ∈ o.dom, D - y ∈ o'.dom ∧ 2 * (o'.val (D - y) - o.val y) = dotS (-(2 : ℤ) • E) y + c := by
  have key : ∀ i : Fin ps.length, ∃ K : ℤ, ∀ y ∈ (ps.get i).placed, y ∉ (ps.get i).exc →
      D - y ∈ o'.dom ∧ 2 * (o'.val (D - y) - o.val y) = dotS (-(2 : ℤ) • E) y + K := by
    intro i
    obtain ⟨q, hq, M, hrel⟩ := hpair i (ps.get i) (by simp)
    obtain ⟨b, hb⟩ := hR.2 _ (List.get_mem ps i)
    obtain ⟨b', hb'⟩ := hR'.2 q (List.mem_of_getElem? hq)
    refine ⟨M + 2 * (b' - b), fun y hy hye => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrel y hy hye
    have e1 := hb y hy hye
    have e2 := hb' (D - y) h1 h2
    refine ⟨?_, ?_⟩
    · rw [hR'.1]
      exact JointGlue.mem_pieceUnion.2 ⟨q, List.mem_of_getElem? hq, h1⟩
    · rw [e1, e2]
      simp only [pieceVal] at h3
      linarith
  choose K hK using key
  have hKeq : ∀ i j, (overlapGraph (goodPart ps)).Adj i j → K i = K j := by
    rintro i j ⟨-, ⟨y, hyi, hyj⟩⟩
    have a := (hK i y.1 hyi.1 hyi.2).2
    have b := (hK j y.1 hyj.1 hyj.2).2
    linarith
  obtain ⟨i0⟩ := hconn.nonempty
  refine ⟨K i0, fun y hy => ?_⟩
  have hy' : y ∈ pieceUnion ps := hR.1 ▸ hy
  obtain ⟨i, p, hp, hyp, hye⟩ := hcov y hy'
  have hi : i < ps.length := by
    rcases Nat.lt_or_ge i ps.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.2 h] at hp; cases hp
  have hpe : ps.get ⟨i, hi⟩ = p := by
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hp
    exact hp
  obtain ⟨h1, h2⟩ := hK ⟨i, hi⟩ y (hpe ▸ hyp) (hpe ▸ hye)
  rw [const_of_connected hconn K hKeq ⟨i, hi⟩ i0] at h2
  exact ⟨h1, h2⟩

/-- **The half-turn of a glued odometer onto itself**: with an involution of the pieces, the constant is `EᵀD`. -/
theorem glue_halfTurn_self (ps : List Piece) (o : PartialOdometer) (hR : RespectsPieces o ps) (hcov : PiecesCovered ps)
    (hconn : (overlapGraph (goodPart ps)).Connected) (σ : ℕ → ℕ) (D E : Site)
    (hpair : ∀ (i : ℕ) (p : Piece), ps[i]? = some p → ∃ q : Piece, ps[σ i]? = some q ∧ ∃ M : ℤ, ∀ y ∈ p.placed, y ∉ p.exc →
      D - y ∈ q.placed ∧ D - y ∉ q.exc ∧ 2 * (pieceVal q (D - y) - pieceVal p y) = dotS (-(2 : ℤ) • E) y + M)
    {y0 : Site} (hy0 : y0 ∈ o.dom) :
    ∀ y ∈ o.dom, D - y ∈ o.dom ∧ 2 * (o.val (D - y) - o.val y) = dotS E D - 2 * dotS E y := by
  obtain ⟨c, hc⟩ := glue_halfTurn ps ps o o hR hR hcov hconn σ D E hpair
  obtain ⟨h1, h2⟩ := hc y0 hy0
  obtain ⟨-, h3⟩ := hc (D - y0) h1
  rw [sub_sub_cancel] at h3
  have hcE : c = dotS E D := by
    simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at h2 h3 ⊢
    linarith
  intro y hy
  obtain ⟨g1, g2⟩ := hc y hy
  refine ⟨g1, ?_⟩
  rw [g2, hcE]
  simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The half-turn relation of two copies of one parent with the half-turn identity (`AltGlueHalfTurn.piece_halfTurn`), in the
form of `glue_halfTurn`. -/
theorem std_pair (T : PartialOdometer) (C a : Site)
    (HT : ∀ z ∈ T.dom, C - z ∈ T.dom ∧ 2 * (T.val (C - z) - T.val z) = dotS a C - 2 * dotS a z)
    (D off off' aff aff' E : Site) (hoff : off' = D - C - off) (haff : aff + aff' = E - a) :
    ∃ M : ℤ, ∀ y ∈ (stdPiece T off aff).placed, y ∉ (stdPiece T off aff).exc →
      D - y ∈ (stdPiece T off' aff').placed ∧ D - y ∉ (stdPiece T off' aff').exc ∧
      2 * (pieceVal (stdPiece T off' aff') (D - y) - pieceVal (stdPiece T off aff) y) = dotS (-(2 : ℤ) • E) y + M := by
  refine ⟨dotS a C + 2 * dotS a off + 2 * dotS aff' D, fun y hy _ => ?_⟩
  obtain ⟨h1, h2⟩ := AltGlueHalfTurn.piece_halfTurn T C a HT D off off' aff aff' E hoff haff y hy
  exact ⟨h1, by simp [stdPiece], h2⟩

end FLatticePaper.Tiles.TileHalfTurnGlue
