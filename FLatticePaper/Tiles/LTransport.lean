import FLatticePaper.Tiles.JointGlue

/-! # Pieces translated from a respected decomposition

If an odometer `o` respects a decomposition, a piece with the same odometer as one of its pieces, placed at the offset translated
by `t` and with the affine factor increased by `Δa`, is `o(· - t) + Δaᵀ·` up to a constant on its placed domain (`transport_val`).
Pieces translated by the same `t` and `Δa` from pieces of one respected decomposition therefore agree with constants on their
overlaps (`transport_agree`): the pairs and the triangle of the L-corrected decompositions that occur in the alternate
decompositions of the prefix. -/

namespace FLatticePaper.Tiles.LTransport

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal)

theorem mem_placed_sub (p : Piece) (t y : Site) :
    y ∈ { p with off := p.off + t }.placed ↔ y - t ∈ p.placed := by
  simp only [Piece.placed, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by abel⟩
  · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, by rw [← add_assoc, hxy]; abel⟩

/-- **A translated piece.** -/
theorem transport_val (o : PartialOdometer) (ps : List Piece) (hR : RespectsPieces o ps) (p : Piece) (hp : p ∈ ps)
    (hexc : p.exc = ∅) (t da : Site) :
    ∃ c : ℤ, ∀ y, y - t ∈ p.placed →
      pieceVal { p with off := p.off + t, aff := p.aff + da } y + c = o.val (y - t) + dotS da y := by
  obtain ⟨b, hb⟩ := hR.2 p hp
  refine ⟨b - dotS p.aff t, fun y hy => ?_⟩
  have e := hb (y - t) hy (by rw [hexc]; exact Set.notMem_empty _)
  have e2 : y - (p.off + t) = y - t - p.off := by abel
  simp only [pieceVal, e2]
  rw [e]
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Translated pieces agree.** Two pieces of a respected decomposition (with no exceptional points), translated by the same
`t` with the same increase `Δa` of the affine factor, agree with constants on the overlap of the translates. -/
theorem transport_agree (o : PartialOdometer) (ps : List Piece) (hR : RespectsPieces o ps) (p q : Piece) (hp : p ∈ ps)
    (hq : q ∈ ps) (hpe : p.exc = ∅) (hqe : q.exc = ∅) (t da : Site) :
    ∃ cp cq : ℤ, ∀ y, y - t ∈ p.placed → y - t ∈ q.placed →
      pieceVal { p with off := p.off + t, aff := p.aff + da } y + cp =
        pieceVal { q with off := q.off + t, aff := q.aff + da } y + cq := by
  obtain ⟨cp, hcp⟩ := transport_val o ps hR p hp hpe t da
  obtain ⟨cq, hcq⟩ := transport_val o ps hR q hq hqe t da
  exact ⟨cp, cq, fun y h1 h2 => by rw [hcp y h1, hcq y h2]⟩

end FLatticePaper.Tiles.LTransport
