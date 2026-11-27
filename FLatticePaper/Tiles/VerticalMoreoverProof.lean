import FLatticePaper.Tiles.VerticalCrossIdent

/-! # The vertical half of the Moreover, assembled

The forward family `vtP w` and the reversed family `vtM w` of `VerticalFamily` satisfy every clause of `VerticalMoreover`: their
`Respects` clauses (`PTFamily.respects_of_triples`), their within-family overlaps (`VerticalWithin`), their cross overlaps
(`VerticalCrossLocal` for the locality `j ∈ {k-1, k, k+1}` and `VerticalCrossIdent` for the three identities), and the equal first
affine factors `(0,0)`. -/

namespace FLatticePaper.Tiles

/-- The cross overlaps of the explicit vertical families agree. -/
theorem vt_cross_common (w : BinaryWord) (hw : IsAlmostPalindrome w) (hf : w.head? = some .p)
    (hl : w.getLast? = some .q) (hn : 2 ≤ w.length) : CrossCommon (vtP w) (vtM w) := by
  intro k hk j hj x hxP hxM
  have hk' : k < w.length := by simpa only [vtP_n] using hk
  have hj' : j < w.length := by simpa only [vtM_n] using hj
  rcases vt_cross_local w hw hf hl hn k j hk' hj' x hxP hxM with rfl | h | h
  · exact vt_cross_same w hw hf hl hn _ hk' x hxP hxM
  · obtain rfl : k = j + 1 := h.symm
    exact vt_cross_pred w hw hf hl hn j hk' x hxP hxM
  · obtain rfl : j = k + 1 := h.symm
    exact vt_cross_succ w hw hf hl hn k hj' x hxP hxM

/-- The vertical half of the Moreover of `lemma:stacked_zero_one_string`, for every word. -/
theorem verticalMoreover_proof (w : BinaryWord) : VerticalMoreover w := by
  unfold VerticalMoreover
  intro hw hf hl
  have hn : 2 ≤ w.length := by
    rcases w with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hf
    · simp_all
    · simp
  refine ⟨vtP w, vtM w, rfl, rfl, vtP_respects w, vtM_respects w, vtP_within w, vtM_within w,
    vt_cross_common w hw hf hl hn, ?_⟩
  simp [vtP, vtM, vtAff, vtCnt]

end FLatticePaper.Tiles
