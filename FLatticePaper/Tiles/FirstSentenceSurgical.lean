import FLatticePaper.Tiles.VerticalMoreoverProof
import FLatticePaper.Tiles.HorizontalEnlarged

/-! # The first sentence of `lemma:stacked_zero_one_string`, with the surgical slope table

For every orientation `o`, every `rev`, and every word `w`, there is a zero-one family `P` on the zero-one string of `w` (reversed
when `rev`), with the positions of that string, which respects it (`Respects o rev`, surgical table) and has common extensions
(`WithinCommon`). The families are the explicit ones: `HP w` and `vtP w` on the unshifted strings; `HM w` and `vtM w` on the
stacked strings, which are translated back to the unshifted positions (`PTFamily.translate`). -/

namespace FLatticePaper.Tiles

/-- The translate of a family by `s`: the tiles move by `s`, the affine factors are kept, and the constants absorb `a · s`, so
that `odo' k x = odo k (x - s)`. -/
def PTFamily.translate (F : PTFamily) (s : GInt) : PTFamily :=
  { ts := F.ts.map (fun p => (p.1, p.2 + s)), a := F.a, b := fun k => F.b k - ptDot (F.a k) s }

theorem PTFamily.translate_n (F : PTFamily) (s : GInt) : (F.translate s).n = F.n := by
  simp [PTFamily.n, PTFamily.translate]

theorem PTFamily.translate_tile (F : PTFamily) (s : GInt) (k : ℕ) (hk : k < F.n) :
    (F.translate s).tile k = ((F.tile k).1, (F.tile k).2 + s) := by
  unfold PTFamily.tile PTFamily.translate
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  have hk' : F.ts[k]? = some F.ts[k] := List.getElem?_eq_getElem (by simpa [PTFamily.n] using hk)
  rw [hk']
  rfl

theorem PTFamily.translate_odo (F : PTFamily) (s : GInt) (k : ℕ) (hk : k < F.n) (x : GInt) :
    (F.translate s).odo k x = F.odo k (x - s) := by
  unfold PTFamily.odo
  rw [PTFamily.translate_tile F s k hk]
  simp only [PTFamily.translate, ptDot, Prod.fst_sub, Prod.snd_sub]
  rw [show x - ((F.tile k).2 + s) = x - s - (F.tile k).2 by abel]
  ring

theorem PTFamily.translate_dom (F : PTFamily) (s : GInt) (k : ℕ) (hk : k < F.n) :
    (F.translate s).dom k = (F.dom k).map (· + s) := by
  unfold PTFamily.dom
  rw [PTFamily.translate_tile F s k hk]
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext x
  abel

theorem PTFamily.mem_translate_dom (F : PTFamily) (s : GInt) (k : ℕ) (hk : k < F.n) (x : GInt) :
    x ∈ (F.translate s).dom k ↔ x - s ∈ F.dom k := by
  rw [PTFamily.translate_dom F s k hk, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - s, hx, by abel⟩

/-- Translation preserves the respect of a family. -/
theorem PTFamily.translate_respects (F : PTFamily) (o : Orientation) (rev : Bool) (s : GInt)
    (h : F.Respects o rev) : (F.translate s).Respects o rev := by
  intro k hk
  rw [PTFamily.translate_n] at hk
  have hk' : k < F.n := by omega
  have hk1 : k + 1 < F.n := hk
  obtain ⟨hsl, hcl⟩ := h k hk
  refine ⟨?_, ?_⟩
  · rw [PTFamily.translate_tile F s k hk', PTFamily.translate_tile F s (k + 1) hk1]
    have e1 : (F.translate s).odo (k + 1) = fun x => F.odo (k + 1) (x - s) := funext (PTFamily.translate_odo F s (k + 1) hk1)
    have e0 : (F.translate s).odo k = fun x => F.odo k (x - s) := funext (PTFamily.translate_odo F s k hk')
    rw [e1, e0, PTFamily.translate_dom F s (k + 1) hk1, PTFamily.translate_dom F s k hk']
    rw [slopeOf_translate (F.odo (k + 1)) (F.dom (k + 1)) s, slopeOf_translate (F.odo k) (F.dom k) s]
    exact hsl
  · intro hno x hx y hy hu
    have hno' : ¬ ∃ z, z ∈ F.dom k ∧ z ∈ F.dom (k + 1) := by
      rintro ⟨z, h1, h2⟩
      apply hno
      refine ⟨z + s, ?_, ?_⟩
      · rw [PTFamily.mem_translate_dom F s k hk']
        simpa using h1
      · rw [PTFamily.mem_translate_dom F s (k + 1) hk1]
        simpa using h2
    have hx' : x - s ∈ F.dom k := (PTFamily.mem_translate_dom F s k hk' x).1 hx
    have hy' : y - s ∈ F.dom (k + 1) := (PTFamily.mem_translate_dom F s (k + 1) hk1 y).1 hy
    have hu' : unitApart (x - s) (y - s) := by
      unfold unitApart at hu ⊢
      simpa [Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using hu
    obtain ⟨hH, hV⟩ := hcl hno' (x - s) hx' (y - s) hy' hu'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have key := hH h
      rw [PTFamily.translate_odo F s k hk', PTFamily.translate_odo F s (k + 1) hk1]
      unfold ptDot at key ⊢
      simp only [Prod.fst_sub, Prod.snd_sub, PTFamily.translate] at key ⊢
      linarith
    · have key := hV h
      rw [PTFamily.translate_odo F s k hk', PTFamily.translate_odo F s (k + 1) hk1]
      unfold ptDot at key ⊢
      simp only [Prod.fst_sub, Prod.snd_sub, PTFamily.translate] at key ⊢
      linarith

/-- Translation preserves the common extension of a family. -/
theorem PTFamily.translate_within (F : PTFamily) (s : GInt) (h : WithinCommon F) :
    WithinCommon (F.translate s) := by
  intro k hk j hj x hxk hxj
  rw [PTFamily.translate_n] at hk hj
  rw [PTFamily.translate_odo F s k hk, PTFamily.translate_odo F s j hj]
  exact h k hk j hj (x - s) ((PTFamily.mem_translate_dom F s k hk x).1 hxk)
    ((PTFamily.mem_translate_dom F s j hj x).1 hxj)

/-- The tile type of a zero-one string of orientation `o` at position `k` of the letter sequence `ℓ`: the enlarged tile
after `qq` in a horizontal string (surgical lines 1293-1300, every horizontal string), the letter's tile in a vertical one. -/
def zoTileAt : Orientation → (ℕ → Letter) → ℕ → ZTile
  | .horizontal, ℓ, k => hTileAt ℓ k
  | .vertical, ℓ, k => letterZTile (ℓ k)

/-- The first sentence of `lemma:stacked_zero_one_string` for every orientation, reversal and word, with the surgical table and
the enlarged tiles of the horizontal strings. -/
theorem zeroOne_first_sentence_surgical (o : Orientation) (rev : Bool) (w : BinaryWord) :
    ∃ P : PTFamily, P.ts = (List.range w.length).map
        (fun k => (zoTileAt o (lettersOf w rev) k, posF o rev (lettersOf w rev) k)) ∧
      P.Respects o rev ∧ WithinCommon P := by
  cases o <;> cases rev
  · exact ⟨HPE w, rfl, HPE_respects w, HPE_within w⟩
  · refine ⟨(HME w).translate horizontalStackShift, ?_,
      PTFamily.translate_respects _ _ _ _ (HME_respects w), PTFamily.translate_within _ _ (HME_within w)⟩
    simp only [PTFamily.translate, HME, zoReversedStackedE, zoTileAt, List.map_map, Function.comp_def, sub_add_cancel]
  · exact ⟨vtP w, rfl, vtP_respects w, vtP_within w⟩
  · refine ⟨(vtM w).translate verticalStackShift, ?_,
      PTFamily.translate_respects _ _ _ _ (vtM_respects w), PTFamily.translate_within _ _ (vtM_within w)⟩
    simp only [PTFamily.translate, vtM, zoReversedStackedV, zoTileAt, List.map_map, Function.comp_def, sub_add_cancel]

end FLatticePaper.Tiles
