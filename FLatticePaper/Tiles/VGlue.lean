import FLatticePaper.Tiles.VJunction
import FLatticePaper.Tiles.HorizontalGlue

/-! Task 53, marksIn (vertical gluing): the vertical strings of a child word lie in the child tile.

The vertical blocks of a child word are `vert` of the blocks of the swapped child word; their junction offsets are `texV2` of the
rotated slopes (`VJunction.vert_jv_odd`, `vert_jv_even`). The pieces of `oddChildB` and `evenChildB` at the offsets `texV2 p` and
`texV2 q` are the registers `T1`, `T2` translated accordingly. The four lemmas are the four parity and tile cases. -/

namespace FLatticePaper.Tiles.VGlue

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.VJunction FLatticePaper.Tiles.HorizontalGlue FLatticePaper.Construction

/-- Every vertical site of the block `L` lies in `T`. -/
def HV (L : List Letter) (T : Tile) : Prop := ∀ z ∈ VS0 L, z ∈ T

theorem vjunction_gen (Y Z : List Letter) (hY : ∃ Y', Y = Letter.q :: Y') (hZ : ∃ Z', Z = Letter.q :: Z') :
    VS0 (Y ++ Z) = VS0 Y ++ (VS0 Z).map fun z => z + jv Y := by
  obtain ⟨Y', rfl⟩ := hY
  obtain ⟨Z', rfl⟩ := hZ
  exact vjunction Y' Z'

theorem mem_vjunction (Y Z : List Letter) (hY : ∃ Y', Y = Letter.q :: Y') (hZ : ∃ Z', Z = Letter.q :: Z')
    (z : ℤ × ℤ) : z ∈ VS0 (Y ++ Z) ↔ z ∈ VS0 Y ∨ ∃ w ∈ VS0 Z, w + jv Y = z := by
  rw [vjunction_gen Y Z hY hZ]
  simp only [List.mem_append, List.mem_map]

/-- The odd-count childQ of the odd tile: `vert qw ++ vert pw`, first block in `T1`, second at `texV2 p` in `T2`. -/
theorem glue_vB_true (Q' P' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hQ : HV (Letter.q :: Q') T1) (hP : HV (Letter.q :: P') T2) (hj : jv (Letter.q :: Q') = texV2 p) :
    HV ((Letter.q :: Q') ++ (Letter.q :: P')) (oddChildB true T1 T2 p q) := by
  intro z hz
  rcases (mem_vjunction (Letter.q :: Q') (Letter.q :: P') ⟨Q', rfl⟩ ⟨P', rfl⟩ z).1 hz with h | ⟨w, hw, rfl⟩
  · have h1 := hQ z h
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto
  · have h2 := mem_shift_add T2 (jv (Letter.q :: Q')) w (hP w hw)
    rw [hj] at h2 ⊢
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto

/-- The even-count childQ of the odd tile: `vert pw ++ vert qw`, first block in `T2`, second at `texV2 q` in `T1`. -/
theorem glue_vB_false (Q' P' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hP : HV (Letter.q :: P') T2) (hQ : HV (Letter.q :: Q') T1) (hj : jv (Letter.q :: P') = texV2 q) :
    HV ((Letter.q :: P') ++ (Letter.q :: Q')) (oddChildB false T1 T2 p q) := by
  intro z hz
  rcases (mem_vjunction (Letter.q :: P') (Letter.q :: Q') ⟨P', rfl⟩ ⟨Q', rfl⟩ z).1 hz with h | ⟨w, hw, rfl⟩
  · have h1 := hP z h
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto
  · have h2 := mem_shift_add T1 (jv (Letter.q :: P')) w (hQ w hw)
    rw [hj] at h2 ⊢
    unfold oddChildB
    simp only [Finset.mem_union]
    tauto

/-- The odd-count childP of the even tile: `vert qw ++ vert qw ++ vert pw`. -/
theorem glue_vA_true (Q' P' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hQ : HV (Letter.q :: Q') T1) (hP : HV (Letter.q :: P') T2) (hj : jv (Letter.q :: Q') = texV2 p) :
    HV ((Letter.q :: Q') ++ (Letter.q :: Q') ++ (Letter.q :: P')) (evenChildB true T1 T2 p q) := by
  intro z hz
  rw [List.append_assoc] at hz
  rcases (mem_vjunction (Letter.q :: Q') ((Letter.q :: Q') ++ (Letter.q :: P')) ⟨Q', rfl⟩
    ⟨Q' ++ (Letter.q :: P'), rfl⟩ z).1 hz with h | ⟨w, hw, rfl⟩
  · have h1 := hQ z h
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto
  · rcases (mem_vjunction (Letter.q :: Q') (Letter.q :: P') ⟨Q', rfl⟩ ⟨P', rfl⟩ w).1 hw with h' | ⟨v, hv, rfl⟩
    · have h2 := mem_shift_add T1 (jv (Letter.q :: Q')) w (hQ w h')
      rw [hj] at h2 ⊢
      unfold evenChildB
      simp only [Finset.mem_union]
      tauto
    · have h2 := mem_shift_add T2 (jv (Letter.q :: Q') + jv (Letter.q :: Q')) v (hP v hv)
      rw [hj] at h2 ⊢
      have e : v + texV2 p + texV2 p = v + (texV2 p + texV2 p) := by abel
      rw [e]
      unfold evenChildB
      simp only [Finset.mem_union]
      tauto

/-- The even-count childP of the even tile: `vert pw ++ vert qw ++ vert qw`. -/
theorem glue_vA_false (Q' P' : List Letter) (T1 T2 : Tile) (p q : Fraction)
    (hP : HV (Letter.q :: P') T2) (hQ : HV (Letter.q :: Q') T1)
    (hjP : jv (Letter.q :: P') = texV2 q) (hjQ : jv (Letter.q :: Q') = texV2 p) :
    HV ((Letter.q :: P') ++ (Letter.q :: Q') ++ (Letter.q :: Q')) (evenChildB false T1 T2 p q) := by
  intro z hz
  rw [List.append_assoc] at hz
  rcases (mem_vjunction (Letter.q :: P') ((Letter.q :: Q') ++ (Letter.q :: Q')) ⟨P', rfl⟩
    ⟨Q' ++ (Letter.q :: Q'), rfl⟩ z).1 hz with h | ⟨w, hw, rfl⟩
  · have h1 := hP z h
    unfold evenChildB
    simp only [Finset.mem_union]
    tauto
  · rcases (mem_vjunction (Letter.q :: Q') (Letter.q :: Q') ⟨Q', rfl⟩ ⟨Q', rfl⟩ w).1 hw with h' | ⟨v, hv, rfl⟩
    · have h2 := mem_shift_add T1 (jv (Letter.q :: P')) w (hQ w h')
      rw [hjP] at h2 ⊢
      unfold evenChildB
      simp only [Finset.mem_union]
      tauto
    · have h2 := mem_shift_add T1 (jv (Letter.q :: P') + jv (Letter.q :: Q')) v (hQ v hv)
      rw [hjP, hjQ] at h2 ⊢
      have e : v + texV2 p + texV2 q = v + (texV2 q + texV2 p) := by abel
      rw [e]
      unfold evenChildB
      simp only [Finset.mem_union]
      tauto

end FLatticePaper.Tiles.VGlue
