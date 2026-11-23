import FLatticePaper.Tiles.CeilWords
import FLatticePaper.Construction.OffsetTables

/-! Task 53, marksIn (blocks): the shape of a ceiling block, and its junction offset.

A ceiling word `x` of slope `k/l` (`CeilWord x k l`) has length `l` and `k` letters `q`. When `1 ≤ k < l` it starts with `q` and
ends with `p`, so it can be followed by a block of the same kind (`SiteJunction.stringSites_block`). Its junction offset
`(2|x| - #q x, #q x)` is `texV1Odd f` for the odd slope `(2 num, den + num)` and `texV1Even f` for the even slope
`(num, (den + num)/2)` of a fraction `f`. -/

namespace FLatticePaper.Tiles.CeilBlocks

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CeilWords FLatticePaper.Construction

theorem ceil_count_q (x : BinaryWord) (k l : ℤ) (hx : CeilWord x k l) (hl : 1 ≤ l) :
    (x.count Letter.q : ℤ) = k := by
  have h := ceil_total x k l hx hl
  unfold qPrefix at h
  rw [List.take_length] at h
  exact_mod_cast h

theorem ceil_head_q (x : BinaryWord) (k l : ℤ) (hx : CeilWord x k l) (h1 : 1 ≤ k) (h2 : k < l) :
    ∃ x', x = Letter.q :: x' := by
  have hlen := hx.1
  have hcond := hx.2
  have hne : x ≠ [] := by
    rintro rfl
    simp at hlen
    omega
  obtain ⟨a, x', rfl⟩ := List.exists_cons_of_ne_nil hne
  cases a with
  | q => exact ⟨x', rfl⟩
  | p =>
    exfalso
    have h := hcond 1 (by norm_num; omega)
    simp [qPrefix] at h
    all_goals omega

theorem ceil_last_p (x : BinaryWord) (k l : ℤ) (hx : CeilWord x k l) (h1 : 1 ≤ k) (h2 : k < l) :
    x.getLast? = some Letter.p := by
  have hlen := hx.1
  have hcond := hx.2
  have hne : x ≠ [] := by
    rintro rfl
    simp at hlen
    omega
  obtain ⟨L, z, rfl⟩ : ∃ L z, x = L ++ [z] :=
    ⟨x.dropLast, x.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  cases z with
  | p => simp
  | q =>
    exfalso
    have hc : ((L ++ [Letter.q]).count Letter.q : ℤ) = k := ceil_count_q _ k l hx (by omega)
    have hLlen : (L.length : ℤ) = l - 1 := by
      simp at hlen
      omega
    have hq : qPrefix (L ++ [Letter.q]) L.length = k - 1 := by
      unfold qPrefix
      rw [List.take_left' rfl]
      simp only [List.count_append, List.count_cons, List.count_nil] at hc ⊢
      simp at hc ⊢
      omega
    have h := hcond L.length (by omega)
    rw [hq, hLlen] at h
    nlinarith [h.2, h2]

/-- The junction offset of an odd block: `(2|x| - #q x, #q x) = texV1Odd f` for the slope `(2 num, den + num)`. -/
theorem offset_odd (x : BinaryWord) (f : Fraction)
    (hx : CeilWord x (2 * f.num) (f.den + f.num)) (hl : 1 ≤ f.den + f.num) :
    (2 * (x.length : ℤ) - (x.count Letter.q : ℤ), (x.count Letter.q : ℤ)) = texV1Odd f := by
  have hlen := hx.1
  have hc := ceil_count_q x _ _ hx hl
  unfold texV1Odd
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega

/-- The junction offset of an even block: `(2|x| - #q x, #q x) = texV1Even f` for the slope `(num, (den + num)/2)`. -/
theorem offset_even (x : BinaryWord) (f : Fraction)
    (hx : CeilWord x f.num ((f.den + f.num) / 2)) (hl : 1 ≤ (f.den + f.num) / 2) (hf : f.Even) :
    (2 * (x.length : ℤ) - (x.count Letter.q : ℤ), (x.count Letter.q : ℤ)) = texV1Even f := by
  have hlen := hx.1
  have hc := ceil_count_q x _ _ hx hl
  have hf' : (f.num + f.den) % 2 = 0 := hf
  unfold texV1Even
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega

end FLatticePaper.Tiles.CeilBlocks
