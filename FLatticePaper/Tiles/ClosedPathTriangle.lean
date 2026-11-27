import FLatticePaper.Tiles.ClosedPathDiagonal
import FLatticePaper.Tiles.HorizontalStepOne
import FLatticePaper.Tiles.StringBridge
import FLatticePaper.Tiles.CeilWords

/-! # Condition (C): the optional interfaces (the text's `z*`), the forward horizontal strings

The triangle identities `TriOdd` read the offset of the plain parent `P` with the farther copy of a doubled piece at one point
`z*`. Relative to `P`, `z*` lies on the forward horizontal string of `P` at the tile following the copy of the word of `Q`
(Step 1 of `lemma:weak_standard_odometer_properties`, "the tile `T^+ = T^+_{|w_h(q_1)|+1}` of `w_h(p_1)` is `T_{1/1}` with
`c(T^+) = v_{q_1,1} + v_{q_1,2}`"). This module gives the tools:

* `scanl_getD_sum`, `hOffset_sum`, `fwd_pos`: the `k`-th position of the forward horizontal string of a word `q :: t` is
  `(2k + 1 - c_{k+1}, c_{k+1} - 1)`, where `c_j = qPrefix x j` counts the letters `q` among the first `j` letters;
* `fwd_tile`, `fwd_mem_sites`: the `k`-th tile of the string, and its sites in the marked strings;
* `count_take_succ`: the letter at `k` is `q` exactly when `c_{k+1} = c_k + 1`.

Together with the ceiling-word description of the forward words (`CeilWords.cw_childP`) and the string formula of Step 1
(`HorizontalStepOne.horizontal_formula`), these place and evaluate `z*`. -/

namespace FLatticePaper.Tiles.ClosedPathTriangle

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords

/-! ### Positions of the forward horizontal string -/

theorem scanl_getD_sum : ∀ (L : List GInt) (c : GInt) (k : ℕ), k ≤ L.length →
    (List.scanl (· + ·) c L).getD k 0 = c + (L.take k).sum
  | [], c, k, hk => by
    have : k = 0 := by simpa using hk
    subst this
    simp
  | x :: L, c, 0, _ => by simp
  | x :: L, c, k + 1, hk => by
    have hk' : k ≤ L.length := by simpa using hk
    rw [List.scanl_cons, List.getD_cons_succ, scanl_getD_sum L (c + x) k hk', List.take_succ_cons, List.sum_cons]
    abel

theorem hOffset_sum : ∀ L : BinaryWord,
    (L.map hOffset).sum = (2 * (L.length : ℤ) - (L.count Letter.q : ℤ), (L.count Letter.q : ℤ))
  | [] => by ext <;> simp
  | l :: L => by
    rw [List.map_cons, List.sum_cons, hOffset_sum L]
    cases l <;> ext <;> simp [hOffset] <;> ring

/-- **The positions of the forward horizontal string** of `q :: t`, from `0`: the `k`-th is `(2k + 1 - c_{k+1}, c_{k+1} - 1)`. -/
theorem fwd_pos (t : BinaryWord) (k : ℕ) (hk : k < (Letter.q :: t).length) :
    (List.scanl (· + ·) (0 : GInt) (t.map hOffset)).getD k 0 =
      (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1) := by
  have hk' : k ≤ (t.map hOffset).length := by simp at hk ⊢; omega
  rw [scanl_getD_sum _ 0 k hk', zero_add, ← List.map_take, hOffset_sum]
  have hlen : ((t.take k).length : ℤ) = k := by
    rw [List.length_take]
    simp at hk
    omega
  have hq : qPrefix (Letter.q :: t) (k + 1) = ((t.take k).count Letter.q : ℤ) + 1 := by
    unfold qPrefix
    rw [List.take_succ_cons, List.count_cons]
    simp
  rw [hlen, hq]
  ext <;> simp

/-- The letter at `k` is counted by the prefix of length `k + 1`. -/
theorem count_take_succ (x : BinaryWord) (k : ℕ) (hk : k < x.length) :
    qPrefix x (k + 1) = qPrefix x k + (if x.getD k Letter.p = Letter.q then 1 else 0) := by
  unfold qPrefix
  rw [List.take_add_one, List.count_append]
  have : x[k]? = some (x.getD k Letter.p) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [this]
  simp only [Option.toList_some, List.count_singleton', Nat.cast_add]
  split_ifs <;> simp_all

/-- The `k`-th tile of the forward horizontal string of `q :: t` from `0`. -/
theorem fwd_tile (t : BinaryWord) (k : ℕ) (hk : k < (Letter.q :: t).length) :
    (hStringAt (Letter.q :: t) 0).getD k (ZTile.zero, 0) =
      ((tileSeq (Letter.q :: t)).getD k ZTile.zero,
        (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1)) := by
  have h1 := ClosedPathCorners.getD_fst_of_map _ _ (ClosedPathCorners.hStringAt_map_fst (Letter.q :: t) 0) k
  have h2 : ((hStringAt (Letter.q :: t) 0).getD k (ZTile.zero, 0)).2 =
      (List.scanl (· + ·) (0 : GInt) (t.map hOffset)).getD k 0 := by
    have hlen : (tileSeq (Letter.q :: t)).length = (List.scanl (· + ·) (0 : GInt) (t.map hOffset)).length := by
      simp [tileSeq, tileSeqAux_length_sac]
    have hm : (hStringAt (Letter.q :: t) 0).map Prod.snd = List.scanl (· + ·) (0 : GInt) (t.map hOffset) := by
      unfold hStringAt
      rw [List.map_snd_zip]
      · simp
      · rw [hlen]; simp
    rw [← hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    generalize (hStringAt (Letter.q :: t) 0)[k]? = o
    cases o <;> simp
  apply Prod.ext
  · exact h1
  · rw [h2]
    exact fwd_pos t k hk

/-- A site `(k`-th position) `+ b` of a `q` tile of the forward horizontal string, for `b` in the `2 × 2` square, is a site of the
string (`SiteStrings.stringSites`). -/
theorem fwd_mem_sites (t : BinaryWord) (k : ℕ) (hk : k < (Letter.q :: t).length)
    (hq : (Letter.q :: t).getD k Letter.p = Letter.q) (b : GInt)
    (hb : b ∈ [((0 : ℤ), (0 : ℤ)), (0, 1), (1, 0), (1, 1)]) :
    (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1) + b ∈
      stringSites false false (Letter.q :: t) := by
  set O := origins false false none (startPos false false) (Letter.q :: t) with hO
  have hlenO : O.length = (Letter.q :: t).length := by
    have := congrArg List.length (ClosedPathContacts.origins_letters false false none (startPos false false)
      (Letter.q :: t))
    simpa using this
  have hkO : k < O.length := by rw [hlenO]; exact hk
  set e := O[k]'hkO with he
  have hmem : e ∈ O := List.getElem_mem hkO
  have hpos : e.1 = (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1) := by
    have hm := StringBridge.origins_none_pos (startPos false false) Letter.q t
    have h2 : (O.map (·.1)).getD k 0 = (List.scanl (· + ·) (0 : GInt) (t.map hOffset)).getD k 0 := by
      rw [hO, hm]
      rfl
    have h3 : e.1 = (O.map (·.1)).getD k 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkO]
      rfl
    rw [h3, h2, fwd_pos t k hk]
  have hlet : e.2.1 = Letter.q := by
    have h2 : (O.map (fun e => e.2.1)).getD k Letter.p = (Letter.q :: t).getD k Letter.p := by
      rw [hO, ClosedPathContacts.origins_letters]
    have h3 : e.2.1 = (O.map (fun e => e.2.1)).getD k Letter.p := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkO]
      rfl
    rw [h3, h2, hq]
  have hbs : b ∈ baseSites e.2.1 e.2.2 := by
    rw [hlet]
    cases e.2.2 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢ <;>
      rcases hb with rfl | rfl | rfl | rfl <;> simp [baseSites]
  unfold stringSites
  refine List.mem_flatMap.2 ⟨e, hmem, List.mem_map.2 ⟨b, hbs, ?_⟩⟩
  rw [hpos]
  rfl

/-- The sites of the `2 × 2` square at the `k`-th position of the forward horizontal string are sites of the string, whatever the
letter of the tile. -/
theorem fwd_mem_sites_any (t : BinaryWord) (k : ℕ) (hk : k < (Letter.q :: t).length) (b : GInt)
    (hb : b ∈ [((0 : ℤ), (0 : ℤ)), (0, 1), (1, 0), (1, 1)]) :
    (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1) + b ∈
      stringSites false false (Letter.q :: t) := by
  by_cases hq : (Letter.q :: t).getD k Letter.p = Letter.q
  · exact fwd_mem_sites t k hk hq b hb
  set O := origins false false none (startPos false false) (Letter.q :: t) with hO
  have hlenO : O.length = (Letter.q :: t).length := by
    have := congrArg List.length (ClosedPathContacts.origins_letters false false none (startPos false false)
      (Letter.q :: t))
    simpa using this
  have hkO : k < O.length := by rw [hlenO]; exact hk
  set e := O[k]'hkO with he
  have hmem : e ∈ O := List.getElem_mem hkO
  have hpos : e.1 = (2 * (k : ℤ) + 1 - qPrefix (Letter.q :: t) (k + 1), qPrefix (Letter.q :: t) (k + 1) - 1) := by
    have hm := StringBridge.origins_none_pos (startPos false false) Letter.q t
    have h2 : (O.map (·.1)).getD k 0 = (List.scanl (· + ·) (0 : GInt) (t.map hOffset)).getD k 0 := by
      rw [hO, hm]
      rfl
    have h3 : e.1 = (O.map (·.1)).getD k 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkO]
      rfl
    rw [h3, h2, fwd_pos t k hk]
  have hlet : e.2.1 = Letter.p := by
    have h2 : (O.map (fun e => e.2.1)).getD k Letter.p = (Letter.q :: t).getD k Letter.p := by
      rw [hO, ClosedPathContacts.origins_letters]
    have h3 : e.2.1 = (O.map (fun e => e.2.1)).getD k Letter.p := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkO]
      rfl
    rw [h3, h2]
    cases h : (Letter.q :: t).getD k Letter.p
    · rfl
    · exact absurd h hq
  have hbs : b ∈ baseSites e.2.1 e.2.2 := by
    rw [hlet]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [baseSites]
  unfold stringSites
  refine List.mem_flatMap.2 ⟨e, hmem, List.mem_map.2 ⟨b, hbs, ?_⟩⟩
  rw [hpos]
  rfl

end FLatticePaper.Tiles.ClosedPathTriangle
