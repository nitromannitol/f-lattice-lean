import FLatticePaper.Tiles.BaseFamilies
import FLatticePaper.Tiles.HorizontalInduction

/-! Task 53, marksIn (base words): the invariant `Inv` of the base words `[]`, `3^n` and `2^n` (`n ≥ 1`), so that the horizontal
induction `HorizontalInduction.inv_all` applies to every word.

The quads of the base words are explicit for every `n ≥ 0` (`quad3`, `quad2`); the tiles and registers of the base words are the
base tiles of `childTiles` and the register identities of `reg_two`, `reg_three`. -/

namespace FLatticePaper.Tiles.BaseInvariant

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.HorizontalGlue
open FLatticePaper.Tiles.HorizontalStep FLatticePaper.Tiles.HorizontalInduction FLatticePaper.Tiles.BaseFamilies
open FLatticePaper.Tiles.CeilWords

/-- The quad of `3^n`: `childP = q p^n q p^{n+1}`, `childQ = q p^{n+1}`, `parentP = p`, `parentQ = q p^n`. -/
theorem quad3 (n : ℕ) : quadAt [] (List.replicate n Digit.three) =
    { childP := (Letter.q :: List.replicate n Letter.p) ++ (Letter.q :: List.replicate (n + 1) Letter.p),
      childQ := Letter.q :: List.replicate (n + 1) Letter.p,
      parentP := [Letter.p],
      parentQ := Letter.q :: List.replicate n Letter.p } := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : List.replicate (n + 1) Digit.three = List.replicate n Digit.three ++ [Digit.three] := by
      simp [List.replicate_succ']
    have hc : (List.replicate n Digit.three ++ [Digit.three]).count Digit.one % 2 = 0 := by
      simp [List.count_replicate]
    rw [e, quadAt_snoc_nil, ih]
    simp only [WordQuad.step, childWords, hc, if_true]
    simp [List.replicate_succ', List.append_assoc]

theorem rep_add_one_q (k : ℕ) : List.replicate (k + 1) Letter.q = Letter.q :: List.replicate k Letter.q := rfl

theorem rep_add_two_q (k : ℕ) : List.replicate (k + 2) Letter.q = Letter.q :: Letter.q :: List.replicate k Letter.q := rfl

/-- The quad of `2^n`: `childP = q^{2n+2} p`, `childQ = q^{2n+1} p`, `parentP = q^{2n} p`, `parentQ = q`. -/
theorem quad2 (n : ℕ) : quadAt [] (List.replicate n Digit.two) =
    { childP := List.replicate (2 * n + 2) Letter.q ++ [Letter.p],
      childQ := List.replicate (2 * n + 1) Letter.q ++ [Letter.p],
      parentP := List.replicate (2 * n) Letter.q ++ [Letter.p],
      parentQ := [Letter.q] } := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : List.replicate (n + 1) Digit.two = List.replicate n Digit.two ++ [Digit.two] := by
      simp [List.replicate_succ']
    have hc : (List.replicate n Digit.two ++ [Digit.two]).count Digit.one % 2 = 0 := by
      simp [List.count_replicate]
    rw [e, quadAt_snoc_nil, ih]
    simp only [WordQuad.step, childWords, hc, if_true, WordQuad.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial


/-! ### The string families, with the arguments of the base quads and tiles -/

theorem jn_q_rep (n : ℕ) : jn (Letter.q :: List.replicate n Letter.p) = (2 * (n : ℤ) + 1, 1) := by
  refine Prod.ext ?_ ?_
  · simp [jn, List.count_replicate]
    ring
  · simp [jn, List.count_replicate]

theorem ladder_family (n : ℕ) (hn : 1 ≤ n) :
    ∀ z ∈ stringSites false false ((Letter.q :: List.replicate n Letter.p) ++ (Letter.q :: List.replicate (n + 1) Letter.p)),
      z ∈ ladderF (2 * (n : ℤ) + 2) := by
  intro z hz
  have hX : (Letter.q :: List.replicate n Letter.p).getLast? = some Letter.p := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [getLast?_cons_of_ne _ _ (by simp)]
    exact getLast?_rep_succ j Letter.p
  rw [stringSites_block' (List.replicate n Letter.p) (List.replicate (n + 1) Letter.p) hX] at hz
  simp only [List.mem_append, List.mem_map] at hz
  rcases hz with h | ⟨w, hw, rfl⟩
  · exact ladderF_mem n z (Or.inl (prun_bounds n z h))
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := prun_bounds (n + 1) w hw
    rw [jn_q_rep]
    refine ladderF_mem n _ (Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩) <;> simp only [Prod.fst_add, Prod.snd_add] <;> push_cast at * <;> omega

theorem stairF_family (m : ℕ) (hm : 1 ≤ m) :
    ∀ z ∈ stringSites false false (Letter.q :: List.replicate m Letter.p), z ∈ stairF (2 * (m : ℤ) + 1) :=
  fun z hz => stairF_mem m hm z (prun_bounds m z hz)

theorem nstair_family (m : ℕ) (hm : 1 ≤ m) :
    ∀ z ∈ stringSites false false (List.replicate (2 * m) Letter.q ++ [Letter.p]), z ∈ nstairN (2 * (m : ℤ) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  intro z hz
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, stringSites_snoc_mem _ (by simp) Letter.p z] at hz
  rcases hz with h | ⟨b, hb, rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qrun_bounds (2 * j + 1) z h
    apply nstairN_mem (j + 1) (by omega) z
    push_cast at h2 h4 ⊢
    omega
  · have ht : (List.replicate (2 * j + 1 + 1) Letter.q).tail = List.replicate (2 * j + 1) Letter.q := rfl
    rw [ht, sumStep_rep_q]
    apply nstairN_mem (j + 1) (by omega)
    simp only [baseSites] at hb
    simp only [stepH] at hb ⊢
    push_cast
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

theorem nladder_family (m : ℕ) (hm : 1 ≤ m) :
    ∀ z ∈ stringSites false false (List.replicate (2 * m + 1) Letter.q ++ [Letter.p]),
      z ∈ nladderN (2 * (m : ℤ) + 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  intro z hz
  rw [show 2 * (j + 1) + 1 = 2 * j + 2 + 1 by ring, stringSites_snoc_mem _ (by simp) Letter.p z] at hz
  rcases hz with h | ⟨b, hb, rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qrun_bounds (2 * j + 2) z h
    apply nladderN_mem (j + 1) (by omega) z
    push_cast at h2 h4 ⊢
    omega
  · have ht : (List.replicate (2 * j + 2 + 1) Letter.q).tail = List.replicate (2 * j + 2) Letter.q := rfl
    rw [ht, sumStep_rep_q]
    apply nladderN_mem (j + 1) (by omega)
    simp only [baseSites] at hb
    simp only [stepH] at hb ⊢
    push_cast
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-! ### Base tiles and registers -/

theorem rep_ne_three_of_two (n : ℕ) (hn : 1 ≤ n) :
    List.replicate n Digit.two ≠ List.replicate (List.replicate n Digit.two).length Digit.three := by
  intro h
  have := (List.eq_replicate_iff.1 h).2 Digit.two (List.mem_replicate.2 ⟨by omega, rfl⟩)
  exact absurd this (by decide)

theorem oddTile_three (n : ℕ) (hn : 1 ≤ n) :
    oddTile (List.replicate n Digit.three) = ladderF (2 * (n : ℤ) + 2) := by
  have h0 : ¬ (List.replicate n Digit.three = []) := by simp; omega
  have h1 : List.replicate n Digit.three = List.replicate (List.replicate n Digit.three).length Digit.three := by
    simp
  unfold oddTile childTiles
  rw [if_neg h0, if_pos h1]
  simp

theorem evenTile_three (n : ℕ) : evenTile (List.replicate n Digit.three) = stairF (2 * (n : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold evenTile childTiles
    simp
  · have h0 : ¬ (List.replicate n Digit.three = []) := by simp; omega
    have h1 : List.replicate n Digit.three = List.replicate (List.replicate n Digit.three).length Digit.three := by
      simp
    unfold evenTile childTiles
    rw [if_neg h0, if_pos h1]
    simp

theorem oddTile_two (n : ℕ) : oddTile (List.replicate n Digit.two) = nstairN (2 * (n : ℤ) + 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold oddTile childTiles
    simp
  · have h0 : ¬ (List.replicate n Digit.two = []) := by simp; omega
    have h2 : List.replicate n Digit.two = List.replicate (List.replicate n Digit.two).length Digit.two := by
      simp
    unfold oddTile childTiles
    rw [if_neg h0, if_neg (rep_ne_three_of_two n hn), if_pos h2]
    simp

theorem evenTile_two (n : ℕ) (hn : 1 ≤ n) :
    evenTile (List.replicate n Digit.two) = nladderN (2 * (n : ℤ) + 2) := by
  have h0 : ¬ (List.replicate n Digit.two = []) := by simp; omega
  have h2 : List.replicate n Digit.two = List.replicate (List.replicate n Digit.two).length Digit.two := by
    simp
  unfold evenTile childTiles
  rw [if_neg h0, if_neg (rep_ne_three_of_two n hn), if_pos h2]
  simp

theorem tOdd_state_three (n : ℕ) : (stateAt (List.replicate n Digit.three)).tOdd = zeroTile := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : List.replicate (n + 1) Digit.three = List.replicate n Digit.three ++ [Digit.three] := by
      simp [List.replicate_succ']
    rw [e]
    exact (reg_three _).1.trans ih

theorem tEven_state_three (j : ℕ) : (stateAt (List.replicate (j + 1) Digit.three)).tEven = stairF (2 * (j : ℤ) + 3) := by
  have e : List.replicate (j + 1) Digit.three = List.replicate j Digit.three ++ [Digit.three] := by
    simp [List.replicate_succ']
  rw [e, (reg_three _).2, evenTile_three]

theorem tOdd_state_two (j : ℕ) : (stateAt (List.replicate (j + 1) Digit.two)).tOdd = nstairN (2 * (j : ℤ) + 3) := by
  have e : List.replicate (j + 1) Digit.two = List.replicate j Digit.two ++ [Digit.two] := by
    simp [List.replicate_succ']
  rw [e, (reg_two _).1, oddTile_two]

theorem tEven_state_two (n : ℕ) : (stateAt (List.replicate n Digit.two)).tEven = oneTile := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : List.replicate (n + 1) Digit.two = List.replicate n Digit.two ++ [Digit.two] := by
      simp [List.replicate_succ']
    rw [e, (reg_two _).2, ih]

theorem hc_p_zero : ∀ z ∈ stringSites false false [Letter.p], z ∈ zeroTile := by
  intro z hz
  simp [stringSites, origins, baseSites, startPos] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem hc_q_one : ∀ z ∈ stringSites false false [Letter.q], z ∈ oneTile := by
  intro z hz
  simp [stringSites, origins, baseSites, startPos] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> decide

/-! ### The invariant of the base words -/

theorem inv_nil : HorizontalStep.Inv [] := by
  have hq : quadAt [] [] =
      { childP := [Letter.q, Letter.q, Letter.p], childQ := [Letter.q, Letter.p], parentP := [Letter.p],
        parentQ := [Letter.q] } := rfl
  unfold HorizontalStep.Inv
  rw [hq]
  have ho : oddTile [] = nstairN 3 := rfl
  have he : evenTile [] = stairF 3 := rfl
  have hs : stateAt [] = initState := rfl
  rw [ho, he, hs]
  refine ⟨?_, ?_, hc_p_zero, hc_q_one⟩
  · intro z hz
    have := nstair_family 1 le_rfl z hz
    have e3 : (2 * ((1 : ℕ) : ℤ) + 1) = 3 := by norm_num
    rw [e3] at this
    exact this
  · intro z hz
    have := stairF_family 1 le_rfl z hz
    have e3 : (2 * ((1 : ℕ) : ℤ) + 1) = 3 := by norm_num
    rw [e3] at this
    exact this

theorem inv_three (j : ℕ) : HorizontalStep.Inv (List.replicate (j + 1) Digit.three) := by
  unfold HorizontalStep.Inv
  rw [quad3 (j + 1), oddTile_three (j + 1) (by omega), evenTile_three, tOdd_state_three, tEven_state_three]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ladder_family (j + 1) (by omega)
  · intro z hz
    have := stairF_family (j + 2) (by omega) z hz
    have e : (2 * ((j + 2 : ℕ) : ℤ) + 1) = 2 * ((j + 1 : ℕ) : ℤ) + 3 := by push_cast; ring
    rw [e] at this
    exact this
  · exact hc_p_zero
  · intro z hz
    have := stairF_family (j + 1) (by omega) z hz
    have e : (2 * ((j + 1 : ℕ) : ℤ) + 1) = 2 * (j : ℤ) + 3 := by push_cast; ring
    rw [e] at this
    exact this

theorem inv_two (j : ℕ) : HorizontalStep.Inv (List.replicate (j + 1) Digit.two) := by
  unfold HorizontalStep.Inv
  rw [quad2 (j + 1), oddTile_two, evenTile_two (j + 1) (by omega), tOdd_state_two, tEven_state_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : 2 * (j + 1) + 2 = 2 * (j + 2) := by ring
    rw [e]
    intro z hz
    have := nstair_family (j + 2) (by omega) z hz
    have e' : (2 * ((j + 2 : ℕ) : ℤ) + 1) = 2 * ((j + 1 : ℕ) : ℤ) + 3 := by push_cast; ring
    rw [e'] at this
    exact this
  · exact nladder_family (j + 1) (by omega)
  · intro z hz
    have := nstair_family (j + 1) (by omega) z hz
    have e' : (2 * ((j + 1 : ℕ) : ℤ) + 1) = 2 * (j : ℤ) + 3 := by push_cast; ring
    rw [e'] at this
    exact this
  · exact hc_q_one

/-- The horizontal strings of every standard tile lie in the tile: the odd string in `oddTile`, the even string in `evenTile`. -/
theorem horizontal_marks (w : Word) :
    HC (quadAt [] w).childP (oddTile w) ∧ HC (quadAt [] w).childQ (evenTile w) :=
  horizontal_all inv_nil
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact inv_three j)
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact inv_two j) w

end FLatticePaper.Tiles.BaseInvariant
