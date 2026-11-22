import FLatticePaper.Construction.BaseFamily
import FLatticePaper.Tiles.StandardTiles

/-! # The standard base registers against the TeX base tiles (task 44, step 2)

The constructor's four standard base masks, normalised to the lowest cell at the origin (`BaseMask.tile` then `llCenter`),
have the same site sets as the TeX closed forms of `childTiles` for the base words:

* `stairOdd M` (odd `M`) is `nstairN M`; `stairEven M` (odd `M`) is `stairF M`;
* `ladderEven M` (even `M`) is `nladderN M`; `ladderOdd M` (even `M`) is `ladderF M`.

Each equality is an extensionality over the explicit membership predicates of the mask (`mem_*_direct`, BaseMasks and
BaseFamily) and of the TeX tile (`mem_stairF`, `mem_nstairF`, ...), and `tile_llCenter_iff` (BaseFamily), which reads the
normalised tile through the lower-left cell of the raw mask. -/

namespace FLatticePaper.Tiles.BaseRegistersTeX

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.Standard

/-- `stairOdd M` normalised is the TeX tile `nstairN M`. -/
theorem stairOdd_llCenter_sites (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) :
    ((BaseMask.stairOdd.tile M hM).llCenter (BaseMask.stairOdd.tile_nonempty M hM)).sites = nstairN M := by
  ext v
  rw [tile_llCenter_iff BaseMask.stairOdd M hM (0, 1) (fun hne => stairOdd_lowerLeft M hM hne) v]
  rw [nstairN, mem_shift, mem_nstairF (by omega), BaseMask.mem_stairOdd_raw_direct]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- `stairEven M` normalised is the TeX tile `stairF M`. -/
theorem stairEven_llCenter_sites (M : ℤ) (hM : 3 ≤ M ∧ M % 2 = 1) :
    ((BaseMask.stairEven.tile M hM).llCenter (BaseMask.stairEven.tile_nonempty M hM)).sites = stairF M := by
  ext v
  rw [tile_llCenter_iff BaseMask.stairEven M hM (0, 0) (fun hne => stairEven_lowerLeft M hM hne) v]
  rw [mem_stairF (by omega), BaseMask.mem_stairEven_raw_iff]
  simp only [Prod.fst_add, Prod.snd_add, BaseMask.StairEvenCorner]
  omega

/-- `ladderEven M` normalised is the TeX tile `nladderN M`. -/
theorem ladderEven_llCenter_sites (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((BaseMask.ladderEven.tile M hM).llCenter (BaseMask.ladderEven.tile_nonempty M hM)).sites = nladderN M := by
  ext v
  rw [tile_llCenter_iff BaseMask.ladderEven M hM (0, 1) (fun hne => ladderEven_lowerLeft M hM hne) v]
  rw [nladderN, mem_shift, mem_nladderF (by omega), BaseMask.mem_ladderEven_raw_direct]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

/-- `ladderOdd M` normalised is the TeX tile `ladderF M`. -/
theorem ladderOdd_llCenter_sites (M : ℤ) (hM : 4 ≤ M ∧ M % 2 = 0) :
    ((BaseMask.ladderOdd.tile M hM).llCenter (BaseMask.ladderOdd.tile_nonempty M hM)).sites = ladderF M := by
  ext v
  rw [tile_llCenter_iff BaseMask.ladderOdd M hM (0, 0) (fun hne => ladderOdd_lowerLeft M hM hne) v]
  rw [mem_ladderF (by omega), mem_ladderOdd_direct]
  simp only [Prod.fst_add, Prod.snd_add]
  omega


/-! ### The endpoint atoms: the zero and one tiles -/

/-- The endpoint atom `one` attached at a standard tile, normalised, is the TeX tile `oneTile`. -/
theorem endpointOne_attach_llCenter_sites (S : NonemptyTile) :
    ((EndpointAtom.one.attach S).llCenter).val.sites = oneTile := by
  ext v
  unfold EndpointAtom.attach
  have hT0 : ((EndpointAtom.one.atOrigin).val.place (S.val.lowerLeft S.property) 0).sites.Nonempty :=
    ((EndpointAtom.one.atOrigin).place (S.val.lowerLeft S.property) 0).property
  refine (mem_llCenter_trim _ _ v).trans ?_
  show v + ((EndpointAtom.one.atOrigin).val.place (S.val.lowerLeft S.property) 0).lowerLeft hT0 ∈
    ((EndpointAtom.one.atOrigin).val.place (S.val.lowerLeft S.property) 0).sites ↔ v ∈ oneTile
  have hlow : ((EndpointAtom.one.atOrigin).val.place (S.val.lowerLeft S.property) 0).lowerLeft hT0 =
      S.val.lowerLeft S.property := by
    apply HeightTile.lowerLeft_eq_of_minimal _ hT0 (point := S.val.lowerLeft S.property)
    · rw [HeightTile.mem_place_sites, sub_self]
      simp [EndpointAtom.atOrigin, mem_maskedTile_sites]
    · intro site hsite
      rw [HeightTile.mem_place_sites] at hsite
      simp only [EndpointAtom.atOrigin, mem_maskedTile_sites, Prod.fst_sub, Prod.snd_sub,
        Option.isSome_some, and_true] at hsite
      omega
  rw [hlow, HeightTile.mem_place_sites, add_sub_cancel_right]
  simp only [EndpointAtom.atOrigin, mem_maskedTile_sites, Option.isSome_some, and_true, oneTile,
    Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

/-- The endpoint atom `zero` attached at a standard tile, normalised, is the TeX tile `zeroTile`. -/
theorem endpointZero_attach_llCenter_sites (S : NonemptyTile) :
    ((EndpointAtom.zero.attach S).llCenter).val.sites = zeroTile := by
  ext v
  unfold EndpointAtom.attach
  have hT0 : ((EndpointAtom.zero.atOrigin).val.place (S.val.lowerLeft S.property) 0).sites.Nonempty :=
    ((EndpointAtom.zero.atOrigin).place (S.val.lowerLeft S.property) 0).property
  refine (mem_llCenter_trim _ _ v).trans ?_
  show v + ((EndpointAtom.zero.atOrigin).val.place (S.val.lowerLeft S.property) 0).lowerLeft hT0 ∈
    ((EndpointAtom.zero.atOrigin).val.place (S.val.lowerLeft S.property) 0).sites ↔ v ∈ zeroTile
  have hlow : ((EndpointAtom.zero.atOrigin).val.place (S.val.lowerLeft S.property) 0).lowerLeft hT0 =
      S.val.lowerLeft S.property := by
    apply HeightTile.lowerLeft_eq_of_minimal _ hT0 (point := S.val.lowerLeft S.property)
    · rw [HeightTile.mem_place_sites, sub_self]
      simp [EndpointAtom.atOrigin, mem_maskedTile_sites]
    · intro site hsite
      rw [HeightTile.mem_place_sites] at hsite
      simp only [EndpointAtom.atOrigin, mem_maskedTile_sites, Prod.fst_sub, Prod.snd_sub,
        Option.isSome_some, and_true] at hsite
      omega
  rw [hlow, HeightTile.mem_place_sites, add_sub_cancel_right]
  simp only [EndpointAtom.atOrigin, mem_maskedTile_sites, Option.isSome_some, and_true, zeroTile,
    Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

/-! ### The closed forms of `childTiles` on the pure words -/

theorem childTiles_two_fst (L : ℕ) (s : TState) :
    (childTiles (List.replicate L Digit.two) s).1 = nstairN (2 * (L : ℤ) + 3) := by
  cases L with
  | zero =>
    rw [List.replicate_zero, childTiles_nil]
    simp
  | succ L =>
    have h1 : List.replicate (L + 1) Digit.two ≠ [] := by simp
    have h2 : List.replicate (L + 1) Digit.two ≠
        List.replicate (List.replicate (L + 1) Digit.two).length Digit.three := by
      intro h
      have hmem : Digit.two ∈ List.replicate (L + 1) Digit.two := by simp
      rw [h, List.mem_replicate] at hmem
      exact absurd hmem.2 (by decide)
    have h3 : List.replicate (L + 1) Digit.two =
        List.replicate (List.replicate (L + 1) Digit.two).length Digit.two := by simp
    unfold childTiles
    rw [if_neg h1, if_neg h2, if_pos h3]
    simp

theorem childTiles_two_snd (L : ℕ) (s : TState) :
    (childTiles (List.replicate (L + 1) Digit.two) s).2 = nladderN (2 * ((L + 1 : ℕ) : ℤ) + 2) := by
  have h1 : List.replicate (L + 1) Digit.two ≠ [] := by simp
  have h2 : List.replicate (L + 1) Digit.two ≠
      List.replicate (List.replicate (L + 1) Digit.two).length Digit.three := by
    intro h
    have hmem : Digit.two ∈ List.replicate (L + 1) Digit.two := by simp
    rw [h, List.mem_replicate] at hmem
    exact absurd hmem.2 (by decide)
  have h3 : List.replicate (L + 1) Digit.two =
      List.replicate (List.replicate (L + 1) Digit.two).length Digit.two := by simp
  unfold childTiles
  rw [if_neg h1, if_neg h2, if_pos h3]
  simp

theorem childTiles_three_fst (L : ℕ) (s : TState) :
    (childTiles (List.replicate (L + 1) Digit.three) s).1 = ladderF (2 * ((L + 1 : ℕ) : ℤ) + 2) := by
  have h1 : List.replicate (L + 1) Digit.three ≠ [] := by simp
  have h3 : List.replicate (L + 1) Digit.three =
      List.replicate (List.replicate (L + 1) Digit.three).length Digit.three := by simp
  unfold childTiles
  rw [if_neg h1, if_pos h3]
  simp

theorem childTiles_three_snd (L : ℕ) (s : TState) :
    (childTiles (List.replicate L Digit.three) s).2 = stairF (2 * (L : ℤ) + 3) := by
  cases L with
  | zero =>
    rw [List.replicate_zero, childTiles_nil]
    simp
  | succ L =>
    have h1 : List.replicate (L + 1) Digit.three ≠ [] := by simp
    have h3 : List.replicate (L + 1) Digit.three =
        List.replicate (List.replicate (L + 1) Digit.three).length Digit.three := by simp
    unfold childTiles
    rw [if_neg h1, if_pos h3]
    simp

/-! ### The TeX states on the pure words -/

theorem runFrom_cons_eq (pre : Word) (d : Digit) (rest : Word) (s : TState) :
    runFrom pre (d :: rest) s = runFrom (pre ++ [d]) rest (stepState pre s d) := rfl

theorem runFrom_two (j n : ℕ) (s : TState) :
    (runFrom (List.replicate j Digit.two) (List.replicate (n + 1) Digit.two) s).tOdd =
        nstairN (2 * ((j + n : ℕ) : ℤ) + 3) ∧
      (runFrom (List.replicate j Digit.two) (List.replicate (n + 1) Digit.two) s).tEven = s.tEven := by
  induction n generalizing j s with
  | zero =>
    simp only [List.replicate_succ, List.replicate_zero, runFrom_cons_eq, runFrom, stepState,
      childTiles_two_fst, Nat.add_zero, and_self]
  | succ n ih =>
    rw [List.replicate_succ (n := n + 1), runFrom_cons_eq]
    have hpre : List.replicate j Digit.two ++ [Digit.two] = List.replicate (j + 1) Digit.two := by
      rw [List.replicate_succ']
    rw [hpre]
    obtain ⟨h1, h2⟩ := ih (j + 1) (stepState (List.replicate j Digit.two) s Digit.two)
    refine ⟨?_, ?_⟩
    · rw [h1]
      congr 1
      omega
    · rw [h2]
      rfl

theorem runFrom_three (j n : ℕ) (s : TState) :
    (runFrom (List.replicate j Digit.three) (List.replicate (n + 1) Digit.three) s).tEven =
        stairF (2 * ((j + n : ℕ) : ℤ) + 3) ∧
      (runFrom (List.replicate j Digit.three) (List.replicate (n + 1) Digit.three) s).tOdd = s.tOdd := by
  induction n generalizing j s with
  | zero =>
    simp only [List.replicate_succ, List.replicate_zero, runFrom_cons_eq, runFrom, stepState,
      childTiles_three_snd, Nat.add_zero, and_self]
  | succ n ih =>
    rw [List.replicate_succ (n := n + 1), runFrom_cons_eq]
    have hpre : List.replicate j Digit.three ++ [Digit.three] = List.replicate (j + 1) Digit.three := by
      rw [List.replicate_succ']
    rw [hpre]
    obtain ⟨h1, h2⟩ := ih (j + 1) (stepState (List.replicate j Digit.three) s Digit.three)
    refine ⟨?_, ?_⟩
    · rw [h1]
      congr 1
      omega
    · rw [h2]
      rfl

theorem stateAt_two (k : ℕ) :
    (stateAt (List.replicate (k + 1) Digit.two)).tOdd = nstairN (2 * (k : ℤ) + 3) ∧
      (stateAt (List.replicate (k + 1) Digit.two)).tEven = oneTile := by
  unfold stateAt
  have h := runFrom_two 0 k initState
  rw [List.replicate_zero] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h1]
    congr 1
    omega
  · rw [h2]
    rfl

theorem stateAt_three (k : ℕ) :
    (stateAt (List.replicate (k + 1) Digit.three)).tEven = stairF (2 * (k : ℤ) + 3) ∧
      (stateAt (List.replicate (k + 1) Digit.three)).tOdd = zeroTile := by
  unfold stateAt
  have h := runFrom_three 0 k initState
  rw [List.replicate_zero] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h1]
    congr 1
    omega
  · rw [h2]
    rfl

/-! ### The base registers against the TeX base tiles -/

/-- The TeX tiles of the pure words, read from the closed forms. -/
theorem oddTile_two (L : ℕ) (hL : 1 ≤ L) :
    oddTile (List.replicate L Digit.two) = nstairN (2 * (L : ℤ) + 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  exact childTiles_two_fst (k + 1) _

theorem evenTile_two (L : ℕ) (hL : 1 ≤ L) :
    evenTile (List.replicate L Digit.two) = nladderN (2 * (L : ℤ) + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  exact childTiles_two_snd k _

theorem oddTile_three (L : ℕ) (hL : 1 ≤ L) :
    oddTile (List.replicate L Digit.three) = ladderF (2 * (L : ℤ) + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  exact childTiles_three_fst k _

theorem evenTile_three (L : ℕ) :
    evenTile (List.replicate L Digit.three) = stairF (2 * (L : ℤ) + 3) :=
  childTiles_three_snd L _

theorem twos_std (e : ℕ) :
    ((BaseRun.registers (.twos e)).llCenter.standard.currentOdd).val.sites =
        oddTile (List.replicate (e + 1) Digit.two) ∧
      ((BaseRun.registers (.twos e)).llCenter.standard.currentEven).val.sites =
        evenTile (List.replicate (e + 1) Digit.two) ∧
      ((BaseRun.registers (.twos e)).llCenter.standard.retainedOdd).val.sites =
        (stateAt (List.replicate (e + 1) Digit.two)).tOdd ∧
      ((BaseRun.registers (.twos e)).llCenter.standard.retainedEven).val.sites =
        (stateAt (List.replicate (e + 1) Digit.two)).tEven := by
  obtain ⟨h1, h2⟩ := stateAt_two e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oddTile_two (e + 1) (by omega)]
    refine (stairOdd_llCenter_sites (2 * (e : ℤ) + 3 + 2) ⟨by omega, by omega⟩).trans ?_
    congr 1
  · rw [evenTile_two (e + 1) (by omega)]
    refine (ladderEven_llCenter_sites (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩).trans ?_
    congr 1
  · rw [h1]
    exact stairOdd_llCenter_sites (2 * (e : ℤ) + 3) ⟨by omega, by omega⟩
  · rw [h2]
    exact endpointOne_attach_llCenter_sites _

theorem threes_std (e : ℕ) :
    ((BaseRun.registers (.threes e)).llCenter.standard.currentOdd).val.sites =
        oddTile (List.replicate (e + 1) Digit.three) ∧
      ((BaseRun.registers (.threes e)).llCenter.standard.currentEven).val.sites =
        evenTile (List.replicate (e + 1) Digit.three) ∧
      ((BaseRun.registers (.threes e)).llCenter.standard.retainedOdd).val.sites =
        (stateAt (List.replicate (e + 1) Digit.three)).tOdd ∧
      ((BaseRun.registers (.threes e)).llCenter.standard.retainedEven).val.sites =
        (stateAt (List.replicate (e + 1) Digit.three)).tEven := by
  obtain ⟨h1, h2⟩ := stateAt_three e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oddTile_three (e + 1) (by omega)]
    refine (ladderOdd_llCenter_sites (2 * (e : ℤ) + 3 + 1) ⟨by omega, by omega⟩).trans ?_
    congr 1
  · rw [evenTile_three (e + 1)]
    refine (stairEven_llCenter_sites (2 * (e : ℤ) + 3 + 2) ⟨by omega, by omega⟩).trans ?_
    congr 1
  · rw [h2]
    exact endpointZero_attach_llCenter_sites _
  · rw [h1]
    exact stairEven_llCenter_sites (2 * (e : ℤ) + 3) ⟨by omega, by omega⟩

theorem empty_std :
    ((BaseRun.registers .empty).llCenter.standard.currentOdd).val.sites = oddTile [] ∧
      ((BaseRun.registers .empty).llCenter.standard.currentEven).val.sites = evenTile [] ∧
      ((BaseRun.registers .empty).llCenter.standard.retainedOdd).val.sites = (stateAt []).tOdd ∧
      ((BaseRun.registers .empty).llCenter.standard.retainedEven).val.sites = (stateAt []).tEven := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oddTile, childTiles_nil]
    exact stairOdd_llCenter_sites 3 ⟨by omega, by omega⟩
  · rw [evenTile, childTiles_nil]
    exact stairEven_llCenter_sites 3 ⟨by omega, by omega⟩
  · exact endpointZero_attach_llCenter_sites _
  · exact endpointOne_attach_llCenter_sites _

/-! ### The evaluator on the pure words -/

/-- The evaluator on `2^(e+1)` is the normalised base register of `BaseRun.twos e` (`evaluateNative_base`). -/
theorem evaluate_twos (e : ℕ) :
    evaluateNative (List.replicate (e + 1) Digit.two) = .ok (BaseRun.registers (.twos e)).llCenter :=
  evaluateNative_base (.twos e)

/-- The evaluator on `3^(e+1)` is the normalised base register of `BaseRun.threes e`. -/
theorem evaluate_threes (e : ℕ) :
    evaluateNative (List.replicate (e + 1) Digit.three) = .ok (BaseRun.registers (.threes e)).llCenter :=
  evaluateNative_base (.threes e)

/-- The evaluator on the empty word is the normalised base register of `BaseRun.empty`. -/
theorem evaluate_empty : evaluateNative [] = .ok (BaseRun.registers .empty).llCenter :=
  evaluateNative_base .empty

end FLatticePaper.Tiles.BaseRegistersTeX
