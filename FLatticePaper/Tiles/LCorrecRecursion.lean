import FLatticePaper.Tiles.LCorrecProps

/-! # The recursion of the L-corrections in the length of the trailing run

Surgical edition 274ad18, proof of `lemma:l_correc_properties` (2): for `w = w_1 s 3^k` with `k ≥ 1` and `q_0'` the even child of
`w` without its last letter, the elongated correction satisfies
`T^{L,+}(q_0) = T(p_1) ∪ (T^{L,+}(q_0') + v_{p_1,1}) ∪ (T̂(p_1) ∪ T̂(p_1) + v_{p_1,2}) + ((k+1) v_{p_1,1} + K_3 + (2k+1) v_{p_1,2})`
in case `10`. In the frame of the first stem the cells of an L-correction depend only on `w_1 s`, `k`, the parity of `W_1`, the sign
and the elongation (`evenLRel`, `oddLRel`), and they satisfy, in every case and for both elongations, the recursion: the first stem,
the correction of `k - 1` translated by `K_1`, and the last two heads (`evenLRel_succ`, `oddLRel_succ`). `evenLRel` and
`oddLRel` are written from the same tables and offsets as `evenLPieces` and `oddLPieces`, with the initial offset removed; the
equality of `LCorrecProps.evenLCells` with the translate of `evenLRel` is not proved here. With `K_1 = v_{p_1,1}` and
`K_4 = v_{p_1,2}` in case `10` this is the displayed identity (it is an identity for the definition read with the `c`-relations,
`k K_1 + K_2`; E40 concerns the literal reading). -/

namespace FLatticePaper.Tiles.LCorrecRecursion

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.LCorrecProps
open FLatticePaper.Tiles.SurgicalAlt (AltCoeff coeffOff)
open FLatticePaper.Tiles.Standard (oddTile evenTile shift Tile)

/-- The tiles of the parents of `pre`, as in `evenLCells`. -/
def stemE (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
  (regsAt pre).1 true).dom
/-- The bridge of the even correction. -/
def bridgeE (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
  (regsAt pre).2 false).dom
/-- The head of the even correction (the alternate odd register of `pre`). -/
def headE (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u))
  (regsAt pre).1 true).dom

/-- The cells of the even L-correction in the frame of its first stem: stems at `j K_1`, the bridge (or the copy of `T^d_{1/1}`)
at `k K_1 + K_2`, the heads at `k K_1 + K_2 + K_3 + i K_4`. -/
def evenLRel (pre : Word) (k : ℕ) (o plus elong : Bool) : Finset Site :=
  let s2 : Bool := decide (pre.getLast? = some Digit.two)
  let K := evenKCoeff o plus s2
  let double : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let case01 : Bool := !o && !plus
  let cB : AltCoeff := (k : ℤ) • K.1 + K.2.1
  let nh := 2 * (k + 1) - (if elong then 0 else 1)
  (Finset.range (k + 1)).biUnion (fun j => (stemE pre).image (· + altOff pre ((j : ℤ) • K.1))) ∪
    (if double && case01 then ∅ else (bridgeE pre).image (· + altOff pre cB)) ∪
    (if double then (tileShape ZTile.oneD).toFinset.image (· + (altOff pre cB + ((1 : ℤ), (1 : ℤ)))) else ∅) ∪
    (Finset.range nh).biUnion (fun i => (headE pre).image (· + altOff pre (cB + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)))

theorem altOff_add (w : Word) (a b : AltCoeff) : altOff w (a + b) = altOff w a + altOff w b := by
  unfold altOff coeffOff
  ext <;> simp <;> ring

theorem altOff_smul (w : Word) (m : ℤ) (a : AltCoeff) : altOff w (m • a) = m • altOff w a := by
  unfold altOff coeffOff
  ext <;> simp <;> ring

theorem img_add (s : Finset Site) (a b : Site) : (s.image (· + a)).image (· + b) = s.image (· + (a + b)) := by
  rw [Finset.image_image]
  congr 1
  funext y
  simp [add_assoc]

/-- The stems: the first one and the others translated by `K_1`. -/
theorem stems_succ (T : Finset Site) (off : ℕ → Site) (K : Site) (hoff : ∀ j, off (j + 1) = off j + K) (h0 : off 0 = 0)
    (k : ℕ) :
    (Finset.range (k + 2)).biUnion (fun j => T.image (· + off j)) =
      T ∪ ((Finset.range (k + 1)).biUnion (fun j => T.image (· + off j))).image (· + K) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, y, hy, rfl⟩
    cases j with
    | zero => left; rw [h0, add_zero]; exact hy
    | succ j => right; exact ⟨y + off j, ⟨j, by omega, y, hy, rfl⟩, by rw [hoff, add_assoc]⟩
  · rintro (hx | ⟨z, ⟨j, hj, y, hy, rfl⟩, rfl⟩)
    · exact ⟨0, by omega, x, hx, by rw [h0, add_zero]⟩
    · exact ⟨j + 1, by omega, y, hy, by rw [hoff, add_assoc]⟩

/-- The heads: the first `n` translated by `K_1`, and two more. -/
theorem heads_succ (T : Finset Site) (off : ℕ → Site) (off' : ℕ → Site) (K : Site) (hoff : ∀ i, off' i = off i + K)
    (n : ℕ) :
    (Finset.range (n + 2)).biUnion (fun i => T.image (· + off' i)) =
      ((Finset.range n).biUnion (fun i => T.image (· + off i))).image (· + K) ∪
        (Finset.range 2).biUnion (fun i => T.image (· + off' (n + i))) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    by_cases h : i < n
    · left; exact ⟨y + off i, ⟨i, h, y, hy, rfl⟩, by rw [hoff, add_assoc]⟩
    · right; exact ⟨i - n, by omega, y, hy, by rw [show n + (i - n) = i by omega]⟩
  · rintro (⟨z, ⟨i, hi, y, hy, rfl⟩, rfl⟩ | ⟨i, hi, y, hy, rfl⟩)
    · exact ⟨i, by omega, y, hy, by rw [hoff, add_assoc]⟩
    · exact ⟨n + i, by omega, y, hy, rfl⟩

/-- The recursion of the even L-correction in `k`: the first stem, the correction of `k` translated by `K_1`, and the two last heads. -/
theorem evenLRel_succ (pre : Word) (k : ℕ) (o plus elong : Bool) :
    evenLRel pre (k + 1) o plus elong =
      stemE pre ∪ (evenLRel pre k o plus elong).image (· + altOff pre (evenKCoeff o plus
        (decide (pre.getLast? = some Digit.two))).1) ∪
      (Finset.range 2).biUnion (fun i => (headE pre).image (· + altOff pre
        ((((k + 1 : ℕ) : ℤ)) • (evenKCoeff o plus (decide (pre.getLast? = some Digit.two))).1 +
          (evenKCoeff o plus (decide (pre.getLast? = some Digit.two))).2.1 +
          (evenKCoeff o plus (decide (pre.getLast? = some Digit.two))).2.2.1 +
          (((2 * (k + 1) - (if elong then 0 else 1) + i : ℕ) : ℤ) + 1) •
            (evenKCoeff o plus (decide (pre.getLast? = some Digit.two))).2.2.2))) := by
  set K := evenKCoeff o plus (decide (pre.getLast? = some Digit.two)) with hK
  have hsm : ∀ (j : ℕ), altOff pre (((j + 1 : ℕ) : ℤ) • K.1) = altOff pre ((j : ℤ) • K.1) + altOff pre K.1 := by
    intro j; rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]
  have hcB : altOff pre (((k + 1 : ℕ) : ℤ) • K.1 + K.2.1) = altOff pre ((k : ℤ) • K.1 + K.2.1) + altOff pre K.1 := by
    rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]; abel
  have hst := stems_succ (stemE pre) (fun j => altOff pre ((j : ℤ) • K.1)) (altOff pre K.1) hsm
    (by simp [altOff, coeffOff]) k
  have hnh : 2 * (k + 1 + 1) - (if elong then 0 else 1) = (2 * (k + 1) - (if elong then 0 else 1)) + 2 := by
    split_ifs <;> omega
  have hhd := heads_succ (headE pre)
    (fun i => altOff pre ((k : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2))
    (fun i => altOff pre ((((k + 1 : ℕ) : ℤ)) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)) (altOff pre K.1)
    (by intro i; rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]; abel)
    (2 * (k + 1) - (if elong then 0 else 1))
  simp only [evenLRel, ← hK]
  rw [hst, hnh, hhd]
  simp only [Finset.image_union]
  rw [hcB]
  split_ifs with h1 h2 <;> simp only [Finset.image_empty, img_add, Finset.union_empty] <;>
    simp only [add_assoc, Finset.union_assoc] <;> ac_rfl

/-! ### The odd L-corrections -/

/-- The stems of the odd correction (the even register of `pre`). -/
def stemO (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
  (regsAt pre).2 false).dom
/-- The bridge of the odd correction (the odd register of `pre`). -/
def bridgeO (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
  (regsAt pre).1 true).dom
/-- The head of the odd correction (the alternate even register of `pre`). -/
def headO (pre : Word) : Finset Site := (regOdo cellData (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u))
  (regsAt pre).2 false).dom

/-- The cells of the odd L-correction in the frame of its first stem. -/
def oddLRel (pre : Word) (k : ℕ) (o plus elong : Bool) : Finset Site :=
  let K := oddKCoeff o plus
  let triple : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.three))
  let cB : AltCoeff := (k : ℤ) • K.1 + K.2.1
  let nh := 2 * (k + 1) - (if elong then 0 else 1)
  (Finset.range (k + 1)).biUnion (fun j => (stemO pre).image (· + altOff pre ((j : ℤ) • K.1))) ∪
    (bridgeO pre).image (· + (altOff pre cB + LCorrections.oddBridgeShift triple o plus)) ∪
    (Finset.range nh).biUnion (fun i => (headO pre).image (· + altOff pre (cB + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)))

/-- The recursion of the odd L-correction in `k`. -/
theorem oddLRel_succ (pre : Word) (k : ℕ) (o plus elong : Bool) :
    oddLRel pre (k + 1) o plus elong =
      stemO pre ∪ (oddLRel pre k o plus elong).image (· + altOff pre (oddKCoeff o plus).1) ∪
      (Finset.range 2).biUnion (fun i => (headO pre).image (· + altOff pre
        ((((k + 1 : ℕ) : ℤ)) • (oddKCoeff o plus).1 + (oddKCoeff o plus).2.1 + (oddKCoeff o plus).2.2.1 +
          (((2 * (k + 1) - (if elong then 0 else 1) + i : ℕ) : ℤ) + 1) • (oddKCoeff o plus).2.2.2))) := by
  set K := oddKCoeff o plus with hK
  have hsm : ∀ (j : ℕ), altOff pre (((j + 1 : ℕ) : ℤ) • K.1) = altOff pre ((j : ℤ) • K.1) + altOff pre K.1 := by
    intro j; rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]
  have hcB : altOff pre (((k + 1 : ℕ) : ℤ) • K.1 + K.2.1) = altOff pre ((k : ℤ) • K.1 + K.2.1) + altOff pre K.1 := by
    rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]; abel
  have hst := stems_succ (stemO pre) (fun j => altOff pre ((j : ℤ) • K.1)) (altOff pre K.1) hsm
    (by simp [altOff, coeffOff]) k
  have hnh : 2 * (k + 1 + 1) - (if elong then 0 else 1) = (2 * (k + 1) - (if elong then 0 else 1)) + 2 := by
    split_ifs <;> omega
  have hhd := heads_succ (headO pre)
    (fun i => altOff pre ((k : ℤ) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2))
    (fun i => altOff pre ((((k + 1 : ℕ) : ℤ)) • K.1 + K.2.1 + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2)) (altOff pre K.1)
    (by intro i; rw [← altOff_add]; congr 1; push_cast; rw [add_smul, one_smul]; abel)
    (2 * (k + 1) - (if elong then 0 else 1))
  simp only [oddLRel, ← hK]
  rw [hst, hnh, hhd]
  simp only [Finset.image_union]
  rw [hcB, img_add]
  simp only [add_assoc, Finset.union_assoc]
  have e : altOff pre ((k : ℤ) • K.1 + K.2.1) + (altOff pre K.1 +
      LCorrections.oddBridgeShift (!pre.isEmpty && pre.all (fun d => decide (d = Digit.three))) o plus) =
      altOff pre ((k : ℤ) • K.1 + K.2.1) + (LCorrections.oddBridgeShift
        (!pre.isEmpty && pre.all (fun d => decide (d = Digit.three))) o plus + altOff pre K.1) := by abel
  rw [e]

end FLatticePaper.Tiles.LCorrecRecursion
