import FLatticePaper.Tiles.HorizontalStepOne
import FLatticePaper.Tiles.VerticalZeroOne

/-! # The boundary-string formula of Step 1 for vertical strings

Surgical edition 274ad18, Step 1 of `lemma:weak_standard_odometer_properties`, the formula for vertical zero-one boundary strings:
if partial odometers respect a vertical (resp. reversed vertical) string, then there are one affine factor `a_0` and one constant
`K` with `o_i(x) + h_0(x) - a_0^T x = v_i^±(x - c(T_i)) + K` on every tile `T_i` (here with `h_0` read at `x` itself; the parity
hypothesis on the position of the first tile is the text's condition that the positions relative to `c_0` have even coordinate
sum).

The tile identities are those of `VerticalZeroOne` (w1): the canonical identity of each tile (`tile_identity`), the step of the
affine factor (`a_step_eq`), and the step of the constant at an overlap point (`b_overlap`) or across a `q q` step (`b_adj`). This
file carries them along the string by induction (`vertical_invariant`) and states the formula for the forward and the reversed
vertical strings (`vertical_formula`, `reversed_vertical_formula`). -/

namespace FLatticePaper.Tiles.VerticalStepOne

open FLatticePaper.Tiles
open FLatticePaper.Tiles.HorizontalStepOne (ConsecOK chain'_getD)

/-- The placed tiles of a vertical string from the position `c` (no enlarged tiles). -/
def vAux (rev : Bool) : BinaryWord → GInt → List (ZTile × GInt)
  | [], _ => []
  | [a], c => [(letterZTile a, c)]
  | a :: b :: rest, c => (letterZTile a, c) :: vAux rev (b :: rest) (c + stepV rev a b)

theorem vStringAt_eq (w : BinaryWord) (c : GInt) : vStringAt w c = vAux false w c := by
  induction w generalizing c with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have := ih (c + vOffset b)
      unfold vStringAt at this ⊢
      have e : vAux false (a :: b :: rest') c = (letterZTile a, c) :: vAux false (b :: rest') (c + vOffset b) := rfl
      rw [e, ← this]
      simp only [List.map_cons, List.tail_cons, List.scanl_cons, List.zip_cons_cons]

theorem vRevStringAt_eq (u : BinaryWord) (c : GInt) : vRevStringAt u c = vAux true u c := by
  induction u generalizing c with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have := ih (c + vRevOffset a b)
      unfold vRevStringAt at this ⊢
      have e : vAux true (a :: b :: rest') c = (letterZTile a, c) :: vAux true (b :: rest') (c + vRevOffset a b) := rfl
      rw [e, ← this]
      simp only [List.map_cons, List.tail_cons, List.scanl_cons, List.zip_cons_cons]

/-- Two consecutive tiles of a vertical string: zero or one tiles, and the step of their letters. -/
def LocalV (rev : Bool) (x y : ZTile × GInt) : Prop :=
  (∃ l, x.1 = letterZTile l) ∧ (∃ l', y.1 = letterZTile l') ∧
    y.2 - x.2 = stepV rev (zTileLetter x.1) (zTileLetter y.1)

theorem vAux_chain (rev : Bool) : ∀ (w : BinaryWord) (c : GInt), ConsecOK (LocalV rev) (vAux rev w c) := by
  intro w
  induction w with
  | nil => intro c; trivial
  | cons a rest ih =>
    intro c
    cases rest with
    | nil => trivial
    | cons b rest' =>
      have hc := ih (c + stepV rev a b)
      have hh : ∃ tl, vAux rev (b :: rest') (c + stepV rev a b) = (letterZTile b, c + stepV rev a b) :: tl := by
        cases rest' <;> exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hh
      show ConsecOK (LocalV rev) ((letterZTile a, c) :: vAux rev (b :: rest') (c + stepV rev a b))
      rw [htl] at hc ⊢
      refine ⟨⟨⟨a, rfl⟩, ⟨b, rfl⟩, ?_⟩, hc⟩
      simp only [vz_letter]
      abel

theorem vAux_head (rev : Bool) (a : Letter) (rest : BinaryWord) (c : GInt) :
    (vAux rev (a :: rest) c).getD 0 (ZTile.zero, 0) = (letterZTile a, c) := by
  cases rest <;> rfl

/-- The invariant of a vertical family along its string: the affine factor is `a_0 + Acl`, the constant `b + Cl = K`, and the
canonical-relative position has even coordinate sum. -/
def VInv (F : PTFamily) (rev : Bool) (a0 : GInt) (K : ℤ) (k : ℕ) : Prop :=
  ((((F.tile k).2 - cstarV (zTileLetter (F.tile k).1) rev).1 +
      ((F.tile k).2 - cstarV (zTileLetter (F.tile k).1) rev).2) % 2 = 0) ∧
    F.a k = a0 + Acl (zTileLetter (F.tile k).1) rev ((F.tile k).2 - cstarV (zTileLetter (F.tile k).1) rev) ∧
    F.b k + Cl (zTileLetter (F.tile k).1) rev ((F.tile k).2 - cstarV (zTileLetter (F.tile k).1) rev) = K

/-- The step of the invariant from tile `k` to tile `k + 1`. -/
theorem vinv_step (F : PTFamily) (rev : Bool) (a0 : GInt) (K : ℤ) (k : ℕ) (hk : k + 1 < F.n)
    (hR : F.Respects .vertical rev)
    (hW : ∀ x ∈ F.dom k, x ∈ F.dom (k + 1) → F.odo k x = F.odo (k + 1) x)
    (l l' : Letter) (hTk : (F.tile k).1 = letterZTile l) (hTk1 : (F.tile (k + 1)).1 = letterZTile l')
    (hpos : (F.tile (k + 1)).2 = (F.tile k).2 + stepV rev l l') (h : VInv F rev a0 K k) : VInv F rev a0 K (k + 1) := by
  obtain ⟨hd, ha, hb⟩ := h
  rw [hTk, vz_letter] at hd ha hb
  have ha' := a_step_eq F rev k l l' a0 hk hR hTk hTk1 hpos hd ha
  have hpar : ((((F.tile (k + 1)).2 - cstarV l' rev).1 + ((F.tile (k + 1)).2 - cstarV l' rev).2) % 2 = 0) := by
    have hs := stepV_parity l l' rev
    rw [hpos]
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at hs hd ⊢
    omega
  refine ⟨by rw [hTk1, vz_letter]; exact hpar, by rw [hTk1, vz_letter]; exact ha', ?_⟩
  rw [hTk1, vz_letter]
  cases l <;> cases l' <;> cases rev
  · exact b_overlap F false k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 1) (by decide) (by decide) (by decide) (by decide)
  · exact b_overlap F true k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 1) (by decide) (by decide) (by decide) (by decide)
  · exact b_overlap F false k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 2) (by decide) (by decide) (by decide) (by decide)
  · exact b_overlap F true k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 2) (by decide) (by decide) (by decide) (by decide)
  · exact b_overlap F false k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 1) (by decide) (by decide) (by decide) (by decide)
  · exact b_overlap F true k _ _ a0 K hTk hTk1 hpos hd ha hb ha' hW (0, 1) (by decide) (by decide) (by decide) (by decide)
  · exact b_adj F false k a0 K hk hR hTk hTk1 hpos hd ha hb ha'
  · exact b_adj F true k a0 K hk hR hTk hTk1 hpos hd ha hb ha'

/-- The invariant along the whole string, from the first tile. -/
theorem vertical_invariant (F : PTFamily) (rev : Bool) (hR : F.Respects .vertical rev)
    (hW : ∀ k, k + 1 < F.n → ∀ x ∈ F.dom k, x ∈ F.dom (k + 1) → F.odo k x = F.odo (k + 1) x)
    (hL : ConsecOK (LocalV rev) F.ts)
    (hd0 : (((F.tile 0).2 - cstarV (zTileLetter (F.tile 0).1) rev).1 +
      ((F.tile 0).2 - cstarV (zTileLetter (F.tile 0).1) rev).2) % 2 = 0) :
    ∃ (a0 : GInt) (K : ℤ), ∀ k < F.n, VInv F rev a0 K k := by
  refine ⟨F.a 0 - Acl (zTileLetter (F.tile 0).1) rev ((F.tile 0).2 - cstarV (zTileLetter (F.tile 0).1) rev),
    F.b 0 + Cl (zTileLetter (F.tile 0).1) rev ((F.tile 0).2 - cstarV (zTileLetter (F.tile 0).1) rev), ?_⟩
  intro k
  induction k with
  | zero => intro _; exact ⟨hd0, by abel, rfl⟩
  | succ k ih =>
    intro hk
    have hloc := chain'_getD (ZTile.zero, (0 : GInt)) hL k hk
    obtain ⟨⟨l, hl⟩, ⟨l', hl'⟩, hs⟩ := hloc
    have hTk : (F.tile k).1 = letterZTile l := hl
    have hTk1 : (F.tile (k + 1)).1 = letterZTile l' := hl'
    have hpos : (F.tile (k + 1)).2 = (F.tile k).2 + stepV rev l l' := by
      have : (F.tile (k + 1)).2 - (F.tile k).2 = stepV rev l l' := by
        have e : (F.tile (k + 1)).2 - (F.tile k).2 = stepV rev (zTileLetter (F.tile k).1) (zTileLetter (F.tile (k + 1)).1) :=
          hs
        rw [e, hTk, hTk1, vz_letter, vz_letter]
      rw [← this]; abel
    exact vinv_step F rev _ _ k hk hR (hW k hk) l l' hTk hTk1 hpos (ih (by omega))

/-- Step 1 for a vertical string whose tiles are zero and one tiles with the letter steps: an odometer respecting the string
satisfies `S(x) + h_0(x) - a_0^T x = v^±(x - c(T_k)) + K` on every tile, with one `a_0` and one `K`. -/
theorem vertical_formula_gen (rev : Bool) (L : List (ZTile × GInt)) (hL : ConsecOK (LocalV rev) L) (S : GInt → ℤ)
    (hR : RespectsTiles .vertical rev L S)
    (hd0 : (((L.getD 0 (ZTile.zero, 0)).2 - cstarV (zTileLetter (L.getD 0 (ZTile.zero, 0)).1) rev).1 +
      ((L.getD 0 (ZTile.zero, 0)).2 - cstarV (zTileLetter (L.getD 0 (ZTile.zero, 0)).1) rev).2) % 2 = 0)
    (htype : ∀ k < L.length, ∃ l, (L.getD k (ZTile.zero, 0)).1 = letterZTile l) :
    ∃ (a0 : GInt) (K : ℤ), ∀ k < L.length, ∀ u ∈ tileShape (L.getD k (ZTile.zero, 0)).1,
      S ((L.getD k (ZTile.zero, 0)).2 + u) + zoH0 ((L.getD k (ZTile.zero, 0)).2 + u) -
          (a0.1 * ((L.getD k (ZTile.zero, 0)).2 + u).1 + a0.2 * ((L.getD k (ZTile.zero, 0)).2 + u).2) =
        vV (zTileLetter (L.getD k (ZTile.zero, 0)).1) rev u + K := by
  obtain ⟨F, hF, hFS, hFR⟩ := hR
  have htile : ∀ k, F.tile k = L.getD k (ZTile.zero, 0) := fun k => by unfold PTFamily.tile; rw [hF]
  have hn : F.n = L.length := by unfold PTFamily.n; rw [hF]
  have hW : ∀ k, k + 1 < F.n → ∀ x ∈ F.dom k, x ∈ F.dom (k + 1) → F.odo k x = F.odo (k + 1) x := by
    intro k hk x hx hy
    rw [← hFS k (by omega) x hx, ← hFS (k + 1) hk x hy]
  obtain ⟨a0, K, hinv⟩ := vertical_invariant F rev hFR hW (by rw [hF]; exact hL) (by rw [htile]; exact hd0)
  refine ⟨a0, K, fun k hk u hu => ?_⟩
  obtain ⟨l, hl⟩ := htype k hk
  have hkF : k < F.n := by rw [hn]; exact hk
  obtain ⟨hd, ha, hb⟩ := hinv k hkF
  have hT : (F.tile k).1 = letterZTile l := by rw [htile]; exact hl
  rw [hT, vz_letter] at hd ha hb
  have hu' : u ∈ tileShape (letterZTile l) := by rw [← hl]; exact hu
  have key := inv_point F rev k l hT a0 K ha hb hd u hu'
  have hmem : (F.tile k).2 + u ∈ F.dom k := by
    unfold PTFamily.dom
    rw [chain_mem_map_add_iff]
    simpa [hT] using hu'
  rw [← htile k, hFS k hkF _ hmem, hT, vz_letter]
  exact key

/-- Step 1 for the forward vertical string `w_v` at `c`. -/
theorem vertical_formula (w : BinaryWord) (c : GInt) (S : GInt → ℤ) (hw : w ≠ [])
    (hR : RespectsTiles .vertical false (vStringAt w c) S)
    (hd0 : ((c - cstarV (w.headD Letter.p) false).1 + (c - cstarV (w.headD Letter.p) false).2) % 2 = 0) :
    ∃ (a0 : GInt) (K : ℤ), ∀ k < (vStringAt w c).length, ∀ u ∈ tileShape ((vStringAt w c).getD k (ZTile.zero, 0)).1,
      S (((vStringAt w c).getD k (ZTile.zero, 0)).2 + u) + zoH0 (((vStringAt w c).getD k (ZTile.zero, 0)).2 + u) -
          (a0.1 * (((vStringAt w c).getD k (ZTile.zero, 0)).2 + u).1 +
            a0.2 * (((vStringAt w c).getD k (ZTile.zero, 0)).2 + u).2) =
        vV (zTileLetter ((vStringAt w c).getD k (ZTile.zero, 0)).1) false u + K := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, w = a :: rest := by
    cases w with
    | nil => exact absurd rfl hw
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hL : ConsecOK (LocalV false) (vStringAt (a :: rest) c) := by rw [vStringAt_eq]; exact vAux_chain false _ c
  refine vertical_formula_gen false _ hL S hR ?_ ?_
  · rw [vStringAt_eq, vAux_head, vz_letter]; simpa using hd0
  · intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [vStringAt_eq, vAux_head]; exact ⟨a, rfl⟩
    · obtain ⟨-, hl', -⟩ := chain'_getD (ZTile.zero, (0 : GInt)) hL (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hl'
      exact hl'

/-- Step 1 for the reversed vertical string `u` at `c`. -/
theorem reversed_vertical_formula (w : BinaryWord) (c : GInt) (S : GInt → ℤ) (hw : w ≠ [])
    (hR : RespectsTiles .vertical true (vRevStringAt w c) S)
    (hd0 : ((c - cstarV (w.headD Letter.p) true).1 + (c - cstarV (w.headD Letter.p) true).2) % 2 = 0) :
    ∃ (a0 : GInt) (K : ℤ), ∀ k < (vRevStringAt w c).length, ∀ u ∈ tileShape ((vRevStringAt w c).getD k (ZTile.zero, 0)).1,
      S (((vRevStringAt w c).getD k (ZTile.zero, 0)).2 + u) + zoH0 (((vRevStringAt w c).getD k (ZTile.zero, 0)).2 + u) -
          (a0.1 * (((vRevStringAt w c).getD k (ZTile.zero, 0)).2 + u).1 +
            a0.2 * (((vRevStringAt w c).getD k (ZTile.zero, 0)).2 + u).2) =
        vV (zTileLetter ((vRevStringAt w c).getD k (ZTile.zero, 0)).1) true u + K := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, w = a :: rest := by
    cases w with
    | nil => exact absurd rfl hw
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hL : ConsecOK (LocalV true) (vRevStringAt (a :: rest) c) := by rw [vRevStringAt_eq]; exact vAux_chain true _ c
  refine vertical_formula_gen true _ hL S hR ?_ ?_
  · rw [vRevStringAt_eq, vAux_head, vz_letter]; simpa using hd0
  · intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [vRevStringAt_eq, vAux_head]; exact ⟨a, rfl⟩
    · obtain ⟨-, hl', -⟩ := chain'_getD (ZTile.zero, (0 : GInt)) hL (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hl'
      exact hl'

end FLatticePaper.Tiles.VerticalStepOne
