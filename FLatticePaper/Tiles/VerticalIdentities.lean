import FLatticePaper.Tiles.VLinVertical
import FLatticePaper.Tiles.CornerPositions

/-! The vertical instance identities: the Moreover strings are the surgical vertical strings.

* `zoForwardV_eq`: the forward vertical zero-one string of `w` is `vStringAt w 0`.
* `zoReversedStackedV_eq`: the reversed stacked vertical string of `w` is `vRevStringAt w.reverse (1,1)`
  (`verticalStackShift = (-1,-1)`).
* `vertical_B_eq`: the bottom-right corner `B = lastPosOf (hStringAt wh 0)` is `almostV1 (oddBottom w) - (1,1)`
  (`CornerPositions.lastPos_hWordOf_false`). -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StringBridge

theorem stepOf_vert_fwd (a b : Letter) : stepOf Orientation.vertical false a b = vOffset b := by
  cases b <;> rfl

theorem stepOf_vert_rev (a b : Letter) : stepOf Orientation.vertical true a b = vRevOffset a b := by
  cases a <;> cases b <;> rfl

theorem vStringAt_add (w : BinaryWord) (c e : GInt) :
    vStringAt w (c + e) = (vStringAt w c).map (fun p => (p.1, p.2 + e)) := by
  unfold vStringAt
  have hs : ∀ (L : List GInt) (c : GInt),
      List.scanl (· + ·) (c + e) L = (List.scanl (· + ·) c L).map (· + e) := by
    intro L
    induction L with
    | nil => intro c; simp
    | cons x L' ih =>
      intro c
      simp only [List.scanl_cons, List.map_cons]
      congr 1
      rw [show c + e + x = c + x + e by abel]
      exact ih (c + x)
  rw [hs, List.zip_map_right]
  congr 1

theorem vFwd_hL (u : BinaryWord) (k : ℕ) (hk : k + 1 < u.length) :
    (u.tail.map vOffset).getD k 0 = vOffset (u.getD (k + 1) Letter.p) := by
  have h1 : k < (u.tail.map vOffset).length := by
    simp
    omega
  rw [List.getD_eq_getElem _ _ h1]
  simp only [List.getElem_map, List.getElem_tail]
  rw [List.getD_eq_getElem _ _ (by omega)]

theorem vFwd_pos_gen (u : BinaryWord) (c : GInt) : ∀ k, k < u.length →
    (List.scanl (· + ·) c (u.tail.map vOffset)).getD k 0 =
      c + posF Orientation.vertical false (fun j => u.getD j Letter.p) k := by
  intro k
  induction k with
  | zero => intro _; simp [posF]
  | succ k ih =>
    intro hk
    rw [scanl_getD_succ_gen _ c k (by simp; omega), ih (by omega), vFwd_hL u k hk]
    simp only [posF, stepOf_vert_fwd]
    abel

theorem zoForwardV_eq (w : BinaryWord) : zoForwardV (lettersOf w false) w.length = vStringAt w 0 := by
  apply List.ext_getElem
  · rw [vStringAt_length]
    simp [zoForwardV]
  · intro k h1 h2
    have hk : k < w.length := by
      simp [zoForwardV] at h1
      omega
    have hk2 : k < (List.scanl (· + ·) (0 : GInt) (w.tail.map vOffset)).length := by
      simp
      omega
    have e2 := vFwd_pos_gen w 0 k hk
    rw [zero_add] at e2
    rw [List.getD_eq_getElem _ _ hk2] at e2
    have e1 : lettersOf w false k = w.getD k Letter.p := rfl
    unfold zoForwardV vStringAt
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
    rw [e2, e1, List.getD_eq_getElem _ _ hk]
    rfl

/-- The position step of the reversed vertical string. -/
theorem vRev_zip_getD (u : BinaryWord) (k : ℕ) (hk : k + 1 < u.length) :
    ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2).getD k 0 =
      vRevOffset (u.getD k Letter.p) (u.getD (k + 1) Letter.p) := by
  have h1 : k < (u.zip u.tail).length := by simp; omega
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp only [List.getElem_map, List.getElem_zip, List.getElem_tail]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem vRev_pos_gen (u : BinaryWord) (c : GInt) : ∀ k, k < u.length →
    (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD k 0 =
      c + posF Orientation.vertical true (fun j => u.getD j Letter.p) k := by
  intro k
  induction k with
  | zero => intro _; simp [posF]
  | succ k ih =>
    intro hk
    rw [scanl_getD_succ_gen _ c k (by simp; omega), ih (by omega), vRev_zip_getD u k hk]
    simp only [posF, stepOf_vert_rev]
    abel

theorem vert_stack_shift (p : GInt) : p - verticalStackShift = (1, 1) + p := by
  unfold verticalStackShift
  apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> omega

theorem zoReversedStackedV_eq (w : BinaryWord) :
    zoReversedStackedV (lettersOf w true) w.length = vRevStringAt w.reverse (1, 1) := by
  apply List.ext_getElem
  · rw [vRevStringAt_length]
    simp [zoReversedStackedV]
  · intro k h1 h2
    have hk : k < w.length := by
      simp [zoReversedStackedV] at h1
      omega
    have hkR : k < w.reverse.length := by simpa using hk
    have hk2 : k < (List.scanl (· + ·) (1, 1)
        ((w.reverse.zip w.reverse.tail).map fun ab => vRevOffset ab.1 ab.2)).length := by
      simp only [List.length_scanl, List.length_map, List.length_zip, List.length_tail, List.length_reverse]
      omega
    have e2 := vRev_pos_gen w.reverse (1, 1) k hkR
    rw [List.getD_eq_getElem _ _ hk2] at e2
    have e1 : lettersOf w true k = w.reverse.getD k Letter.p := rfl
    unfold zoReversedStackedV vRevStringAt
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
    rw [e2, e1, List.getD_eq_getElem _ _ hkR, vert_stack_shift]
    rfl

/-- The bottom-right corner of the horizontal bottom string, in the vertical frame `v = almostV1 - (1,1)`. -/
theorem vertical_B_eq (w : FLatticePaper.Farey.Word) :
    lastPosOf (hStringAt (hWordOf w false) 0) = almostV₁ (oddBottom w) + (-1, -1) := by
  have key : lastPosOf (hStringAt (hWordOf w false) 0) = almostV₁ (oddBottom w) - (1, 1) :=
    FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_false w
  rw [key, sub_eq_add_neg]
  rfl

end FLatticePaper.Tiles
