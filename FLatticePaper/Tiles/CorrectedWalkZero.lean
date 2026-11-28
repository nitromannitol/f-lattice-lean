import FLatticePaper.Tiles.TileStepAssembly

/-! # Condition (C) from constants with which the pieces agree

If the pieces of a decomposition agree with constants `κ` on every overlap (outside the exceptional points), then on every edge of
the overlap graph the overlap constant is `κ j - κ i`, so the sum along a closed walk telescopes to `0`: `TileStepAssembly.WalkZero`.
This is the form in which condition (C) is proved for the corrected tile decompositions, by exhibiting the constants. -/

namespace FLatticePaper.Tiles.CorrectedWalkZero

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointGlue

/-- **Condition (C) from the edge constants.** If, for every choice of overlap constants (the differences of the two pieces on
each overlap), the constant of every edge of the overlap graph is `κ j - κ i`, then the constants sum to zero along every closed
walk. Inside the hypothesis all overlap differences are constant, so one edge can be read through a point it shares with two
other edges. -/
theorem walkZero_of_edges (ps : List Piece) (κ : ℕ → ℤ)
    (h : ∀ off : Fin ps.length → Fin ps.length → ℤ,
      (∀ i j, ∀ x ∈ goodPart ps i ∩ goodPart ps j, pieceVal (ps.get i) x.1 - pieceVal (ps.get j) x.1 = off i j) →
      ∀ i j, (overlapGraph (goodPart ps)).Adj i j → off i j = κ j.1 - κ i.1) : TileStepAssembly.WalkZero ps := by
  intro off hoff i walk
  suffices h' : ∀ (a b : Fin ps.length) (p : (overlapGraph (goodPart ps)).Walk a b), walkSum off p = κ b.1 - κ a.1 by
    simpa using h' i i walk
  intro a b p
  induction p with
  | nil => simp [walkSum_nil]
  | @cons u v w hadj p ih =>
    rw [walkSum_cons, ih, h off hoff u v hadj]
    ring

/-- **Condition (C) from agreeing constants.** -/
theorem walkZero_of_agree (ps : List Piece) (κ : ℕ → ℤ) (hag : PiecesAgree ps κ) : TileStepAssembly.WalkZero ps := by
  refine walkZero_of_edges ps κ fun off hoff u v hadj => ?_
  obtain ⟨-, x, hx1, hx2⟩ := hadj
  have e1 := hoff u v x ⟨hx1, hx2⟩
  have e2 := hag u.1 v.1 (ps.get u) (ps.get v) (by simp) (by simp) x.1 hx1.1 hx2.1 hx1.2 hx2.2
  linarith

/-! ### Edges by witness points and by triple points -/

/-- The overlap constants of a decomposition: the difference of the two pieces on each overlap. -/
def OffMatch (ps : List Piece) (off : Fin ps.length → Fin ps.length → ℤ) : Prop :=
  ∀ i j, ∀ x ∈ goodPart ps i ∩ goodPart ps j, pieceVal (ps.get i) x.1 - pieceVal (ps.get j) x.1 = off i j

/-- The pieces `i` and `j` agree with the constants `κ` at every common point. -/
def AgreeAll (ps : List Piece) (κ : ℕ → ℤ) (i j : ℕ) : Prop :=
  ∀ p q, ps[i]? = some p → ps[j]? = some q →
    ∀ x ∈ p.placed, x ∈ q.placed → x ∉ p.exc → x ∉ q.exc → pieceVal p x + κ i = pieceVal q x + κ j

/-- One common point of the pieces `i` and `j` where they agree with the constants `κ`. -/
def EdgeWitness (ps : List Piece) (κ : ℕ → ℤ) (i j : ℕ) : Prop :=
  ∀ p q, ps[i]? = some p → ps[j]? = some q →
    ∃ x ∈ p.placed, x ∈ q.placed ∧ x ∉ p.exc ∧ x ∉ q.exc ∧ pieceVal p x + κ i = pieceVal q x + κ j

theorem mem_union_of {ps : List Piece} {i : ℕ} {p : Piece} (h : ps[i]? = some p) {x : ℤ × ℤ} (hx : x ∈ p.placed) :
    x ∈ pieceUnion ps := by
  have hm : p ∈ ps := List.mem_of_getElem? h
  clear h
  induction ps with
  | nil => simp at hm
  | cons a t ih =>
    simp only [pieceUnion, List.foldr_cons, Finset.mem_union]
    rcases List.mem_cons.mp hm with rfl | ht
    · exact Or.inl hx
    · exact Or.inr (ih ht)

theorem get_of {ps : List Piece} {i : ℕ} {p : Piece} (h : ps[i]? = some p) :
    ∃ hi : i < ps.length, ps.get ⟨i, hi⟩ = p := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hi, e⟩

/-- The overlap constant of two pieces is their difference at any common point. -/
theorem off_point {ps : List Piece} {off : Fin ps.length → Fin ps.length → ℤ} (hoff : OffMatch ps off)
    {i j : ℕ} {p q : Piece} (hp : ps[i]? = some p) (hq : ps[j]? = some q) {x : ℤ × ℤ} (hxp : x ∈ p.placed)
    (hxq : x ∈ q.placed) (hep : x ∉ p.exc) (heq : x ∉ q.exc) (hi : i < ps.length) (hj : j < ps.length) :
    off ⟨i, hi⟩ ⟨j, hj⟩ = pieceVal p x - pieceVal q x := by
  obtain ⟨hi', ep⟩ := get_of hp
  obtain ⟨hj', eq⟩ := get_of hq
  have := hoff ⟨i, hi⟩ ⟨j, hj⟩ ⟨x, mem_union_of hp hxp⟩
    ⟨by simp only [goodPart, Set.mem_setOf_eq]; rw [ep]; exact ⟨hxp, hep⟩,
     by simp only [goodPart, Set.mem_setOf_eq]; rw [eq]; exact ⟨hxq, heq⟩⟩
  rw [← this, ep, eq]

/-- An edge with a witness point has the constant `κ j - κ i`. -/
theorem off_of_witness {ps : List Piece} {off : Fin ps.length → Fin ps.length → ℤ} (hoff : OffMatch ps off)
    {κ : ℕ → ℤ} {i j : ℕ} (hw : EdgeWitness ps κ i j) (hi : i < ps.length) (hj : j < ps.length) :
    off ⟨i, hi⟩ ⟨j, hj⟩ = κ j - κ i := by
  obtain ⟨x, hxp, hxq, hep, heq, h⟩ := hw (ps.get ⟨i, hi⟩) (ps.get ⟨j, hj⟩) (by simp) (by simp)
  rw [off_point hoff (by simp) (by simp) hxp hxq hep heq hi hj]
  linarith

/-- A pair that agrees at every common point has the constant `κ j - κ i` as soon as it meets. -/
theorem off_of_agreeAll {ps : List Piece} {off : Fin ps.length → Fin ps.length → ℤ} (hoff : OffMatch ps off)
    {κ : ℕ → ℤ} {i j : ℕ} (ha : AgreeAll ps κ i j) (hi : i < ps.length) (hj : j < ps.length)
    (hx : ∃ x ∈ (ps.get ⟨i, hi⟩).placed, x ∈ (ps.get ⟨j, hj⟩).placed ∧ x ∉ (ps.get ⟨i, hi⟩).exc ∧
      x ∉ (ps.get ⟨j, hj⟩).exc) : off ⟨i, hi⟩ ⟨j, hj⟩ = κ j - κ i := by
  obtain ⟨x, hxp, hxq, hep, heq⟩ := hx
  have h := ha _ _ (by simp) (by simp) x hxp hxq hep heq
  rw [off_point hoff (by simp) (by simp) hxp hxq hep heq hi hj]
  linarith

/-- **An edge by a cross half-turn** (the text's `c = -c`). If the half-turn `z ↦ C - z` maps the odometer `Ls` of piece `i`
into the odometer `Lt` of piece `j` with constant `K`, and back with constant `K'` (both with the affine factor `-2a`), then the
overlap of the placed pieces is invariant under `z ↦ a_i + a_j + C - z`, and their overlap constant is determined by `K`, `K'`. -/
theorem off_of_halfTurn {ps : List Piece} {off : Fin ps.length → Fin ps.length → ℤ} (hoff : OffMatch ps off)
    {κ : ℕ → ℤ} {i j : ℕ} {Ls Lt : PartialOdometer} {a0 a3 s0 s3 C a : ℤ × ℤ} {K K' : ℤ}
    (hpi : ps[i]? = some (stdPiece Ls a0 s0)) (hpj : ps[j]? = some (stdPiece Lt a3 s3))
    (hK : ∀ y ∈ Ls.dom, C - y ∈ Lt.dom ∧ 2 * (Lt.val (C - y) - Ls.val y) = dotS (-(2 : ℤ) • a) y + K)
    (hK' : ∀ y ∈ Lt.dom, C - y ∈ Ls.dom ∧ 2 * (Ls.val (C - y) - Lt.val y) = dotS (-(2 : ℤ) • a) y + K')
    (halg : 4 * (κ j - κ i) = 2 * dotS (s0 - s3) (a0 + a3 + C) + 2 * dotS a (a3 - a0) + K' - K)
    (hi : i < ps.length) (hj : j < ps.length)
    (hx : ∃ x ∈ (ps.get ⟨i, hi⟩).placed, x ∈ (ps.get ⟨j, hj⟩).placed ∧ x ∉ (ps.get ⟨i, hi⟩).exc ∧
      x ∉ (ps.get ⟨j, hj⟩).exc) : off ⟨i, hi⟩ ⟨j, hj⟩ = κ j - κ i := by
  obtain ⟨x, hxp, hxq, -, -⟩ := hx
  obtain ⟨hi', ep⟩ := get_of hpi
  obtain ⟨hj', eq⟩ := get_of hpj
  rw [ep] at hxp
  rw [eq] at hxq
  have y0 : x - a0 ∈ Ls.dom := JointRot.mem_placed.1 hxp
  have y3 : x - a3 ∈ Lt.dom := JointRot.mem_placed.1 hxq
  obtain ⟨m3, h1⟩ := hK _ y0
  obtain ⟨m0, h2⟩ := hK' _ y3
  set z := a0 + a3 + C - x with hz
  have ez0 : z - a0 = C - (x - a3) := by rw [hz]; abel
  have ez3 : z - a3 = C - (x - a0) := by rw [hz]; abel
  have hz0 : z ∈ (stdPiece Ls a0 s0).placed := JointRot.mem_placed.2 (by simp only [stdPiece]; rw [ez0]; exact m0)
  have hz3 : z ∈ (stdPiece Lt a3 s3).placed := JointRot.mem_placed.2 (by simp only [stdPiece]; rw [ez3]; exact m3)
  have e1 := off_point hoff hpi hpj hxp hxq (by simp [stdPiece]) (by simp [stdPiece]) hi hj
  have e2 := off_point hoff hpi hpj hz0 hz3 (by simp [stdPiece]) (by simp [stdPiece]) hi hj
  simp only [pieceVal, stdPiece] at e1 e2
  rw [ez0, ez3] at e2
  have hzx : z = a0 + a3 + C - x := hz
  simp only [dotS, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at h1 h2 halg e1 e2
  rw [hzx] at e2
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at e2
  linarith

/-- At a point common to three pieces the overlap constants add up. -/
theorem off_triple {ps : List Piece} {off : Fin ps.length → Fin ps.length → ℤ} (hoff : OffMatch ps off)
    {a b c : ℕ} {p q r : Piece} (hp : ps[a]? = some p) (hq : ps[b]? = some q) (hr : ps[c]? = some r) {x : ℤ × ℤ}
    (hxp : x ∈ p.placed) (hxq : x ∈ q.placed) (hxr : x ∈ r.placed) (hep : x ∉ p.exc) (heq : x ∉ q.exc) (her : x ∉ r.exc)
    (ha : a < ps.length) (hb : b < ps.length) (hc : c < ps.length) :
    off ⟨a, ha⟩ ⟨b, hb⟩ = off ⟨a, ha⟩ ⟨c, hc⟩ + off ⟨c, hc⟩ ⟨b, hb⟩ := by
  rw [off_point hoff hp hq hxp hxq hep heq, off_point hoff hp hr hxp hxr hep her, off_point hoff hr hq hxr hxq her heq]
  ring

/-- **Condition (C) from a list of edges**: every listed pair that meets has the constant `κ j - κ i` for every choice of
overlap constants, and two pieces not listed (in either order) do not meet. -/
theorem walkZero_of_list (ps : List Piece) (κ : ℕ → ℤ) (E : List (ℕ × ℕ))
    (hE : ∀ off, OffMatch ps off → ∀ e ∈ E, ∀ (hi : e.1 < ps.length) (hj : e.2 < ps.length),
      (∃ x ∈ (ps.get ⟨e.1, hi⟩).placed, x ∈ (ps.get ⟨e.2, hj⟩).placed ∧ x ∉ (ps.get ⟨e.1, hi⟩).exc ∧
        x ∉ (ps.get ⟨e.2, hj⟩).exc) → off ⟨e.1, hi⟩ ⟨e.2, hj⟩ = κ e.2 - κ e.1)
    (hN : ∀ (i j : ℕ) (p q : Piece), ps[i]? = some p → ps[j]? = some q → i ≠ j → (i, j) ∉ E → (j, i) ∉ E →
      ∀ x ∈ p.placed, x ∈ q.placed → x ∉ p.exc → x ∉ q.exc → False) : TileStepAssembly.WalkZero ps := by
  refine walkZero_of_edges ps κ fun off hoff u v hadj => ?_
  obtain ⟨hne, x, hxu, hxv⟩ := hadj
  have hu : ps[u.1]? = some (ps.get u) := by simp
  have hv : ps[v.1]? = some (ps.get v) := by simp
  by_cases h1 : (u.1, v.1) ∈ E
  · exact hE off hoff _ h1 u.2 v.2 ⟨x.1, hxu.1, hxv.1, hxu.2, hxv.2⟩
  by_cases h2 : (v.1, u.1) ∈ E
  · have e2 := hE off hoff _ h2 v.2 u.2 ⟨x.1, hxv.1, hxu.1, hxv.2, hxu.2⟩
    have a := off_point hoff hu hv hxu.1 hxv.1 hxu.2 hxv.2 u.2 v.2
    have b := off_point hoff hv hu hxv.1 hxu.1 hxv.2 hxu.2 v.2 u.2
    simp only [Fin.eta] at a b e2 ⊢
    linarith
  exact (hN u.1 v.1 _ _ hu hv (fun h => hne (Fin.ext h)) h1 h2 x.1 hxu.1 hxv.1 hxu.2 hxv.2).elim

end FLatticePaper.Tiles.CorrectedWalkZero
