import FLatticePaper.Construction.PureRank
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Tiles.SiteCovers
import FLatticePaper.Tiles.SiteMaskStair
import FLatticePaper.Graph

/-!
# The signed canonical policy e(-1, eta) on the reciprocal field (task 118, W1 base)

The policy of flatrank3.py (`select`), in the native coordinates of the reciprocal tile (`NativeP`, the raw tile of
`BaseMask.stairEven` at `d = 2k+3`), and its extension to all of `ℤ × ℤ` through the native representative of each deck class.

* `freeEdge d η q e`: the free table of the sign `η` at a free point `q` for the displacement `e` (flatrank3.py `freeE`).
* `FreeAliasAt d c q`: `q` is a free native translate `shiftP d c i j` of `c` (an alias of `c`).
* `RetNat d η black c i`: the rule at a native centre `c`: the input `i` is retained when `c` is black (both inputs), or
  `c` is an even white with no free alias and the x-rule selects `i`, or some free alias `q` of `c` has `freeEdge q (i − c)`.
* `ePolicy d η lap c i`: the policy on `ℤ × ℤ`, evaluated at the native representative of `c`.
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey
open FLatticePaper.Tiles.SiteCovers FLatticePaper.Tiles.SiteInduction

/-- The deck vectors of `1/d` for odd `d`: the kernel is `(d, 1)` and the transverse is `(1 - d, 1 + d)`. -/
theorem combine_mk_one {d : ℤ} (hd : d % 2 = 1) (i j : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine i j = (i * d + j * (1 - d), i + j * (1 + d)) := by
  have hmu : muOf (Fraction.mk 1 d) = 1 := by
    unfold muOf
    dsimp only
    rw [if_neg (by omega)]
  have hk : (Fraction.mk 1 d).modifiedDeck.kernel = (d, 1) := by
    rw [modifiedDeck_kernel]
    unfold perU
    rw [hmu]
    simp
  have ht : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) := by
    rw [modifiedDeck_transverse]
    unfold perV
    simp only
    ring_nf
  unfold PeriodDeck.combine
  rw [hk, ht]
  simp only
  ring_nf

/-- Translation by an alias is translation by the deck vector. -/
theorem shiftP_eq_add_combine {d : ℤ} (hd : d % 2 = 1) (p : Pt) (i j : ℤ) :
    shiftP d p i j = p + (Fraction.mk 1 d).modifiedDeck.combine i j := by
  rw [combine_mk_one hd]
  unfold shiftP
  ext <;> (simp; try ring)

theorem shiftP_zero_zero (d : ℤ) (p : Pt) : shiftP d p 0 0 = p := by
  simp [shiftP]

/-- The deck translations preserve the parity of the coordinate sum (`d` odd). -/
theorem combine_sum_even {d : ℤ} (hd : d % 2 = 1) (i j : ℤ) :
    (((Fraction.mk 1 d).modifiedDeck.combine i j).1 + ((Fraction.mk 1 d).modifiedDeck.combine i j).2) % 2 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, d = 2 * t + 1 := ⟨(d - 1) / 2, by omega⟩
  rw [combine_mk_one (by omega)]
  have e : (i * (2 * t + 1) + j * (1 - (2 * t + 1))) + (i + j * (1 + (2 * t + 1))) = 2 * ((t + 1) * i + j) := by
    ring
  rw [e]
  simp [Int.mul_emod_right]

/-- A free point of the native domain is native. -/
theorem nativeP_of_raw {d : ℤ} {p : Pt} (h : p ∈ (BaseMask.stairEven.raw d).sites) : NativeP d p := by
  rw [BaseMask.mem_stairEven_raw_iff] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, hc⟩ := h
  obtain ⟨x, y⟩ := p
  unfold NativeP
  simp only at h1 h2 h3 h4 hc ⊢
  rcases hc with hc | hc
  · unfold BaseMask.StairEvenCorner at hc
    rcases hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr (Or.inl (Prod.ext hx hy))
    · exact Or.inr (Or.inr (Prod.ext hx hy))
  · left
    omega

/-- The free table of the sign `η` at a free point `q` for the displacement `e` (flatrank3.py `freeE`). -/
def freeEdge (d η : ℤ) (q e : Pt) : Prop :=
  if IsHc d q then (if q.1 = 1 then e = (0, -η) else e.1 + e.2 = 1)
  else if IsVc d q then (if q = (0, 0) then e.1 = 1 else (e.1 = η ∧ e.2 = 0) ∨ (e.1 = 0 ∧ e.2 = -η))
  else False

/-- `q` is a free alias of `c`: a native free translate `shiftP d c i j` with `IsAlias i j`. -/
def FreeAliasAt (d : ℤ) (c q : Pt) : Prop :=
  ∃ i j, IsAlias i j ∧ q = shiftP d c i j ∧ NativeP d q ∧ IsFreeP d q

/-- The retained inputs `i` of the sign-`η` policy at a native centre `c` (flatrank3.py `select`): a black centre keeps both
inputs; an even white with no free alias keeps its x-rule input; a white with a free alias `q` keeps the input `i` when the
free table of `q` holds for the displacement `i - c`. -/
def RetNat (d η : ℤ) (black : Prop) (c i : Pt) : Prop :=
  (i = incomingNeg c ∨ i = incomingPos c) ∧
    (black ∨
      (EvenSite c ∧ ¬ (∃ q, FreeAliasAt d c q) ∧
        ((c.1 ≤ 0 ∧ i = incomingNeg c) ∨ (2 ≤ c.1 ∧ i = incomingPos c))) ∨
      (∃ q, FreeAliasAt d c q ∧ freeEdge d η q (i - c)))

/-- Every site is a native point translated by a deck vector (the cover of the raw tile, `stairEven_raw_cover`). -/
theorem exists_native_rep {d : ℤ} (hden : BaseMask.stairEven.Valid d) (p : Pt) :
    ∃ y, NativeP d y ∧ ∃ i j, p = y + (Fraction.mk 1 d).modifiedDeck.combine i j := by
  obtain ⟨y, hy, hspan⟩ := stairEven_raw_cover hden p
  obtain ⟨i, j, hij⟩ := hspan
  exact ⟨y, nativeP_of_raw hy, i, j, by rw [add_comm]; exact sub_eq_iff_eq_add.mp hij⟩

/-- The native representative of a site (a choice; the policy does not depend on it, see `ePolicy_indep`). -/
noncomputable def nativeRep (d : ℤ) (p : Pt) : Pt :=
  if h : BaseMask.stairEven.Valid d then Classical.choose (exists_native_rep h p) else p

theorem nativeRep_spec {d : ℤ} (h : BaseMask.stairEven.Valid d) (p : Pt) :
    NativeP d (nativeRep d p) ∧ ∃ i j, p = nativeRep d p + (Fraction.mk 1 d).modifiedDeck.combine i j := by
  unfold nativeRep
  rw [dif_pos h]
  exact Classical.choose_spec (exists_native_rep h p)

/-- The sign-`η` policy `e(-1, η)` on `ℤ × ℤ`: the rule at the native representative of the centre `c`, with the
displacement `i - c` carried to the representative. `lap` is the laplacian of the field. -/
noncomputable def ePolicy (d η : ℤ) (lap : Pt → ℤ) (c i : Pt) : Prop :=
  RetNat d η (lap c = -1) (nativeRep d c) (nativeRep d c + (i - c))

/-! ### Generic facts: translation by an even vector commutes with the inputs -/

theorem evenSite_add_iff {p l : Pt} (h : (l.1 + l.2) % 2 = 0) : EvenSite (p + l) ↔ EvenSite p := by
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem incomingNeg_add {p l : Pt} (h : (l.1 + l.2) % 2 = 0) : incomingNeg (p + l) = incomingNeg p + l := by
  unfold incomingNeg
  by_cases hp : EvenSite p
  · rw [if_pos hp, if_pos ((evenSite_add_iff h).mpr hp)]
    ext <;> (simp; try ring)
  · rw [if_neg hp, if_neg (fun hq => hp ((evenSite_add_iff h).mp hq))]
    ext <;> (simp; try ring)

theorem incomingPos_add {p l : Pt} (h : (l.1 + l.2) % 2 = 0) : incomingPos (p + l) = incomingPos p + l := by
  unfold incomingPos
  by_cases hp : EvenSite p
  · rw [if_pos hp, if_pos ((evenSite_add_iff h).mpr hp)]
    ext <;> (simp; try ring)
  · rw [if_neg hp, if_neg (fun hq => hp ((evenSite_add_iff h).mp hq))]
    ext <;> (simp; try ring)

/-- The representative of a site and the deck vector carrying it. -/
theorem ePolicy_rep {d : ℤ} (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (c : Pt) :
    ∃ l : Pt, (l.1 + l.2) % 2 = 0 ∧ c = nativeRep d c + l := by
  obtain ⟨-, i, j, hc⟩ := nativeRep_spec hden c
  refine ⟨(Fraction.mk 1 d).modifiedDeck.combine i j, ?_, hc⟩
  exact combine_sum_even hd i j

/-- A retained input of the rule at a representative `y`, carried by the even vector `l` to the centre `c = y + l`, is an edge
of `c`. -/
theorem retNat_edge {d η : ℤ} {black : Prop} {y c i l : Pt} (hl : (l.1 + l.2) % 2 = 0) (hc : c = y + l)
    (h : RetNat d η black y (y + (i - c))) : i = incomingNeg c ∨ i = incomingPos c := by
  subst hc
  unfold RetNat at h
  obtain ⟨h1, -⟩ := h
  rcases h1 with h1 | h1
  · left
    rw [incomingNeg_add hl]
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2
    ext
    · simp only [Prod.fst_add]
      omega
    · simp only [Prod.snd_add]
      omega
  · right
    rw [incomingPos_add hl]
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2
    ext
    · simp only [Prod.fst_add]
      omega
    · simp only [Prod.snd_add]
      omega

/-- Every retained input of `ePolicy` is an edge of the graph: the policy is a set of edges. -/
theorem ePolicy_edge {d : ℤ} (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (η : ℤ)
    (lap : Pt → ℤ) (c i : Pt) (h : ePolicy d η lap c i) : i = incomingNeg c ∨ i = incomingPos c := by
  obtain ⟨l, hl, hc⟩ := ePolicy_rep hd hden c
  unfold ePolicy at h
  exact retNat_edge hl hc h

/-- The two inputs of a black centre, carried from its representative: both are retained by the black clause. -/
theorem retNat_black_both {d η : ℤ} {y c l : Pt} (hl : (l.1 + l.2) % 2 = 0) (hc : c = y + l) (hb : Prop)
    (hbl : hb) :
    RetNat d η hb y (y + (incomingNeg c - c)) ∧ RetNat d η hb y (y + (incomingPos c - c)) := by
  subst hc
  have hN : incomingNeg (y + l) - (y + l) = incomingNeg y - y := by
    rw [incomingNeg_add hl]
    ext <;> simp
  have hP : incomingPos (y + l) - (y + l) = incomingPos y - y := by
    rw [incomingPos_add hl]
    ext <;> simp
  constructor
  · unfold RetNat
    rw [hN]
    exact ⟨Or.inl (by ext <;> simp), Or.inl hbl⟩
  · unfold RetNat
    rw [hP]
    exact ⟨Or.inr (by ext <;> simp), Or.inl hbl⟩

/-- Black centres keep both inputs (the black clause of the rule). -/
theorem ePolicy_black {d : ℤ} (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d) (η : ℤ)
    (lap : Pt → ℤ) (c : Pt) (hb : lap c = -1) :
    ePolicy d η lap c (incomingNeg c) ∧ ePolicy d η lap c (incomingPos c) := by
  obtain ⟨l, hl, hc⟩ := ePolicy_rep hd hden c
  obtain ⟨h1, h2⟩ := retNat_black_both (d := d) (η := η) hl hc (lap c = -1) hb
  exact ⟨h1, h2⟩

/-- The deck vectors `combine i j` add and negate. -/
theorem combine_add_mk_one {d : ℤ} (hd : d % 2 = 1) (i j i' j' : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine i j + (Fraction.mk 1 d).modifiedDeck.combine i' j' =
      (Fraction.mk 1 d).modifiedDeck.combine (i + i') (j + j') := by
  rw [combine_mk_one hd, combine_mk_one hd, combine_mk_one hd]
  ext <;> (simp; try ring)

theorem combine_neg_mk_one {d : ℤ} (hd : d % 2 = 1) (i j : ℤ) :
    -(Fraction.mk 1 d).modifiedDeck.combine i j = (Fraction.mk 1 d).modifiedDeck.combine (-i) (-j) := by
  rw [combine_mk_one hd, combine_mk_one hd]
  ext <;> (simp; try ring)

/-- The free set of the policy: a site is free when some deck translate of it is a free point of the native domain. -/
def FreeGlobal (d : ℤ) (c : Pt) : Prop :=
  ∃ i j : ℤ, IsFreeP d (c + (Fraction.mk 1 d).modifiedDeck.combine i j)

/-- The free set is invariant under the deck span. -/
theorem freeGlobal_add_span {d : ℤ} (hd : d % 2 = 1) (step : Pt)
    (hstep : step ∈ (Fraction.mk 1 d).modifiedDeck.span) (site : Pt) :
    FreeGlobal d (site + step) ↔ FreeGlobal d site := by
  obtain ⟨i0, j0, rfl⟩ := hstep
  constructor
  · rintro ⟨i, j, h⟩
    refine ⟨i0 + i, j0 + j, ?_⟩
    rw [add_assoc, combine_add_mk_one hd] at h
    exact h
  · rintro ⟨i, j, h⟩
    refine ⟨i - i0, j - j0, ?_⟩
    have e : site + (Fraction.mk 1 d).modifiedDeck.combine i0 j0 +
        (Fraction.mk 1 d).modifiedDeck.combine (i - i0) (j - j0) = site + (Fraction.mk 1 d).modifiedDeck.combine i j := by
      rw [add_assoc, combine_add_mk_one hd, show i0 + (i - i0) = i by ring, show j0 + (j - j0) = j by ring]
    rw [e]
    exact h

end FLatticePaper.EPolicy
