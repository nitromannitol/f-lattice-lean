import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.TwoRank
import FLatticePaper.Plane.Induction.W1MRank
import FLatticePaper.Plane.AlternateMidpoint

/-! Task 72 / Q20: the acyclic minimum policy of the two-rank argument (`TWO_RANK_RAW_PHI_AUDIT.md` §2), as a proof.

Fields: `F` (Laplacian binary, `laplacian F ∈ {−1, 0}`, with unit slip), `g = F(· + ησ)`, `D = slip F η = F − g`, and the minimum
`m = min(F, g + k)` (`mF`). The minimum is taken with the Laplacian binary for every `k`: at a strict winner the star of the winner is
the star of `m`; at a tie the star of `m` is the `F`- or `g`-star, or the two white parents with input increments `(+1, −1)` of `D`.

The rank of a site is the lexicographic key `(Q, X)`: `Q = −|D − k|`; `X` is the F-game's physical key (price, rounded slip, rank) on
`D < k` and the translated opposite game's key (at `c + ησ`) on `D ≥ k`. The selection is the F-selection on `D < k` and the translated
opposite selection on `D ≥ k`. Square clauses follow from `squareClauses_of_burning` (a strict rank in a linear order). -/

namespace FLatticePaper.MinPolicy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1MRank

/-- The translated g-field `g(x) = F(x + ησ)`. -/
def gF (frame : ChildFrame) (F : Field) (η : ℤ) : Field := fun x => F (x + η • frame.shortShift)

/-- The minimum `m = min(F, g + k)`. -/
def mF (frame : ChildFrame) (F : Field) (η : ℤ) (k : ℤ) : Field :=
  fun x => min (F x) (gF frame F η x + k)

/-- The first rank coordinate `Q = min(D − k, k − D) = −|D − k|`. -/
def Qk (frame : ChildFrame) (F : Field) (η : ℤ) (k : ℤ) (x : Site) : ℤ :=
  min (frame.slip F η x - k) (k - frame.slip F η x)

/-- The second coordinate: the F-game's physical key on `D < k`, the translated opposite game's on `D ≥ k`. -/
def XK (frame : ChildFrame) (F : Field) (η : ℤ) (C : CanonicalSignedPolicy frame F η)
    (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (x : Site) : Lex (ℤ × Lex (ℤ × ℤ)) :=
  if frame.slip F η x < k then toLex (frame.price F x, toLex (frame.cutGrade F 0 1 η x, C.rank x))
  else toLex (frame.price F (x + η • frame.shortShift),
    toLex (frame.cutGrade F 0 1 (-η) (x + η • frame.shortShift), O.rank (x + η • frame.shortShift)))

/-- The lexicographic rank of a site. -/
def keyK (frame : ChildFrame) (F : Field) (η : ℤ) (C : CanonicalSignedPolicy frame F η)
    (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (x : Site) : Lex (ℤ × Lex (ℤ × Lex (ℤ × ℤ))) :=
  toLex (Qk frame F η k x, XK frame F η C O k x)

/-- The selection of the minimum: the F-selection on `D < k`, the translated opposite selection otherwise. -/
def msel (frame : ChildFrame) (F : Field) (η : ℤ) (C : CanonicalSignedPolicy frame F η)
    (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (c : Site) : Site :=
  if frame.slip F η c < k then C.sel c else O.sel (c + η • frame.shortShift) - η • frame.shortShift

/-- The minimum's tie expression: the Laplacian of `min(F, g + k)` at a site whose value is `a0` (with `g0`) and whose inputs are
`(a1, g1)`, `(a2, g2)`. -/
def tieL (a0 a1 a2 g0 g1 g2 k : ℤ) : ℤ :=
  (min a1 (g1 + k) - min a0 (g0 + k)) + (min a2 (g2 + k) - min a0 (g0 + k))

/-- The even shift `ησ` (its coordinate sum is even). -/
theorem shift_even (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    ((η • frame.shortShift).1 + (η • frame.shortShift).2) % 2 = 0 := by
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ frame.shortShift.1 + frame.shortShift.2 :=
    Int.dvd_of_emod_eq_zero (FLatticePaper.BothFreeGrades.shortShift_even frame)
  rcases hη with h | h <;> simp only [h, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> omega

/-- The lexicographic decrease along a kept edge of a canonical policy of any sign. -/
theorem lex_of_canonical {frame : ChildFrame} {F : Field} {s : ℤ} (C : CanonicalSignedPolicy frame F s) {c x : Site}
    (h : C.policy c x) :
    toLex (frame.price F x, toLex (frame.cutGrade F 0 1 s x, C.rank x)) <
      toLex (frame.price F c, toLex (frame.cutGrade F 0 1 s c, C.rank c)) := by
  have hP : frame.price F x ≤ frame.price F c := by
    have h1 := C.nonincreasingP c x h
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
    exact h1
  have hJ := C.nonincreasingJ c x h
  rcases lt_or_eq_of_le hP with hPlt | hPeq
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hPlt)
  · by_cases hJeq : frame.cutGrade F 0 1 s x = frame.cutGrade F 0 1 s c
    · have hPe : frame.cutGrade F 1 0 1 x = frame.cutGrade F 1 0 1 c := by
        rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
        exact hPeq
      have hr := C.strictRank c x h hPe hJeq
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hPeq, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hJeq, hr⟩)⟩)
    · have hJlt : frame.cutGrade F 0 1 s x < frame.cutGrade F 0 1 s c := lt_of_le_of_ne hJ hJeq
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hPeq, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hJlt)⟩)

/-- The F-game's monotonicity of the raw slip: a kept input has `D ≤ D(centre)`. -/
theorem slip_le_of_F {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η) {c x : Site}
    (h : C.policy c x) : frame.slip F η x ≤ frame.slip F η c :=
  rawSlip_of_canonical C c x h

/-- The translated opposite game's monotonicity: a kept input of the translated g-policy has `D ≥ D(centre)`. -/
theorem slip_le_of_G {frame : ChildFrame} {F : Field} {η : ℤ} (O : CanonicalSignedPolicy frame F (-η)) {c x : Site}
    (h : O.policy (c + η • frame.shortShift) (x + η • frame.shortShift)) : frame.slip F η c ≤ frame.slip F η x := by
  have h1 := rawSlip_of_canonical O (c + η • frame.shortShift) (x + η • frame.shortShift) h
  dsimp only at h1
  rw [TwoRank.add_neg_smul_cancel, TwoRank.add_neg_smul_cancel] at h1
  unfold ChildFrame.slip
  linarith

theorem slip_eq_gF (frame : ChildFrame) (F : Field) (η : ℤ) (x : Site) :
    frame.slip F η x = F x - gF frame F η x := rfl

theorem mF_of_le {frame : ChildFrame} {F : Field} {η k : ℤ} {x : Site} (h : frame.slip F η x ≤ k) :
    mF frame F η k x = F x := by
  rw [slip_eq_gF] at h
  show min (F x) (gF frame F η x + k) = F x
  exact min_eq_left (by linarith)

theorem mF_of_ge {frame : ChildFrame} {F : Field} {η k : ℤ} {x : Site} (h : k ≤ frame.slip F η x) :
    mF frame F η k x = gF frame F η x + k := by
  rw [slip_eq_gF] at h
  show min (F x) (gF frame F η x + k) = gF frame F η x + k
  exact min_eq_right (by linarith)

theorem Qk_of_le {frame : ChildFrame} {F : Field} {η k : ℤ} {x : Site} (h : frame.slip F η x ≤ k) :
    Qk frame F η k x = frame.slip F η x - k := by
  unfold Qk
  exact min_eq_left (by linarith)

theorem Qk_of_ge {frame : ChildFrame} {F : Field} {η k : ℤ} {x : Site} (h : k ≤ frame.slip F η x) :
    Qk frame F η k x = k - frame.slip F η x := by
  unfold Qk
  exact min_eq_right (by linarith)

theorem Qk_neg_of_ne {frame : ChildFrame} {F : Field} {η k : ℤ} {x : Site} (h : frame.slip F η x ≠ k) :
    Qk frame F η k x < 0 := by
  unfold Qk
  rcases lt_or_gt_of_ne h with h' | h'
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

theorem Qk_of_tie {frame : ChildFrame} {F : Field} {η k : ℤ} {c : Site} (h : frame.slip F η c = k) :
    Qk frame F η k c = 0 := by
  unfold Qk
  rw [h]
  simp

/-- A strict decrease of `Q` decreases the key. -/
theorem key_lt_of_Qlt {frame : ChildFrame} {F : Field} {η : ℤ} {C : CanonicalSignedPolicy frame F η}
    {O : CanonicalSignedPolicy frame F (-η)} {k : ℤ} {x c : Site}
    (h : Qk frame F η k x < Qk frame F η k c) : keyK frame F η C O k x < keyK frame F η C O k c :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- **The F-key decreases along a kept edge of a centre in the F-region.** -/
theorem key_lt_of_F {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η)
    (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) {c x : Site} (hC : C.policy c x)
    (hc : frame.slip F η c < k) : keyK frame F η C O k x < keyK frame F η C O k c := by
  have hD := slip_le_of_F C hC
  have hx : frame.slip F η x < k := lt_of_le_of_lt hD hc
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases lt_or_eq_of_le hD with hlt | heq
  · left
    show Qk frame F η k x < Qk frame F η k c
    rw [Qk_of_le hx.le, Qk_of_le hc.le]
    linarith
  · right
    refine ⟨?_, ?_⟩
    · show Qk frame F η k x = Qk frame F η k c
      rw [Qk_of_le hx.le, Qk_of_le hc.le, heq]
    · show XK frame F η C O k x < XK frame F η C O k c
      unfold XK
      rw [if_pos hx, if_pos hc]
      exact lex_of_canonical C hC

/-- **The g-key decreases along a kept edge of the translated opposite policy, for a centre with `D ≥ k`.** -/
theorem key_lt_of_G {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η)
    (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) {c x : Site}
    (hO : O.policy (c + η • frame.shortShift) (x + η • frame.shortShift)) (hc : k ≤ frame.slip F η c) :
    keyK frame F η C O k x < keyK frame F η C O k c := by
  have hD := slip_le_of_G O hO
  have hx : k ≤ frame.slip F η x := le_trans hc hD
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases lt_or_eq_of_le hD with hlt | heq
  · left
    show Qk frame F η k x < Qk frame F η k c
    rw [Qk_of_ge hx, Qk_of_ge hc]
    linarith
  · right
    refine ⟨?_, ?_⟩
    · show Qk frame F η k x = Qk frame F η k c
      rw [Qk_of_ge hx, Qk_of_ge hc, heq]
    · show XK frame F η C O k x < XK frame F η C O k c
      unfold XK
      rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hc)]
      exact lex_of_canonical O hO

/-- The Laplacian of the minimum on an F-region centre equals the F-Laplacian. -/
theorem lap_mF_of_le {frame : ChildFrame} {F : Field} {η k : ℤ} {c : Site} (h0 : frame.slip F η c ≤ k)
    (h1 : frame.slip F η (incomingNeg c) ≤ k) (h2 : frame.slip F η (incomingPos c) ≤ k) :
    laplacian (mF frame F η k) c = laplacian F c := by
  unfold laplacian
  rw [mF_of_le h0, mF_of_le h1, mF_of_le h2]

/-- The Laplacian of the minimum on a g-region centre equals the g-Laplacian. -/
theorem lap_mF_of_ge {frame : ChildFrame} {F : Field} {η k : ℤ} {c : Site} (h0 : k ≤ frame.slip F η c)
    (h1 : k ≤ frame.slip F η (incomingNeg c)) (h2 : k ≤ frame.slip F η (incomingPos c)) :
    laplacian (mF frame F η k) c = laplacian (gF frame F η) c := by
  unfold laplacian
  rw [mF_of_ge h0, mF_of_ge h1, mF_of_ge h2]
  ring

/-- The Laplacian of the translated field is the Laplacian of `F` at the translated site. -/
theorem lap_gF_eq_shift {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1) (c : Site) :
    laplacian (gF frame F η) c = laplacian F (c + η • frame.shortShift) :=
  TwoRank.laplacian_translate F (η • frame.shortShift) (shift_even frame hη) c

/-- The minimum's Laplacian at a tie centre (`mF c = F c`). -/
theorem lap_mF_eq_tieL (frame : ChildFrame) (F : Field) (η k : ℤ) (c : Site) :
    laplacian (mF frame F η k) c = tieL (F c) (F (incomingNeg c)) (F (incomingPos c))
      (gF frame F η c) (gF frame F η (incomingNeg c)) (gF frame F η (incomingPos c)) k := rfl

/-- **The tie arithmetic.** At a centre with `F c − g c = k`, the Laplacian of the minimum is `−1` or `0`; its black case has the
F-black, the g-black, or the both-white `(+1, −1)` pattern; its white case forces the g-Laplacian to vanish. -/
theorem tie_arith (a0 a1 a2 g0 g1 g2 d1 d2 k : ℤ) (hd1 : d1 = a1 - g1) (hd2 : d2 = a2 - g2) (hk : a0 - g0 = k)
    (hA : (a1 - a0) + (a2 - a0) = -1 ∨ (a1 - a0) + (a2 - a0) = 0)
    (hG : (g1 - g0) + (g2 - g0) = -1 ∨ (g1 - g0) + (g2 - g0) = 0)
    (hU1 : -1 ≤ d1 - k ∧ d1 - k ≤ 1) (hU2 : -1 ≤ d2 - k ∧ d2 - k ≤ 1)
    (hFb : (a1 - a0) + (a2 - a0) = -1 → d1 ≤ k ∧ d2 ≤ k)
    (hGb : (g1 - g0) + (g2 - g0) = -1 → k ≤ d1 ∧ k ≤ d2) :
    (tieL a0 a1 a2 g0 g1 g2 k = -1 ∨ tieL a0 a1 a2 g0 g1 g2 k = 0) ∧
    (tieL a0 a1 a2 g0 g1 g2 k = 0 → (g1 - g0) + (g2 - g0) = 0) ∧
    (tieL a0 a1 a2 g0 g1 g2 k = -1 →
      (g1 - g0) + (g2 - g0) = -1 ∨
      ((g1 - g0) + (g2 - g0) = 0 ∧ (a1 - a0) + (a2 - a0) = -1 ∧ ¬(d1 = k ∧ d2 = k)) ∨
      ((g1 - g0) + (g2 - g0) = 0 ∧ (a1 - a0) + (a2 - a0) = 0 ∧ d1 ≠ k ∧ d2 ≠ k)) := by
  unfold tieL
  have h0 : min a0 (g0 + k) = a0 := min_eq_left (by omega)
  rw [h0]
  subst hd1 hd2
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [min_def]; split_ifs <;> omega)

/-- The unit bound of the slip for the sign `η = ±1`, from the packet's unit slip `D_1` (the sign `−1` by translation). -/
theorem unit_slip_sign (frame : ChildFrame) (F : Field) (hU : HasUnitSlip F (fun z => F (z + frame.shortShift)))
    {η : ℤ} (hη : η = 1 ∨ η = -1) :
    ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1 := by
  intro c i h
  rcases hη with rfl | rfl
  · obtain ⟨h1, h2⟩ := hU c i h
    simp only [slipIncrement, ChildFrame.slip, one_smul] at h1 h2 ⊢
    constructor <;> linarith
  · have hs : ((-frame.shortShift).1 + (-frame.shortShift).2) % 2 = 0 := by
      have := FLatticePaper.BothFreeGrades.shortShift_even frame
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    have he := TwoRank.edge_add_of_even (-frame.shortShift) hs h
    obtain ⟨h1, h2⟩ := hU (c + -frame.shortShift) (i + -frame.shortShift) he
    have e1 : i + -frame.shortShift + frame.shortShift = i := by abel
    have e2 : c + -frame.shortShift + frame.shortShift = c := by abel
    simp only [slipIncrement, e1, e2] at h1 h2
    simp only [ChildFrame.slip, neg_one_smul]
    constructor <;> linarith

/-- The opposite black policy: a black translated centre keeps both translated inputs. -/
theorem opp_black_policy {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (O : CanonicalSignedPolicy frame F (-η)) {c : Site} (h : laplacian F (c + η • frame.shortShift) = -1) :
    O.policy (c + η • frame.shortShift) (incomingNeg c + η • frame.shortShift) ∧
      O.policy (c + η • frame.shortShift) (incomingPos c + η • frame.shortShift) := by
  have hq := O.quota
  unfold RetainQuota at hq
  have hn := hq.1 _ h
  rw [TwoRank.incomingNeg_add c _ (shift_even frame hη),
    TwoRank.incomingPos_add c _ (shift_even frame hη)] at hn
  exact hn

/-- The translated opposite selection is an input of the centre. -/
theorem sel_g_input {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (O : CanonicalSignedPolicy frame F (-η)) {c : Site} (hz : laplacian F (c + η • frame.shortShift) = 0) :
    O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingNeg c ∨
      O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingPos c := by
  rcases O.sel_input _ hz with h | h
  · left
    rw [h, TwoRank.incomingNeg_add c _ (shift_even frame hη), add_sub_cancel_right]
  · right
    rw [h, TwoRank.incomingPos_add c _ (shift_even frame hη), add_sub_cancel_right]

/-- The translated opposite selection, shifted back, is a policy edge of the translated opposite policy. -/
theorem sel_g_policy {frame : ChildFrame} {F : Field} {η : ℤ} (O : CanonicalSignedPolicy frame F (-η)) {c : Site}
    (hz : laplacian F (c + η • frame.shortShift) = 0) :
    O.policy (c + η • frame.shortShift) (O.sel (c + η • frame.shortShift) - η • frame.shortShift + η • frame.shortShift) := by
  rw [sub_add_cancel]
  exact (O.white_policy _ hz _).mpr rfl

/-- The tie instance of `tie_arith` at a centre with `D c = k`. -/
theorem tie_inst {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1)
    (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) {c : Site}
    (heq : frame.slip F η c = k) :
    (laplacian (mF frame F η k) c = -1 ∨ laplacian (mF frame F η k) c = 0) ∧
    (laplacian (mF frame F η k) c = 0 → laplacian (gF frame F η) c = 0) ∧
    (laplacian (mF frame F η k) c = -1 →
      laplacian (gF frame F η) c = -1 ∨
      (laplacian (gF frame F η) c = 0 ∧ laplacian F c = -1 ∧
        ¬(frame.slip F η (incomingNeg c) = k ∧ frame.slip F η (incomingPos c) = k)) ∨
      (laplacian (gF frame F η) c = 0 ∧ laplacian F c = 0 ∧
        frame.slip F η (incomingNeg c) ≠ k ∧ frame.slip F η (incomingPos c) ≠ k)) := by
  obtain ⟨hn1, hn2⟩ := hunit c (incomingNeg c) (Or.inl rfl)
  obtain ⟨hp1, hp2⟩ := hunit c (incomingPos c) (Or.inr rfl)
  have hk : F c - gF frame F η c = k := by
    rw [← heq]
    rfl
  have hq := C.quota
  unfold RetainQuota at hq
  have hFb : (F (incomingNeg c) - F c) + (F (incomingPos c) - F c) = -1 →
      frame.slip F η (incomingNeg c) ≤ k ∧ frame.slip F η (incomingPos c) ≤ k := by
    intro hA
    obtain ⟨hn, hp⟩ := hq.1 c hA
    have h1 := slip_le_of_F C hn
    have h2 := slip_le_of_F C hp
    constructor <;> linarith
  have hGb : (gF frame F η (incomingNeg c) - gF frame F η c) + (gF frame F η (incomingPos c) - gF frame F η c) = -1 →
      k ≤ frame.slip F η (incomingNeg c) ∧ k ≤ frame.slip F η (incomingPos c) := by
    intro hG
    have hG' : laplacian F (c + η • frame.shortShift) = -1 := by
      rw [← lap_gF_eq_shift hη c]
      exact hG
    obtain ⟨hn, hp⟩ := opp_black_policy hη O hG'
    have h1 := slip_le_of_G O hn
    have h2 := slip_le_of_G O hp
    constructor <;> linarith
  have hbinG : (gF frame F η (incomingNeg c) - gF frame F η c) + (gF frame F η (incomingPos c) - gF frame F η c) = -1 ∨
      (gF frame F η (incomingNeg c) - gF frame F η c) + (gF frame F η (incomingPos c) - gF frame F η c) = 0 := by
    have := hbin (c + η • frame.shortShift)
    rw [← lap_gF_eq_shift hη c] at this
    exact this
  have hU1 : -1 ≤ frame.slip F η (incomingNeg c) - k ∧ frame.slip F η (incomingNeg c) - k ≤ 1 :=
    ⟨by linarith, by linarith⟩
  have hU2 : -1 ≤ frame.slip F η (incomingPos c) - k ∧ frame.slip F η (incomingPos c) - k ≤ 1 :=
    ⟨by linarith, by linarith⟩
  obtain ⟨T1, T2, T3⟩ := tie_arith (F c) (F (incomingNeg c)) (F (incomingPos c)) (gF frame F η c)
    (gF frame F η (incomingNeg c)) (gF frame F η (incomingPos c)) (frame.slip F η (incomingNeg c))
    (frame.slip F η (incomingPos c)) k (slip_eq_gF frame F η _) (slip_eq_gF frame F η _) hk (hbin c) hbinG hU1 hU2
    hFb hGb
  refine ⟨?_, ?_, ?_⟩
  · rw [lap_mF_eq_tieL]
    exact T1
  · intro h
    rw [lap_mF_eq_tieL] at h
    exact T2 h
  · intro h
    rw [lap_mF_eq_tieL] at h
    exact T3 h

/-- **The black case of the key.** A black centre of the minimum has both inputs of strictly smaller key. -/
theorem black_lt {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1)
    (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) {c : Site}
    (hb : laplacian (mF frame F η k) c = -1) :
    keyK frame F η C O k (incomingNeg c) < keyK frame F η C O k c ∧
      keyK frame F η C O k (incomingPos c) < keyK frame F η C O k c := by
  obtain ⟨hn1, hn2⟩ := hunit c (incomingNeg c) (Or.inl rfl)
  obtain ⟨hp1, hp2⟩ := hunit c (incomingPos c) (Or.inr rfl)
  rcases lt_trichotomy (frame.slip F η c) k with hlt | heq | hgt
  · have hlapF : laplacian F c = -1 := by
      rw [lap_mF_of_le hlt.le (by linarith) (by linarith)] at hb
      exact hb
    have hq := C.quota
    unfold RetainQuota at hq
    obtain ⟨hn, hp⟩ := hq.1 c hlapF
    exact ⟨key_lt_of_F C O k hn hlt, key_lt_of_F C O k hp hlt⟩
  · obtain ⟨-, -, T3⟩ := tie_inst hη hbin hunit C O k heq
    rcases T3 hb with hG1 | ⟨hG0, hA1, hnb⟩ | ⟨hG0, hA0, hd1, hd2⟩
    · have hG' : laplacian F (c + η • frame.shortShift) = -1 := by
        rw [← lap_gF_eq_shift hη c]
        exact hG1
      obtain ⟨hn, hp⟩ := opp_black_policy hη O hG'
      exact ⟨key_lt_of_G C O k hn heq.ge, key_lt_of_G C O k hp heq.ge⟩
    · -- F black at the tie, g white: the only tied input is the translated opposite selection.
      have hz : laplacian F (c + η • frame.shortShift) = 0 := by
        rw [← lap_gF_eq_shift hη c]
        exact hG0
      have hsIn := sel_g_input hη O hz
      have hsKey := key_lt_of_G C O k (sel_g_policy O hz) heq.ge
      have hq := C.quota
      unfold RetainQuota at hq
      have hlow : ∀ x, (x = incomingNeg c ∨ x = incomingPos c) → frame.slip F η x ≤ k := by
        intro x hx
        obtain ⟨hn, hp⟩ := hq.1 c hA1
        rcases hx with rfl | rfl
        · have := slip_le_of_F C hn
          linarith
        · have := slip_le_of_F C hp
          linarith
      have hsTied : frame.slip F η (O.sel (c + η • frame.shortShift) - η • frame.shortShift) = k := by
        have h1 := slip_le_of_G O (sel_g_policy O hz)
        have h2 := hlow _ (hsIn)
        linarith
      have key_of : ∀ x, (x = incomingNeg c ∨ x = incomingPos c) →
          (frame.slip F η x < k ∨ x = O.sel (c + η • frame.shortShift) - η • frame.shortShift) := by
        intro x hx
        by_cases hlt' : frame.slip F η x < k
        · exact Or.inl hlt'
        · right
          by_contra hxs
          have hxk : frame.slip F η x = k := le_antisymm (hlow x hx) (not_lt.mp hlt')
          apply hnb
          rcases hx with rfl | rfl <;> rcases hsIn with hs | hs
          · exact absurd hs.symm hxs
          · exact ⟨hxk, hs ▸ hsTied⟩
          · exact ⟨hs ▸ hsTied, hxk⟩
          · exact absurd hs.symm hxs
      constructor
      · rcases key_of _ (Or.inl rfl) with h | h
        · apply key_lt_of_Qlt
          rw [Qk_of_le (le_of_lt h), Qk_of_tie heq]
          linarith
        · rw [h]
          exact hsKey
      · rcases key_of _ (Or.inr rfl) with h | h
        · apply key_lt_of_Qlt
          rw [Qk_of_le (le_of_lt h), Qk_of_tie heq]
          linarith
        · rw [h]
          exact hsKey
    · exact ⟨key_lt_of_Qlt (by rw [Qk_of_tie heq]; exact Qk_neg_of_ne hd1),
        key_lt_of_Qlt (by rw [Qk_of_tie heq]; exact Qk_neg_of_ne hd2)⟩
  · have hlapG : laplacian (gF frame F η) c = -1 := by
      rw [lap_mF_of_ge hgt.le (by linarith) (by linarith)] at hb
      exact hb
    have hG' : laplacian F (c + η • frame.shortShift) = -1 := by
      rw [← lap_gF_eq_shift hη c]
      exact hlapG
    obtain ⟨hn, hp⟩ := opp_black_policy hη O hG'
    exact ⟨key_lt_of_G C O k hn hgt.le, key_lt_of_G C O k hp hgt.le⟩

/-- The minimum is binary: its Laplacian is `−1` or `0` at every centre. -/
theorem lapM_binary {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1)
    (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) (c : Site) :
    laplacian (mF frame F η k) c = -1 ∨ laplacian (mF frame F η k) c = 0 := by
  obtain ⟨hn1, hn2⟩ := hunit c (incomingNeg c) (Or.inl rfl)
  obtain ⟨hp1, hp2⟩ := hunit c (incomingPos c) (Or.inr rfl)
  rcases lt_trichotomy (frame.slip F η c) k with hlt | heq | hgt
  · rw [lap_mF_of_le hlt.le (by linarith) (by linarith)]
    exact hbin c
  · exact (tie_inst hη hbin hunit C O k heq).1
  · rw [lap_mF_of_ge hgt.le (by linarith) (by linarith), lap_gF_eq_shift hη c]
    exact hbin _

/-- **The white case of the key.** A white centre of the minimum selects an input of strictly smaller key. -/
theorem white_sel {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1)
    (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k : ℤ) {c : Site}
    (hw : laplacian (mF frame F η k) c = 0) :
    (msel frame F η C O k c = incomingNeg c ∨ msel frame F η C O k c = incomingPos c) ∧
      keyK frame F η C O k (msel frame F η C O k c) < keyK frame F η C O k c := by
  obtain ⟨hn1, hn2⟩ := hunit c (incomingNeg c) (Or.inl rfl)
  obtain ⟨hp1, hp2⟩ := hunit c (incomingPos c) (Or.inr rfl)
  have hG_case : k ≤ frame.slip F η c → laplacian F (c + η • frame.shortShift) = 0 →
      (msel frame F η C O k c = incomingNeg c ∨ msel frame F η C O k c = incomingPos c) ∧
        keyK frame F η C O k (msel frame F η C O k c) < keyK frame F η C O k c := by
    intro hc hz
    have hm : msel frame F η C O k c = O.sel (c + η • frame.shortShift) - η • frame.shortShift := by
      unfold msel
      rw [if_neg (not_lt.mpr hc)]
    rw [hm]
    exact ⟨sel_g_input hη O hz, key_lt_of_G C O k (sel_g_policy O hz) hc⟩
  rcases lt_trichotomy (frame.slip F η c) k with hlt | heq | hgt
  · have hlapF : laplacian F c = 0 := by
      rw [lap_mF_of_le hlt.le (by linarith) (by linarith)] at hw
      exact hw
    have hm : msel frame F η C O k c = C.sel c := by
      unfold msel
      rw [if_pos hlt]
    rw [hm]
    exact ⟨C.sel_input c hlapF, key_lt_of_F C O k ((C.white_policy c hlapF (C.sel c)).mpr rfl) hlt⟩
  · have hz := (tie_inst hη hbin hunit C O k heq).2.1 hw
    exact hG_case heq.ge (by rw [← lap_gF_eq_shift hη c]; exact hz)
  · have hlapG : laplacian (gF frame F η) c = 0 := by
      rw [lap_mF_of_ge hgt.le (by linarith) (by linarith)] at hw
      exact hw
    exact hG_case hgt.le (by rw [← lap_gF_eq_shift hη c]; exact hlapG)

/-- **The square clauses of the minimum** (`msel` is the acyclic selection): the strict key of `squareClauses_of_burning`. -/
theorem msel_squareClauses {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hunit : ∀ c i, FLatticePaper.Edge i c → -1 ≤ frame.slip F η i - frame.slip F η c ∧
      frame.slip F η i - frame.slip F η c ≤ 1)
    (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η)) (k a b : ℤ) :
    SquareClauseSat (mF frame F η k) (msel frame F η C O k) a b :=
  squareClauses_of_burning (R := keyK frame F η C O k) (lapM_binary hη hbin hunit C O k)
    (fun c hb i hi => by
      obtain ⟨h1, h2⟩ := black_lt hη hbin hunit C O k hb
      rcases hi with rfl | rfl
      · exact h1
      · exact h2)
    (fun c hw => white_sel hη hbin hunit C O k hw) a b

end FLatticePaper.MinPolicy
