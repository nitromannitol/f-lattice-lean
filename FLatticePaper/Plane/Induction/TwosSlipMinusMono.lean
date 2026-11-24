import FLatticePaper.Plane.Induction.TwosSlipMono
import FLatticePaper.Plane.Induction.TwosSlipMinus
import FLatticePaper.Plane.Induction.TwosBaseSlip
import FLatticePaper.Plane.Induction.Q3Field

/-! Task 118, the sign `η = −1` of the twos slip monotonicity.

The standard field is symmetric under the reflection `z ↦ (1,−1) − z` (`packet_reflection_I`), and the sign `−1` slip is the
reflected `+1` slip: `slip (−1) z = twosSlip k ((1,−1) − z)` (`slip_minus_eq_iRefl`). The reflection preserves the laplacian and
exchanges the incoming sites (`incomingNeg_iRefl`, `incomingPos_iRefl`), so the black branch of `TwosSel a (−1)` is the black branch of
`TwosSel a 1` at the reflected pair, and `twosSlip_nonincreasing` applies (`twosSlipM_black`). -/

namespace FLatticePaper.Induction
open Farey Construction FLatticePaper

/-- The reflection of the standard field: `F ((1,−1) − z) = F z`. -/
theorem twos_F_iRefl (k : ℕ) (z : Site) :
    standardField (List.replicate (k + 1) Digit.two) ((1, -1) - z) = standardField (List.replicate (k + 1) Digit.two) z :=
  packet_reflection_I (frameAt (List.replicate (k + 1) Digit.two))
    (twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht) (fun _ hz hs => twos_harm_strip k hz hs)) z

/-- The sign `−1` slip is the reflected `+1` slip. -/
theorem slip_minus_eq_iRefl (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) z =
      twosSlip k ((1, -1) - z) := by
  unfold ChildFrame.slip twosSlip
  rw [twos_F_iRefl k z, neg_one_smul]
  have e : (1, -1) - z + (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (1, -1) - (z + -(frameAt (List.replicate (k + 1) Digit.two)).shortShift) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg]
      ring
  rw [e, twos_F_iRefl]

/-- The reflection is an involution of the incoming sites: the parity of `(1,−1) − c` is that of `c`. -/
theorem evenSite_iRefl (c : Site) : EvenSite ((1, -1) - c) ↔ EvenSite c := by
  unfold EvenSite
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- The reflection exchanges the incoming sites: `incomingNeg (I − c) = I − incomingPos c`. -/
theorem incomingNeg_iRefl (c : Site) : incomingNeg ((1, -1) - c) = (1, -1) - incomingPos c := by
  unfold incomingNeg incomingPos
  by_cases hc : EvenSite c
  · have hI : EvenSite ((1, -1) - c) := (evenSite_iRefl c).mpr hc
    rw [if_pos hI, if_pos hc]
    ext <;> simp
  · have hI : ¬ EvenSite ((1, -1) - c) := fun h => hc ((evenSite_iRefl c).mp h)
    rw [if_neg hI, if_neg hc]
    ext <;> simp
    all_goals ring

/-- The reflection exchanges the incoming sites: `incomingPos (I − c) = I − incomingNeg c`. -/
theorem incomingPos_iRefl (c : Site) : incomingPos ((1, -1) - c) = (1, -1) - incomingNeg c := by
  unfold incomingNeg incomingPos
  by_cases hc : EvenSite c
  · have hI : EvenSite ((1, -1) - c) := (evenSite_iRefl c).mpr hc
    rw [if_pos hI, if_pos hc]
    ext <;> simp
    all_goals ring
  · have hI : ¬ EvenSite ((1, -1) - c) := fun h => hc ((evenSite_iRefl c).mp h)
    rw [if_neg hI, if_neg hc]
    ext <;> simp
    all_goals ring

/-- The laplacian is reflection invariant. -/
theorem laplacian_iRefl (k : ℕ) (c : Site) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) ((1, -1) - c) =
      laplacian (standardField (List.replicate (k + 1) Digit.two)) c := by
  unfold laplacian
  rw [incomingNeg_iRefl, incomingPos_iRefl, twos_F_iRefl, twos_F_iRefl, twos_F_iRefl]
  ring

/-- The reflection maps incoming edges to incoming edges. -/
theorem edge_iRefl (i c : Site) : Edge i c → Edge ((1, -1) - i) ((1, -1) - c) := by
  intro h
  unfold Edge at h ⊢
  rcases h with h | h
  · exact Or.inr (by rw [h, incomingPos_iRefl])
  · exact Or.inl (by rw [h, incomingNeg_iRefl])

/-- **The black branch for the sign `−1`.** At a black centre `c` the sign `−1` slip does not increase along its inputs. -/
theorem twosSlipM_black (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {c i : Site}
    (hl : laplacian (standardField (List.replicate (k + 1) Digit.two)) c = -1) (he : Edge i c) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) c := by
  rw [slip_minus_eq_iRefl, slip_minus_eq_iRefl]
  apply FLatticePaper.TwosEPolicy.twosSlip_nonincreasing k hagree hperiod
  left
  exact ⟨by rw [laplacian_iRefl]; exact hl, edge_iRefl i c he⟩


open FLatticePaper.TwosEPolicy

set_option maxHeartbeats 400000 in
/-- The east candidate for the sign -1: the reflected pair steps west. -/
theorem twosSlip_cand_E_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hE : CandE (2 * (k : ℤ) + 4) u1 u2) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - 1, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - 0) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandE at hE
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The west candidate for the sign -1. -/
theorem twosSlip_cand_W_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hW : CandW (2 * (k : ℤ) + 4) u1 u2) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - -1, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - 0) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandW at hW
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The low band candidate below its middle row. -/
theorem twosSlip_cand_low_down_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hL : CandLow (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - 0, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - -1) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandLow at hL
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The low band candidate above its middle row. -/
theorem twosSlip_cand_low_up_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hL : CandLow (2 * (k : ℤ) + 4) u1 u2) (hm : ¬ u2 < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - 0, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - 1) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandLow at hL
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The high band candidate below its middle row. -/
theorem twosSlip_cand_high_down_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hH : CandHigh (2 * (k : ℤ) + 4) u1 u2) (hm : u2 < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - 0, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - -1) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandHigh at hH
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The high band candidate above its middle row. -/
theorem twosSlip_cand_high_up_minus (k : ℕ) {u1 u2 : ℤ} (_hn : NativeT (2 * (k : ℤ) + 4) u1 u2) (hH : CandHigh (2 * (k : ℤ) + 4) u1 u2) (hm : ¬ u2 < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k ((2 * (k : ℤ) + 4) - u1 - 0, 3 * (2 * (k : ℤ) + 4) - 2 - u2 - 1) ≤ twosSlip k ((2 * (k : ℤ) + 4) - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  unfold CandHigh at hH
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega


/-- The guard dispatch of the candidate branch: the reflected candidate pair steps `−δ` from `p`. -/
theorem twosSlip_cand_dispatch (k : ℕ) {u1 u2 : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) u1 u2)
    (hg : CandGuard (2 * (k : ℤ) + 4) u1 u2) :
    twosSlip k (2 * (k : ℤ) + 4 - u1 - (candDisp (2 * (k : ℤ) + 4) u1 u2).1,
      3 * (2 * (k : ℤ) + 4) - 2 - u2 - (candDisp (2 * (k : ℤ) + 4) u1 u2).2) ≤
      twosSlip k (2 * (k : ℤ) + 4 - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) := by
  rcases hg with hL | hH | hE | hW
  · by_cases hm : u2 < 2 * (k : ℤ) + 4 - 1
    · rw [candDisp_low_down hL hm]
      dsimp only
      exact twosSlip_cand_low_down_minus k hn hL hm
    · rw [candDisp_low_up hL hm]
      dsimp only
      exact twosSlip_cand_low_up_minus k hn hL hm
  · by_cases hm : u2 < 2 * (2 * (k : ℤ) + 4) - 1
    · rw [candDisp_high_down hH hm]
      dsimp only
      exact twosSlip_cand_high_down_minus k hn hH hm
    · rw [candDisp_high_up hH hm]
      dsimp only
      exact twosSlip_cand_high_up_minus k hn hH hm
  · rw [candDisp_E hE]
    dsimp only
    exact twosSlip_cand_E_minus k hn hE
  · rw [candDisp_W hW]
    dsimp only
    exact twosSlip_cand_W_minus k hn hW

/-- **The candidate branch for the sign `−1`.** -/
theorem twosSlipM_cand (k : ℕ) {c i : Site}
    (hT : ∃ u : Site, AliasOf (2 * (k : ℤ) + 4) c u ∧ NativeT (2 * (k : ℤ) + 4) u.1 u.2 ∧
      CandGuard (2 * (k : ℤ) + 4) u.1 u.2 ∧
      i = (c.1 + (candDisp (2 * (k : ℤ) + 4) u.1 u.2).1, c.2 + (candDisp (2 * (k : ℤ) + 4) u.1 u.2).2)) :
    (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) i ≤
      (frameAt (List.replicate (k + 1) Digit.two)).slip (standardField (List.replicate (k + 1) Digit.two)) (-1) c := by
  obtain ⟨⟨u1, u2⟩, ⟨i', l, hu⟩, hn, hg, hi⟩ := hT
  have hu1 : u1 = c.1 - i' * (2 * (k : ℤ) + 4 + 1) + 2 * l := congrArg Prod.fst hu
  have hu2 : u2 = c.2 - i' * (2 * (k : ℤ) + 4 - 1) - 2 * (2 * (k : ℤ) + 4) * l := congrArg Prod.snd hu
  have key := twosSlip_cand_dispatch k hn hg
  rw [slip_minus_eq_iRefl, slip_minus_eq_iRefl]
  have hL1 : ((1 : ℤ), (-1 : ℤ)) - c = (2 * (k : ℤ) + 4 - u1, 3 * (2 * (k : ℤ) + 4) - 2 - u2) +
      ((-i' - 1) * (2 * (k : ℤ) + 5) + (-1 - l) * (-2), (-i' - 1) * (2 * (k : ℤ) + 3) + (-1 - l) * (4 * (k : ℤ) + 8)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sub]
      rw [hu1]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub]
      rw [hu2]
      ring
  have hL2 : ((1 : ℤ), (-1 : ℤ)) - i = (2 * (k : ℤ) + 4 - u1 - (candDisp (2 * (k : ℤ) + 4) u1 u2).1,
      3 * (2 * (k : ℤ) + 4) - 2 - u2 - (candDisp (2 * (k : ℤ) + 4) u1 u2).2) +
      ((-i' - 1) * (2 * (k : ℤ) + 5) + (-1 - l) * (-2), (-i' - 1) * (2 * (k : ℤ) + 3) + (-1 - l) * (4 * (k : ℤ) + 8)) := by
    rw [hi]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sub]
      rw [hu1]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub]
      rw [hu2]
      ring
  rw [hL1, hL2, twosSlip_lattice, twosSlip_lattice]
  linarith [key]


/-- The lattice shift of the slip: `D(Y) = D(X) + 2j` when `Y = X + (iU + jV)`. -/
theorem twosSlip_shift_eq (k : ℕ) (X Y : Site) (i j : ℤ)
    (h : Y = X + (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) :
    twosSlip k Y = twosSlip k X + 2 * j := by
  rw [h]
  exact twosSlip_lattice k X i j

set_option maxHeartbeats 400000 in
/-- The free class `H_0`: the slip at `(a−1, 3a−3)` is at most that at `(a−1, 3a−2)`. -/
theorem twosSlip_famH0 (k : ℕ) :
    twosSlip k (2 * (k : ℤ) + 4 - 1, 3 * (2 * (k : ℤ) + 4) - 3) ≤
      twosSlip k (2 * (k : ℤ) + 4 - 1, 3 * (2 * (k : ℤ) + 4) - 2) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The free class `H_{a+1}`: the slip at `(−1, 2a−1)` is at most that at `(−1, 2a)`. -/
theorem twosSlip_famHa1 (k : ℕ) :
    twosSlip k (-1, 2 * (2 * (k : ℤ) + 4) - 1) ≤ twosSlip k (-1, 2 * (2 * (k : ℤ) + 4)) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The free class `V_0`: the slip at `(a−1, 3a−2)` is at most that at `(a, 3a−2)`. -/
theorem twosSlip_famV0 (k : ℕ) :
    twosSlip k (2 * (k : ℤ) + 4 - 1, 3 * (2 * (k : ℤ) + 4) - 2) ≤
      twosSlip k (2 * (k : ℤ) + 4, 3 * (2 * (k : ℤ) + 4) - 2) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The generic free class `H_x = (x, x−2)`, `2 ≤ x ≤ a`: the slip at `(a+1−x, a−x)` is at most that at `(a+2−x, a−x)`. -/
theorem twosSlip_famH (k : ℕ) {x : ℤ} (hx1 : 2 ≤ x) (hx2 : x ≤ 2 * (k : ℤ) + 4) :
    twosSlip k (2 * (k : ℤ) + 4 + 1 - x, 2 * (k : ℤ) + 4 - x) ≤
      twosSlip k (2 * (k : ℤ) + 4 + 2 - x, 2 * (k : ℤ) + 4 - x) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The even vertical class `V_{0,y}` with `y` even: the slip at `(0, 2a−1−y)` is at most that at `(−1, 2a−1−y)`. -/
theorem twosSlip_famVe (k : ℕ) {y : ℤ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2 * (k : ℤ) + 4 - 1) (hp : y % 2 = 0) :
    twosSlip k (0, 2 * (2 * (k : ℤ) + 4) - 1 - y) ≤ twosSlip k (-1, 2 * (2 * (k : ℤ) + 4) - 1 - y) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The odd vertical class `V_{0,y}` with `y` odd: the slip at `(a, 3a−3−y)` is at most that at `(a, 3a−2−y)`. -/
theorem twosSlip_famVo (k : ℕ) {y : ℤ} (hy1 : 1 ≤ y) (hy2 : y ≤ 2 * (k : ℤ) + 4 - 1) (hp : y % 2 = 1) :
    twosSlip k (2 * (k : ℤ) + 4, 3 * (2 * (k : ℤ) + 4) - 3 - y) ≤
      twosSlip k (2 * (k : ℤ) + 4, 3 * (2 * (k : ℤ) + 4) - 2 - y) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega

set_option maxHeartbeats 400000 in
/-- The even vertical class `V_{−1,y}` with `y−1` even: the slip at `(1, 2a−1−y)` is at most that at `(0, 2a−1−y)`. -/
theorem twosSlip_famV1e (k : ℕ) {y : ℤ} (hy1 : 2 * (k : ℤ) + 4 ≤ y) (hy2 : y < 2 * (2 * (k : ℤ) + 4))
    (hp : (y - 1) % 2 = 0) :
    twosSlip k (1, 2 * (2 * (k : ℤ) + 4) - 1 - y) ≤ twosSlip k (0, 2 * (2 * (k : ℤ) + 4) - 1 - y) := by
  apply twosSlip_le_of_bands k
  · rw [twosKey_pos]
    omega
  · rw [twosKey_pos]
    omega
  · intro h
    unfold TwosSlipZ2 at h ⊢
    omega
  · intro h
    unfold TwosSlipZ0 at h ⊢
    omega


end FLatticePaper.Induction
