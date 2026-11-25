import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.FanTerminal

/-! # The first exit of a fan with the cone window (Q23, step 2: FanTerminal with the star-restricted cap in place of `hwin`)

The fan of a window root `v0` (open rectangle and cone, `CapRay.ConeRoot`) leaves the window at a first point `w`. The window
`WindowOn (openRect ∧ ConeRoot) F (parabolaField b_y)` is `CapRay.cone_window`, so the steps from window roots are fan steps
(`fan_path_exists`). A step from a window root to an open contact is again a window root (`CapRay.fan_next_P`, the two height bounds of
step 1), so the first point outside the window is not open: it is a boundary contact on the closed polygon (`rectInputs`). -/

namespace FLatticePaper.ConeTerminal

open FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanPropagation FLatticePaper.CapRay

/-- The window roots are finite (the open rectangle is). -/
theorem cone_finite (frame : ChildFrame) (b : Site) (K : ℕ) :
    {c | frame.openRect c ∧ ConeRoot b K c}.Finite :=
  (FLatticePaper.FanTerminal.openRect_finite frame).subset (fun _ hc => hc.1)

/-- **The first exit of the cone fan** (step 2): from a window root `v0` that is a contact, the fan leaves the window at a contact `w`
on the closed polygon which is not open. -/
theorem fan_terminal_cone {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b)
    {S : Set Site} (hfort : IsIncomingFort F S)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = parabolaField b.2 v0)
    (hv0P : frame.openRect v0 ∧ ConeRoot b K v0) :
    ∃ w : Site, w ∈ S ∧ F w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w := by
  have hwin := cone_window frame hP hsig hs K hcap b hb
  obtain ⟨next, hr⟩ := fan_path_exists hfort (parabola_binary b.2) (fun z hz => parabola_lap_even b.2 z hz) hwin
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr (cone_finite frame b K) ⟨v0, hv0S, hv0c⟩
  cases k with
  | zero => exact absurd hv0P hk
  | succ k' =>
    have hpredP := hj k' (Nat.lt_succ_self k')
    have hsucc : next^[k' + 1] ⟨v0, hv0S, hv0c⟩ = next (next^[k'] ⟨v0, hv0S, hv0c⟩) :=
      Function.iterate_succ_apply' next k' _
    rw [hsucc] at hk
    have hcl : (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).1 ∈ frame.closedPolygon :=
      FLatticePaper.W1Exit.rectInputs frame _ hpredP.1 _ (hr _ hpredP).2
    have hout : ¬ frame.openRect (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).1 := fun hopen =>
      hk (fan_next_P frame hP hsig hs K hK2 hKs hKr hcap b hb _ _ hpredP (hr _ hpredP).2 (hr _ hpredP).1
        hopen (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).2.2)
    exact ⟨(next (next^[k'] ⟨v0, hv0S, hv0c⟩)).1, (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).2.1,
      (next (next^[k'] ⟨v0, hv0S, hv0c⟩)).2.2, hcl, hout⟩

/-- **The contradiction of the cone fan** (step 2, the form used by the fort argument): a fort with a window contact leaves the window at a
boundary contact, which the paid exclusion forbids. -/
theorem fan_terminal_cone_contradiction {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (b : Site) (hb : frame.child.num + 2 ≤ frame.tGrade b)
    {S : Set Site} (hfort : IsIncomingFort F S)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = parabolaField b.2 v0)
    (hv0P : frame.openRect v0 ∧ ConeRoot b K v0)
    (hpaid : ∀ w : Site, w ∈ frame.closedPolygon → ¬ frame.openRect w → w ∈ S →
      F w = parabolaField b.2 w → False) : False := by
  obtain ⟨w, hwS, hwc, hwcl, hwout⟩ :=
    fan_terminal_cone frame hP hsig hs K hK2 hKs hKr hcap b hb hfort v0 hv0S hv0c hv0P
  exact hpaid w hwcl hwout hwS hwc

/-- **The cone kind of starts** (the hypothesis `hcone` of `FreeRows.free_row_empty`): every window start `(v0, b)` with `t b ≥ N + 2`
and `ConeRoot b K v0`, touching its parabola, exits on a boundary contact of `S` on that parabola (`fan_terminal_cone`). The base `b`
is the H midpoint `H_i` in `E` (the note's `H_i − U` on `E − U`; `F (z + U) = F z`). -/
theorem cone_kind_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num) (K : ℕ)
    (hK2 : 2 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hfort : IsIncomingFort F S) :
    ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → F v0 = parabolaField b.2 v0 →
      frame.child.num + 2 ≤ frame.tGrade b → ConeRoot b K v0 →
      ∃ w : Site, w ∈ S ∧ F w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w :=
  fun v0 b hv0S hv0o hv0c hb hR =>
    fan_terminal_cone frame hP hsig hs K hK2 hKs hKr hcap b hb hfort v0 hv0S hv0c ⟨hv0o, hR⟩

end FLatticePaper.ConeTerminal
