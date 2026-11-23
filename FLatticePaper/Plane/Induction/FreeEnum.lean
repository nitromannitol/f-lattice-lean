import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The enumeration of the free V cut by ordinate (task 112, step (3), partial)

The free V cut `freeV` (the left boundary with the V spectrum, `S3FreeBoundary`) has one point on each ordinate `r` with `0 ≤ r < L`
(`L = d + n`): this is `CutOnePerOrdinate`, checked numerically on the 24 reduced child frames with `d ≤ 15` (not yet proved in Lean; the
proof needs the left-boundary floor arithmetic). Given a base `base r` (the point on ordinate `r`, `0 ≤ r < L`), the labels of Q13's insertion
extend by the deck, `V_{j+L} = V_j + V` (`V = Vdeck = (n−d, n+d)` shifts the ordinate by `L`):

  `vAt base j = base (j mod L) + (j div L) · V`.

Proved here: the period law `vAt (j + L) = vAt j + V`, the ordinate `(vAt base j).2 = j`, the existence of a base from the cut hypothesis, and
the coverage `z = base z.2` for `z ∈ freeV` on the period (the cut is one point per ordinate). The base's ordinate range `freeV ⊆ {0 ≤ y < L}`
is named (`freeV_ordinate`), as the sites of the rows are on one period. -/

namespace FLatticePaper.FreeEnum

open FLatticePaper FLatticePaper.Induction

/-- The period `L = d + n` (the ordinate shift of the transverse deck `V`). -/
def period (frame : ChildFrame) : ℤ := frame.child.den + frame.child.num

theorem period_pos (frame : ChildFrame) : 0 < period frame := by
  obtain ⟨hpos, hnlt, -, -, -⟩ := frame.child_facts
  unfold period
  omega

theorem Vdeck_snd (frame : ChildFrame) : (Vdeck frame).2 = period frame := by
  unfold Vdeck period
  ring

/-- **The named cut hypothesis**: on each ordinate `0 ≤ r < L` of the period, the free V cut has exactly one point (numerically checked). -/
def CutOnePerOrdinate (frame : ChildFrame) : Prop :=
  ∀ r : ℤ, 0 ≤ r → r < period frame → ∃! x : ℤ, (x, r) ∈ frame.freeV

/-- **The labelling of the V cut** by the base and the deck: `vAt base j = base (j mod L) + (j div L) · V`. -/
def vAt (frame : ChildFrame) (base : ℤ → Site) (j : ℤ) : Site :=
  ((base (j % period frame)).1 + (j / period frame) * (Vdeck frame).1,
    (base (j % period frame)).2 + (j / period frame) * (Vdeck frame).2)

/-- **The period law**: `V_{j+L} = V_j + V`. -/
theorem vAt_add_period (frame : ChildFrame) (base : ℤ → Site) (j : ℤ) :
    vAt frame base (j + period frame) = vAt frame base j + Vdeck frame := by
  have hL : period frame ≠ 0 := (period_pos frame).ne'
  have h1 : (j + period frame) % period frame = j % period frame := by simp
  have h2 : (j + period frame) / period frame = j / period frame + 1 := by
    rw [show j + period frame = j + 1 * period frame by ring, Int.add_mul_ediv_right _ _ hL]
  unfold vAt
  rw [h1, h2]
  ext
  · simp only [Prod.fst_add]
    ring
  · simp only [Prod.snd_add]
    ring

/-- **The ordinate law**: `(V_j).2 = j`, when the base has ordinate `r` on `0 ≤ r < L`. -/
theorem vAt_snd (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r).2 = r) (j : ℤ) :
    (vAt frame base j).2 = j := by
  have hL := period_pos frame
  have hlo : 0 ≤ j % period frame := Int.emod_nonneg _ hL.ne'
  have hhi : j % period frame < period frame := Int.emod_lt_of_pos _ hL
  unfold vAt
  show (base (j % period frame)).2 + (j / period frame) * (Vdeck frame).2 = j
  rw [hbase _ hlo hhi, Vdeck_snd]
  have := Int.emod_def j (period frame)
  linarith

/-- **A base exists** from the cut hypothesis: a point of `freeV` on each ordinate of the period. -/
theorem exists_base (frame : ChildFrame) (hcut : CutOnePerOrdinate frame) :
    ∃ base : ℤ → Site, ∀ r : ℤ, 0 ≤ r → r < period frame → (base r) ∈ frame.freeV ∧ (base r).2 = r := by
  have key : ∀ r : ℤ, ∃ p : Site, 0 ≤ r → r < period frame → p ∈ frame.freeV ∧ p.2 = r := by
    intro r
    by_cases hr : 0 ≤ r ∧ r < period frame
    · obtain ⟨x, hx, -⟩ := hcut r hr.1 hr.2
      exact ⟨(x, r), fun _ _ => ⟨hx, rfl⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
  choose base hbase using key
  exact ⟨base, fun r h1 h2 => hbase r h1 h2⟩

/-- **Coverage of the period**: a point of `freeV` whose ordinate lies in `[0, L)` is the base point of its ordinate (uniqueness on the cut). -/
theorem freeV_eq_base (frame : ChildFrame) (hcut : CutOnePerOrdinate frame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r) ∈ frame.freeV ∧ (base r).2 = r)
    {z : Site} (hz : z ∈ frame.freeV) (hord : 0 ≤ z.2 ∧ z.2 < period frame) :
    z = base z.2 := by
  obtain ⟨x, -, hxu⟩ := hcut z.2 hord.1 hord.2
  obtain ⟨hb, hbo⟩ := hbase z.2 hord.1 hord.2
  have h1 : z.1 = x := hxu z.1 (show (z.1, z.2) ∈ frame.freeV from hz)
  have hb' : ((base z.2).1, z.2) ∈ frame.freeV := by
    have e : ((base z.2).1, z.2) = base z.2 := Prod.ext rfl hbo.symm
    rw [e]
    exact hb
  have h2 : (base z.2).1 = x := hxu (base z.2).1 hb'
  exact Prod.ext (by rw [h1, h2]) hbo.symm

/-- **The labels are the enumeration**: the V labels `V_j` of the period are the base points, and the deck extension is `vAt`. -/
theorem vAt_eq_base (frame : ChildFrame) (base : ℤ → Site) (j : ℤ) (hj : 0 ≤ j ∧ j < period frame) :
    vAt frame base j = base j := by
  unfold vAt
  have hm : j % period frame = j := Int.emod_eq_of_lt hj.1 hj.2
  have hd : j / period frame = 0 := Int.ediv_eq_zero_of_lt hj.1 hj.2
  rw [hm, hd]
  simp

end FLatticePaper.FreeEnum
