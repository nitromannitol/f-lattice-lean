import FLatticePaper.Plane.Induction.FreeEnum

/-! Task 72 / Q29, item 5 of the raw-cut audit: the V labels of the free cut step by one ordinate.

The labelling `vAt base j = base (j mod L) + (j div L) · V` (`FreeEnum.vAt`) has `(vAt base j).2 = j` (`FreeEnum.vAt_snd`), with `base r`
the point of ordinate `r` on the period (`FreeEnum.exists_base`). Consecutive labels therefore sit on consecutive ordinates, and each
label on the period is a point of the free V cut. -/

namespace FLatticePaper.VCutSteps

open FLatticePaper FLatticePaper.Induction FLatticePaper.FreeEnum

/-- **The ordinate of the label `V_j` is `j`.** -/
theorem vAt_ordinate (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r).2 = r) (j : ℤ) :
    (vAt frame base j).2 = j :=
  vAt_snd frame base hbase j

/-- **Consecutive V roots step by one ordinate.** -/
theorem vAt_ordinate_succ (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r).2 = r) (j : ℤ) :
    (vAt frame base (j + 1)).2 = (vAt frame base j).2 + 1 := by
  rw [vAt_ordinate frame base hbase, vAt_ordinate frame base hbase]

/-- **Every label on the period is a free V point**, for a base chosen from the cut. -/
theorem vAt_mem_freeV (frame : ChildFrame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r) ∈ frame.freeV ∧ (base r).2 = r)
    (j : ℤ) (hj : 0 ≤ j ∧ j < period frame) :
    vAt frame base j ∈ frame.freeV := by
  rw [vAt_eq_base frame base j hj]
  exact (hbase j hj.1 hj.2).1

end FLatticePaper.VCutSteps
