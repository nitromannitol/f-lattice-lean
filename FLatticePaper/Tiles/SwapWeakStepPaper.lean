import FLatticePaper.Tiles.SwapBaseInputAssembly
import FLatticePaper.Tiles.BaseWeakInputPaper
import FLatticePaper.Tiles.TileSlopeZeroPaper
import FLatticePaper.Tiles.MixedCompatGeneral
import FLatticePaper.Tiles.GlueColumns
import FLatticePaper.Tiles.SwapContainPaper
import FLatticePaper.Tiles.SwapVacuousTerm

/-! # The weak step for the text data, from the vacuous families

`WeakStepInput D` for the paper data, chaining `WeakStepAssembly.weakStep_paper` with the paper-data named inputs:
`BaseWeakInput` (`BaseWeakInputPaper.baseWeakInput_paper`), `TileSlopeZero` (`TileSlopeZeroPaper.tileSlopeZero_paper`),
`MixedCompatInput` (`MixedCompatGeneral.mixedCompatInput`), `GlueRespectsInput` and `GlueLatticeInput` (`GlueColumns`), and
`GlueFullInput` from `SameParentInput` (`GlueFull.glueFullInput_of`, `GlueFull.sameParent_of`). The only remaining input is the
vacuous families `SwapVacuous`, through `SwapBaseInput` (`SwapBaseInputAssembly.swapBaseInput_of`). -/

namespace FLatticePaper.Tiles.SwapWeakStepPaper

open FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily

/-- The weak step of the joint induction for the paper data, from the vacuous families `V`, with the paper weak data `hS` and
the paper alternate base `hA` (the inputs of `weakStep_paper` that depend on them). -/
theorem weakStepInput_paper_of (V : SwapVacuousSpec.SwapVacuous) (D : JointData)
    (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) :
    JointInduction.WeakStepInput D := by
  have hsl : WeakStepAssembly.TileSlopeZero D := TileSlopeZeroPaper.tileSlopeZero_paper D hS hA
  have hmc : WeakStepAssembly.MixedCompatInput D := MixedCompatGeneral.mixedCompatInput D hS hA
  have hgr : WeakStepAssembly.GlueRespectsInput D := GlueColumns.glueRespectsInput_paper D hS
  have hgl : WeakStepAssembly.GlueLatticeInput D := GlueColumns.glueLatticeInput_paper D hS hsl
  have hsp : GlueFull.SameParentInput D :=
    GlueFull.sameParent_of D hS (GlueFull.sameDisjoint_paper D) (SwapContainPaper.swapContain_paper D)
      (SwapBaseInputAssembly.swapBaseInput_of V D)
  have hgf : WeakStepAssembly.GlueFullInput D := GlueFull.glueFullInput_of D hS hsl hsp
  exact WeakStepAssembly.weakStep_paper D hS BaseWeakInputPaper.baseWeakInput_paper hsl hmc hgr hgl hgf

/-- **The weak step for the paper data, with no vacuity input.** The vacuous families are `SwapVacuousTerm.swapVacuous_term`
(the seven vacuity fields, proved in `SwapVacuousTerm` and `SwapVacuousV27`). -/
theorem weakStepInput_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) : JointInduction.WeakStepInput D :=
  weakStepInput_paper_of SwapVacuousTerm.swapVacuous_term D hS hA

end FLatticePaper.Tiles.SwapWeakStepPaper
