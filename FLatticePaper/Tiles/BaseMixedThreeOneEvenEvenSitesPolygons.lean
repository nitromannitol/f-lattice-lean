import FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSites
import FLatticePaper.Tiles.CorrectedBaseShears
import FLatticePaper.Tiles.CorrectedCutoffTwelve

/-! The finite inequalities of the base comparison evaluated on the actual physical polygons. -/

namespace FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesPolygons

open FLatticePaper.Farey FLatticePaper.Construction CorrectedFiniteFaces CorrectedLevelTests
open CorrectedRegisterDiagram (Probe)
open CorrectedBaseShears CorrectedPlacedDiagram
open BaseMixedThreeOneEvenEvenSites (Register Frame contains test arity)

private theorem probe_ext {u v : Probe} (a : u.w=v.w) (b : u.v=v.v) (c : u.width=v.width) (d : u.slope=v.slope) : u=v := by
  cases u; cases v; simp_all

private theorem agrees {l v : Line} (eq : l=v) : inside 12 l ↔ (Test.line 12 v).holds := by subst v; rfl

def physicalSite (r : Register) : Site := (r.X-r.Y,r.Y)
def shape (d : ℤ) : ℕ → Block
  | 0 => ⟨((0),(0)),((3*d+1),(3)),((-2*d+1),(2*d+3)),0,0⟩
  | 9 => ⟨((2),(d+2)),((3*d+1),(3)),((-2*d+1),(2*d+3)),0,0⟩
  | 1 => ⟨((0),(0)),((2*d),(2)),((-d+1),(d+1)),0,0⟩
  | 2 => ⟨((3),(2*d+5)),((2*d),(2)),((-d+1),(d+1)),0,0⟩
  | 3 => ⟨((2*d),(2)),((d+1),(1)),((-d),(d+2)),0,0⟩
  | 4 => ⟨((2*d+2),(d+4)),((d+1),(1)),((-d),(d+2)),0,0⟩
  | 5 => ⟨((-d+1),(d+1)),((d+1),(1)),((-d),(d+2)),0,0⟩
  | 6 => ⟨((-d+3),(2*d+3)),((d+1),(1)),((-d),(d+2)),0,0⟩
  | _ => ⟨0,0,0,0,0⟩

def measured (r : Register) : ℕ → ℕ → Probe
  | 0, 0 => ⟨(r.Y+1),(r.X+2),(3*r.d+4),3⟩
  | 0, 1 => ⟨(-2*r.d+r.Y-3),(r.X-6),(3*r.d+4),3⟩
  | 0, 2 => ⟨(r.X),(r.Y),(2*r.d+3),4⟩
  | 0, 3 => ⟨(-3*r.d+r.X-4),(r.Y-2),(2*r.d+3),4⟩
  | 9, 0 => ⟨(-r.d+r.Y-1),(-r.d+r.X-2),(3*r.d+4),3⟩
  | 9, 1 => ⟨(-3*r.d+r.Y-5),(-r.d+r.X-10),(3*r.d+4),3⟩
  | 9, 2 => ⟨(-r.d+r.X-4),(-r.d+r.Y-2),(2*r.d+3),4⟩
  | 9, 3 => ⟨(-4*r.d+r.X-8),(-r.d+r.Y-4),(2*r.d+3),4⟩
  | 1, 0 => ⟨(r.Y+1),(r.X+2),(2*r.d+2),2⟩
  | 1, 1 => ⟨(-r.d+r.Y-1),(r.X-4),(2*r.d+2),2⟩
  | 1, 2 => ⟨(r.X),(r.Y),(r.d+1),2⟩
  | 1, 3 => ⟨(-2*r.d+r.X-2),(r.Y-1),(r.d+1),2⟩
  | 2, 0 => ⟨(-2*r.d+r.Y-4),(-2*r.d+r.X-6),(2*r.d+2),2⟩
  | 2, 1 => ⟨(-3*r.d+r.Y-6),(-2*r.d+r.X-12),(2*r.d+2),2⟩
  | 2, 2 => ⟨(-2*r.d+r.X-8),(-2*r.d+r.Y-5),(r.d+1),2⟩
  | 2, 3 => ⟨(-4*r.d+r.X-10),(-2*r.d+r.Y-6),(r.d+1),2⟩
  | 3, 0 => ⟨(r.Y-1),(-2*r.d+r.X),(r.d+2),1⟩
  | 3, 1 => ⟨(-r.d+r.Y-4),(-2*r.d+r.X-6),(r.d+2),1⟩
  | 3, 2 => ⟨(-2*r.d+r.X-2),(r.Y-2),(r.d+2),2⟩
  | 3, 3 => ⟨(-3*r.d+r.X-4),(r.Y-2),(r.d+2),2⟩
  | 4, 0 => ⟨(-r.d+r.Y-3),(-3*r.d+r.X-4),(r.d+2),1⟩
  | 4, 1 => ⟨(-2*r.d+r.Y-6),(-3*r.d+r.X-10),(r.d+2),1⟩
  | 4, 2 => ⟨(-3*r.d+r.X-6),(-r.d+r.Y-4),(r.d+2),2⟩
  | 4, 3 => ⟨(-4*r.d+r.X-8),(-r.d+r.Y-4),(r.d+2),2⟩
  | 5, 0 => ⟨(-r.d+r.Y),(r.X),(r.d+2),1⟩
  | 5, 1 => ⟨(-2*r.d+r.Y-3),(r.X-6),(r.d+2),1⟩
  | 5, 2 => ⟨(r.X-2),(-r.d+r.Y-1),(r.d+2),2⟩
  | 5, 3 => ⟨(-r.d+r.X-4),(-r.d+r.Y-1),(r.d+2),2⟩
  | 6, 0 => ⟨(-2*r.d+r.Y-2),(-r.d+r.X-4),(r.d+2),1⟩
  | 6, 1 => ⟨(-3*r.d+r.Y-5),(-r.d+r.X-10),(r.d+2),1⟩
  | 6, 2 => ⟨(-r.d+r.X-6),(-2*r.d+r.Y-3),(r.d+2),2⟩
  | 6, 3 => ⟨(-2*r.d+r.X-8),(-2*r.d+r.Y-3),(r.d+2),2⟩
  | _, _ => ⟨0,0,0,0⟩

private theorem valid0 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 0 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 0 3).w≤(measured r 0 2).w+24
    norm_num [measured]; omega
  · change (measured r 0 1).w≤(measured r 0 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon0 (r : Register) (h : Frame r) : (shape r.d 0).mem (physicalSite r) ↔ contains r 0 := by
  let B := shape r.d 0
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 0 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 0 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 0
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid0 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 0 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 0 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid9 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 9 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 9 3).w≤(measured r 9 2).w+24
    norm_num [measured]; omega
  · change (measured r 9 1).w≤(measured r 9 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon9 (r : Register) (h : Frame r) : (shape r.d 9).mem (physicalSite r) ↔ contains r 9 := by
  let B := shape r.d 9
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 9 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 9 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 9
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid9 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 9 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 9 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid1 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 1 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 1 3).w≤(measured r 1 2).w+24
    norm_num [measured]; omega
  · change (measured r 1 1).w≤(measured r 1 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon1 (r : Register) (h : Frame r) : (shape r.d 1).mem (physicalSite r) ↔ contains r 1 := by
  let B := shape r.d 1
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 1 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 1 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 1
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid1 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 1 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 1 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid2 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 2 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 2 3).w≤(measured r 2 2).w+24
    norm_num [measured]; omega
  · change (measured r 2 1).w≤(measured r 2 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon2 (r : Register) (h : Frame r) : (shape r.d 2).mem (physicalSite r) ↔ contains r 2 := by
  let B := shape r.d 2
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 2 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 2 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 2
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid2 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 2 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 2 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid3 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 3 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 3 3).w≤(measured r 3 2).w+24
    norm_num [measured]; omega
  · change (measured r 3 1).w≤(measured r 3 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon3 (r : Register) (h : Frame r) : (shape r.d 3).mem (physicalSite r) ↔ contains r 3 := by
  let B := shape r.d 3
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 3 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 3 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 3
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid3 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 3 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 3 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid4 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 4 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 4 3).w≤(measured r 4 2).w+24
    norm_num [measured]; omega
  · change (measured r 4 1).w≤(measured r 4 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon4 (r : Register) (h : Frame r) : (shape r.d 4).mem (physicalSite r) ↔ contains r 4 := by
  let B := shape r.d 4
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 4 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 4 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 4
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid4 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 4 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 4 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid5 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 5 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 5 3).w≤(measured r 5 2).w+24
    norm_num [measured]; omega
  · change (measured r 5 1).w≤(measured r 5 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon5 (r : Register) (h : Frame r) : (shape r.d 5).mem (physicalSite r) ↔ contains r 5 := by
  let B := shape r.d 5
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 5 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 5 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 5
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid5 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 5 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 5 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid6 (r : Register) (h : Frame r) :
    CorrectedCutoffTwelve.Fits (fun j : Fin 4 => measured r 6 j.val) := by
  have d := h.f0
  constructor
  · change (measured r 6 3).w≤(measured r 6 2).w+24
    norm_num [measured]; omega
  · change (measured r 6 1).w≤(measured r 6 0).w+24
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,CorrectedRegisterFaces.low,CorrectedRegisterFaces.high] <;> omega

theorem polygon6 (r : Register) (h : Frame r) : (shape r.d 6).mem (physicalSite r) ↔ contains r 6 := by
  let B := shape r.d 6
  let z := physicalSite r
  have d := h.f0
  have dp := h.f1
  have site := h.f2
  have p : CorrectedCellsBands.oddSite (z-B.c)=false := by
    dsimp [z,B,physicalSite,shape,CorrectedCellsBands.oddSite]; first | exact decide_eq_true_iff.mpr (by omega) | (simp; omega)
  have A : CorrectedCellsBands.probe B.a false=horizontal false 0 := by
    simp [B,shape,horizontal,CorrectedCellsBands.probe]; all_goals omega
  have V : CorrectedCellsBands.probe (CorrectedCellsBands.transverse B.b) (!false)=vertical false 0 := by
    rfl
  have m (j : Fin 4) : probes true B z false 0 j=measured r 6 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [probes,CorrectedBaseShears.read,shear,point,horizontal,vertical,measured,B,z,shape,physicalSite,mulI,Fin.ext_iff] <;> ring
  have desc : probes true B z false 0=fun j : Fin 4 => measured r 6 j.val := funext m
  change CorrectedCellsBands.Band B.a B.b 0 0 (z-B.c) ↔ contains r 6
  rw [CorrectedBaseShears.band true B.a B.b B.c z false 0 p A V]
  change CorrectedRegisterFaces.exact (probes true B z false 0) ↔ _
  rw [desc,CorrectedCutoffTwelve.exact_iff _ (valid6 r h)]
  change (∀ j : Fin 4, inside 12 ((measured r 6 j.val).line (decide (j.val%2=1)))) ↔
    ∀ j : Fin 4, (test r 6 j.val).holds
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

end FLatticePaper.Tiles.BaseMixedThreeOneEvenEvenSitesPolygons
