import FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSites
import FLatticePaper.Tiles.CorrectedRegisterFaces

/-! Physical determinant inequalities for every polygon of the pure corrected comparison. -/

namespace FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesPolygons

open CorrectedRegisterDiagram CorrectedRegisterFaces CorrectedLevelTests CorrectedFiniteFaces
open BaseCorrectedThreeOneShortEvenSites (Frame test contains)

private theorem probe_ext {u v : Probe} (w : u.w=v.w) (q : u.v=v.v) (a : u.width=v.width) (k : u.slope=v.slope) : u=v := by
  cases u; cases v; simp_all

private theorem agrees {l v : Line} (eq : l=v) : l.holds ↔ (Test.line 4 v).holds := by
  subst v; cases l <;> rfl

def measured (r : Register) : ℕ → ℕ → Probe
  | 0, 0 => ⟨(r.d-r.n+r.Y),(r.S+r.d+r.X),(r.M+2*r.T+2*r.S),-2⟩
  | 0, 1 => ⟨(-r.M-2*r.T-2*r.S+2*r.n+r.Y),(r.S-r.d-r.n+r.X+1),(r.M+2*r.T+2*r.S),-2⟩
  | 0, 2 => ⟨(r.S+r.X),(r.Y),(r.M+2*r.T+2*r.S),-1⟩
  | 0, 3 => ⟨(-r.M-2*r.T-r.S-r.n+r.X),(r.d+r.n+r.Y+2),(r.M+2*r.T+2*r.S),-1⟩
  | 1, 0 => ⟨(-r.M+r.d-r.n+r.Y),(r.S+r.d+r.X),(r.T+r.S),-1⟩
  | 1, 1 => ⟨(-r.M-2*r.T-2*r.S+2*r.n+r.Y),(r.S-r.d-r.n+r.X+1),(r.T+r.S),-1⟩
  | 1, 2 => ⟨(r.S+r.X),(-r.M+r.Y),(2*r.T+2*r.S),-1⟩
  | 1, 3 => ⟨(-r.T-r.n+r.X),(-r.M+r.d+r.n+r.Y+1),(2*r.T+2*r.S),-1⟩
  | 2, 0 => ⟨(r.d-r.n+r.Y+1),(-r.M-r.T+r.d+r.X),(r.T+r.S),-1⟩
  | 2, 1 => ⟨(-2*r.T-2*r.S+2*r.n+r.Y+1),(-r.M-r.T-r.d-r.n+r.X+1),(r.T+r.S),-1⟩
  | 2, 2 => ⟨(-r.M-r.T+r.X),(r.Y+1),(2*r.T+2*r.S),-1⟩
  | 2, 3 => ⟨(-r.M-2*r.T-r.S-r.n+r.X),(r.d+r.n+r.Y+2),(2*r.T+2*r.S),-1⟩
  | 3, 0 => ⟨(r.d-r.n+r.Y),(r.S+r.d+r.X),(r.M),0⟩
  | 3, 1 => ⟨(-r.M+2*r.n+r.Y),(r.S-r.d-r.n+r.X),(r.M),0⟩
  | 3, 2 => ⟨(r.S+r.X),(r.Y),(r.M),0⟩
  | 3, 3 => ⟨(-r.M-r.n+r.X),(r.d+r.n+r.Y),(r.M),0⟩
  | 4, 0 => ⟨(-2*r.T-2*r.S+r.d-r.n+r.Y+2),(-2*r.T+r.d+r.X+1),(r.M),0⟩
  | 4, 1 => ⟨(-r.M-2*r.T-2*r.S+2*r.n+r.Y+2),(-2*r.T-r.d-r.n+r.X+1),(r.M),0⟩
  | 4, 2 => ⟨(-2*r.T+r.X+1),(-2*r.T-2*r.S+r.Y+2),(r.M),0⟩
  | 4, 3 => ⟨(-r.M-2*r.T-r.S-r.n+r.X+1),(-2*r.T-2*r.S+r.d+r.n+r.Y+2),(r.M),0⟩
  | 5, 0 => ⟨(r.d-r.n+r.Y),(-r.M+r.d+r.X),(r.T),-1⟩
  | 5, 1 => ⟨(-2*r.T+2*r.n+r.Y),(-r.M-r.d-r.n+r.X+1),(r.T),-1⟩
  | 5, 2 => ⟨(-r.M+r.X),(r.Y),(2*r.T),-1⟩
  | 5, 3 => ⟨(-r.M-r.T-r.n+r.X),(r.d+r.n+r.Y+1),(2*r.T),-1⟩
  | 6, 0 => ⟨(-r.M-2*r.S+r.d-r.n+r.Y+1),(-r.T+r.d+r.X),(r.T),-1⟩
  | 6, 1 => ⟨(-r.M-2*r.T-2*r.S+2*r.n+r.Y+1),(-r.T-r.d-r.n+r.X+1),(r.T),-1⟩
  | 6, 2 => ⟨(-r.T+r.X),(-r.M-2*r.S+r.Y+1),(2*r.T),-1⟩
  | 6, 3 => ⟨(-2*r.T-r.n+r.X),(-r.M-2*r.S+r.d+r.n+r.Y+2),(2*r.T),-1⟩
  | 7, 0 => ⟨(-r.M+r.d-r.n+r.Y+1),(-r.T+r.d+r.X),(r.T),-1⟩
  | 7, 1 => ⟨(-r.M-2*r.S+2*r.n+r.Y+1),(-r.T-r.d-r.n+r.X),(r.T),-1⟩
  | 7, 2 => ⟨(-r.T+r.X),(-r.M+r.Y+1),(r.M),0⟩
  | 7, 3 => ⟨(-2*r.T-r.n+r.X),(-r.M+r.d+r.n+r.Y+2),(r.M),0⟩
  | 8, 0 => ⟨(-2*r.T+r.d-r.n+r.Y),(-r.M+r.d+r.X+1),(r.T),-1⟩
  | 8, 1 => ⟨(-2*r.T-2*r.S+2*r.n+r.Y),(-r.M-r.d-r.n+r.X+1),(r.T),-1⟩
  | 8, 2 => ⟨(-r.M+r.X+1),(-2*r.T+r.Y),(r.M),0⟩
  | 8, 3 => ⟨(-r.M-r.T-r.n+r.X+1),(-2*r.T+r.d+r.n+r.Y+1),(r.M),0⟩
  | _, _ => ⟨0,0,0,0⟩

private theorem valid0 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 0 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 0 3).w≤(measured r 0 2).w+8
    norm_num [measured]; omega
  · change (measured r 0 1).w≤(measured r 0 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon0 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 0).probe r false 0) ↔
      ∀ j : Fin 4, (test r 0 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 0).probe r false 0 j = measured r 0 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid0 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid1 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 1 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 1 3).w≤(measured r 1 2).w+8
    norm_num [measured]; omega
  · change (measured r 1 1).w≤(measured r 1 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon1 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 1).probe r false 0) ↔
      ∀ j : Fin 4, (test r 1 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 1).probe r false 0 j = measured r 1 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid1 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid2 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 2 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 2 3).w≤(measured r 2 2).w+8
    norm_num [measured]; omega
  · change (measured r 2 1).w≤(measured r 2 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon2 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 2).probe r false 0) ↔
      ∀ j : Fin 4, (test r 2 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 2).probe r false 0 j = measured r 2 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid2 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid3 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 3 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 3 3).w≤(measured r 3 2).w+8
    norm_num [measured]; omega
  · change (measured r 3 1).w≤(measured r 3 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon3 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 3).probe r false 0) ↔
      ∀ j : Fin 4, (test r 3 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 3).probe r false 0 j = measured r 3 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid3 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid4 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 4 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 4 3).w≤(measured r 4 2).w+8
    norm_num [measured]; omega
  · change (measured r 4 1).w≤(measured r 4 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon4 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 4).probe r false 0) ↔
      ∀ j : Fin 4, (test r 4 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 4).probe r false 0 j = measured r 4 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid4 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid5 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 5 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 5 3).w≤(measured r 5 2).w+8
    norm_num [measured]; omega
  · change (measured r 5 1).w≤(measured r 5 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon5 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 5).probe r false 0) ↔
      ∀ j : Fin 4, (test r 5 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 5).probe r false 0 j = measured r 5 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid5 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid6 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 6 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 6 3).w≤(measured r 6 2).w+8
    norm_num [measured]; omega
  · change (measured r 6 1).w≤(measured r 6 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon6 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 6).probe r false 0) ↔
      ∀ j : Fin 4, (test r 6 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 6).probe r false 0 j = measured r 6 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid6 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid7 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 7 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 7 3).w≤(measured r 7 2).w+8
    norm_num [measured]; omega
  · change (measured r 7 1).w≤(measured r 7 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon7 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 7).probe r false 0) ↔
      ∀ j : Fin 4, (test r 7 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 7).probe r false 0 j = measured r 7 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid7 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

private theorem valid8 (r : Register) (h : Frame r) :
    Fits (fun j : Fin 4 => measured r 8 j.val) := by
  have f0 := h.f0
  have f1 := h.f1
  have f2 := h.f2
  have f3 := h.f3
  have f4 := h.f4
  have f5 := h.f5
  have f6 := h.f6
  have f7 := h.f7
  have f8 := h.f8
  have f9 := h.f9
  have f10 := h.f10
  have f11 := h.f11
  have f12 := h.f12
  constructor
  · change (measured r 8 3).w≤(measured r 8 2).w+8
    norm_num [measured]; omega
  · change (measured r 8 1).w≤(measured r 8 0).w+8
    norm_num [measured]; omega
  · intro j; fin_cases j <;> norm_num [measured] <;> omega
  · intro j; fin_cases j <;> norm_num [measured,low,high] <;> omega

theorem polygon8 (r : Register) (h : Frame r) :
    CorrectedRegisterFaces.exact ((corrected r true 1 false 8).probe r false 0) ↔
      ∀ j : Fin 4, (test r 8 j.val).holds := by
  have desc (j : Fin 4) : (corrected r true 1 false 8).probe r false 0 j = measured r 8 j.val := by
    fin_cases j <;> apply probe_ext <;>
      norm_num [corrected,Shape.probe,orientation,bias,displacement,FLatticePaper.Farey.mulI,measured,Prod.smul_mk,Fin.ext_iff] <;> ring
  rw [funext desc,exact_iff _ (valid8 r h)]
  apply forall_congr'; intro j
  fin_cases j <;> apply agrees <;> norm_num [measured,Probe.line] <;> omega

theorem part0 (r : Register) (h : Frame r) : contains r 0 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 0).probe r false 0) := by
  rw [polygon0 r h]
  rfl

theorem part1 (r : Register) (h : Frame r) : contains r 1 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 1).probe r false 0) := by
  rw [polygon1 r h]
  rfl

theorem part2 (r : Register) (h : Frame r) : contains r 2 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 2).probe r false 0) := by
  rw [polygon2 r h]
  rfl

theorem part3 (r : Register) (h : Frame r) : contains r 3 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 3).probe r false 0) := by
  rw [polygon3 r h]
  rfl

theorem part4 (r : Register) (h : Frame r) : contains r 4 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 4).probe r false 0) := by
  rw [polygon4 r h]
  rfl

theorem part5 (r : Register) (h : Frame r) : contains r 5 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 5).probe r false 0) := by
  rw [polygon5 r h]
  rfl

theorem part6 (r : Register) (h : Frame r) : contains r 6 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 6).probe r false 0) := by
  rw [polygon6 r h]
  rfl

theorem part7 (r : Register) (h : Frame r) : contains r 7 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 7).probe r false 0) ∧ (0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)) ∧ (0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)) ∧ (0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-2*r.n+r.Y+1)) ∧ (0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-r.d-2*r.n+r.Y+1)) := by
  rw [polygon7 r h]
  constructor
  · intro h
    change ∀ j : Fin 8, (test r 7 j.val).holds at h
    have c4 := h 4
    change (0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)) at c4
    have c5 := h 5
    change (0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)) at c5
    have c6 := h 6
    change (0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-2*r.n+r.Y+1)) at c6
    have c7 := h 7
    change (0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-r.d-2*r.n+r.Y+1)) at c7
    exact ⟨(fun j => h ⟨j.val,by have := j.isLt; change _ < 8; omega⟩), c4, c5, c6, c7⟩
  · intro h j
    change Fin 8 at j
    fin_cases j
    · exact h.1 0
    · exact h.1 1
    · exact h.1 2
    · exact h.1 3
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2

theorem part8 (r : Register) (h : Frame r) : contains r 8 ↔ CorrectedRegisterFaces.exact ((corrected r true 1 false 8).probe r false 0) ∧ (0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)) ∧ (0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)) ∧ (0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-2*r.n+r.Y+1)) ∧ (0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-r.d-2*r.n+r.Y+1)) := by
  rw [polygon8 r h]
  constructor
  · intro h
    change ∀ j : Fin 8, (test r 8 j.val).holds at h
    have c4 := h 4
    change (0 ≤ (4*r.T-r.d+r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d-r.n+2*r.X-1) ∨ 0 ≤ (r.M-r.d-r.Y-3) ∨ 0 ≤ (-r.M+r.d+r.Y+1)) at c4
    have c5 := h 5
    change (0 ≤ (2*r.T-r.X-1) ∨ 0 ≤ (-2*r.T+r.X-1) ∨ 0 ≤ (r.M-r.Y-3) ∨ 0 ≤ (-r.M+r.Y+1)) at c5
    have c6 := h 6
    change (0 ≤ (2*r.T-r.d-r.n-r.X-1) ∨ 0 ≤ (-2*r.T+r.d+r.n+r.X-1) ∨ 0 ≤ (r.M+2*r.S+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-2*r.n+r.Y+1)) at c6
    have c7 := h 7
    change (0 ≤ (4*r.T-r.d-3*r.n-2*r.X-1) ∨ 0 ≤ (-4*r.T+r.d+3*r.n+2*r.X-1) ∨ 0 ≤ (r.M+2*r.S+r.d+2*r.n-r.Y-3) ∨ 0 ≤ (-r.M-2*r.S-r.d-2*r.n+r.Y+1)) at c7
    exact ⟨(fun j => h ⟨j.val,by have := j.isLt; change _ < 8; omega⟩), c4, c5, c6, c7⟩
  · intro h j
    change Fin 8 at j
    fin_cases j
    · exact h.1 0
    · exact h.1 1
    · exact h.1 2
    · exact h.1 3
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2

end FLatticePaper.Tiles.BaseCorrectedThreeOneShortEvenSitesPolygons
