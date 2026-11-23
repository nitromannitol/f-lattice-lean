import FLatticePaper.Tiles.SiteFwdLink

/-! Task 53, item 4 (the vertical marks by index): membership in the vertical string of a word read after a `q`.

The vertical string `stringSites true true ℓ` (reversed vertical reading) has, for the tile `k` (full index), origin
`(1 − k + B_k, k + B_{k+1})`, where `B_j = qPrefix ℓ j` and `ℓ` starts with `q`; the step of a letter is `(−[prev = p], 1 or 2)`
and there is no enlargement. Shifted by `(−1, −1)`, as in `markedSites`, the sites are `(−k + B_k + b₁, k + B_{k+1} − 1 + b₂)` with
`b` in `{0,1}²` for a `q` and in `{0,1} × {0,1,2}` for a `p`. -/

namespace FLatticePaper.Tiles.SiteVertLink

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteMarksCursor FLatticePaper.Tiles.SiteFwdLink

theorem dxdy_vert (pr l : Letter) :
    dxdy true true pr l = ((if pr = Letter.p then -1 else 0), (if l = Letter.p then 1 else 2)) := by
  cases pr <;> cases l <;> simp [dxdy]

theorem origins_vert_spec (ls : BinaryWord) : ∀ (pr : Letter) (pos : ℤ × ℤ) (o : (ℤ × ℤ) × Letter × Bool),
    o ∈ origins true true (some pr) pos ls →
    ∃ k : ℕ, k < ls.length ∧
      o.1 = (pos.1 - (if pr = Letter.p then 1 else 0) - (k : ℤ) + qPrefix ls k,
        pos.2 + (k : ℤ) + 1 + qPrefix ls (k + 1)) ∧
      o.2.1 = ls.getD k pr ∧
      o.2.2 = false := by
  induction ls with
  | nil => intro pr pos o ho; simp [origins] at ho
  | cons l ls ih =>
    intro pr pos o ho
    have hstep : origins true true (some pr) pos (l :: ls) =
        ((pos.1 + (if pr = Letter.p then -1 else 0), pos.2 + (if l = Letter.p then 1 else 2)), l, false) ::
          origins true true (some l)
            (pos.1 + (if pr = Letter.p then -1 else 0), pos.2 + (if l = Letter.p then 1 else 2)) ls := by
      simp only [origins, dxdy_vert]
      simp
    rw [hstep, List.mem_cons] at ho
    rcases ho with rfl | ho
    · refine ⟨0, by simp, ?_, ?_, rfl⟩
      · cases pr <;> cases l <;> simp [qPrefix, List.take_succ_cons]
        all_goals omega
      · simp
    · obtain ⟨k, hk, h1, h2, h3⟩ := ih l _ o ho
      refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, ?_, h3⟩
      · rw [h1]
        simp only [qPrefix_cons_succ]
        cases pr <;> cases l <;> simp <;> omega
      · rw [h2, List.getD_cons_succ, getD_irrel ls k hk l pr]

theorem origins_vert_surj (ls : BinaryWord) : ∀ (pr : Letter) (pos : ℤ × ℤ) (k : ℕ), k < ls.length →
    ∃ o ∈ origins true true (some pr) pos ls,
      o.1 = (pos.1 - (if pr = Letter.p then 1 else 0) - (k : ℤ) + qPrefix ls k,
        pos.2 + (k : ℤ) + 1 + qPrefix ls (k + 1)) ∧
      o.2.1 = ls.getD k pr ∧
      o.2.2 = false := by
  induction ls with
  | nil => intro pr pos k hk; simp at hk
  | cons l ls ih =>
    intro pr pos k hk
    have hstep : origins true true (some pr) pos (l :: ls) =
        ((pos.1 + (if pr = Letter.p then -1 else 0), pos.2 + (if l = Letter.p then 1 else 2)), l, false) ::
          origins true true (some l)
            (pos.1 + (if pr = Letter.p then -1 else 0), pos.2 + (if l = Letter.p then 1 else 2)) ls := by
      simp only [origins, dxdy_vert]
      simp
    rw [hstep]
    cases k with
    | zero =>
      refine ⟨_, List.mem_cons_self, ?_, ?_, rfl⟩
      · cases pr <;> cases l <;> simp [qPrefix, List.take_succ_cons]
        all_goals omega
      · simp
    | succ k' =>
      obtain ⟨o, ho, h1, h2, h3⟩ := ih l _ k' (by simp only [List.length_cons] at hk; omega)
      refine ⟨o, List.mem_cons_of_mem _ ho, ?_, ?_, h3⟩
      · rw [h1]
        simp only [qPrefix_cons_succ]
        cases pr <;> cases l <;> simp <;> omega
      · rw [h2, List.getD_cons_succ, getD_irrel ls k' (by simp only [List.length_cons] at hk; omega) l pr]

/-- The vertical flatMap over the origins, indexed by the tiles. -/
theorem flatMap_vert_iff (ℓ' : BinaryWord) (pr : Letter) (pos : ℤ × ℤ) (z : ℤ × ℤ) :
    z ∈ (origins true true (some pr) pos ℓ').flatMap
        (fun o => (baseSites o.2.1 o.2.2).map fun b => (o.1.1 + b.1, o.1.2 + b.2)) ↔
      ∃ j : ℕ, j < ℓ'.length ∧ ∃ b : ℤ × ℤ, b ∈ baseSites (ℓ'.getD j pr) false ∧
        z = (pos.1 - (if pr = Letter.p then 1 else 0) - (j : ℤ) + qPrefix ℓ' j + b.1,
          pos.2 + (j : ℤ) + 1 + qPrefix ℓ' (j + 1) + b.2) := by
  constructor
  · intro h
    obtain ⟨o, ho, hz⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, h1, h2, h3⟩ := origins_vert_spec ℓ' pr pos o ho
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    refine ⟨j, hj, b, ?_, ?_⟩
    · rw [h2, h3] at hb
      exact hb
    · simp [h1]
  · rintro ⟨j, hj, b, hb, rfl⟩
    obtain ⟨o, ho, h1, h2, h3⟩ := origins_vert_surj ℓ' pr pos j hj
    refine List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨b, ?_, ?_⟩⟩
    · rw [h2, h3]
      exact hb
    · simp [h1]

/-- The offsets of a vertical index: a `p` has `{0,1} × {0,1,2}`, a `q` has `{0,1}²` (no enlargement in the vertical word). -/
def VertOffset (ℓ : BinaryWord) (k : ℕ) (b : ℤ × ℤ) : Prop :=
  (ℓ.getD k Letter.p = Letter.p ∧ 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 2) ∨
  (ℓ.getD k Letter.p = Letter.q ∧ 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1)

theorem vertOffset_zero_iff (ℓ'' : BinaryWord) (b : ℤ × ℤ) :
    VertOffset (Letter.q :: ℓ'') 0 b ↔ b ∈ baseSites Letter.q false := by
  rw [mem_baseSites_iff]
  unfold VertOffset
  simp

theorem vertOffset_succ_iff (ℓ'' : BinaryWord) (j : ℕ) (hj : j < ℓ''.length) (b : ℤ × ℤ) :
    VertOffset (Letter.q :: ℓ'') (j + 1) b ↔ b ∈ baseSites (ℓ''.getD j Letter.q) false := by
  rw [mem_baseSites_iff]
  have h1 : (Letter.q :: ℓ'').getD (j + 1) Letter.p = ℓ''.getD j Letter.q := by
    rw [List.getD_cons_succ, getD_irrel ℓ'' j hj Letter.p Letter.q]
  unfold VertOffset
  rw [h1]
  simp

/-- **The vertical string by index.** For a word `q :: ℓ''` (the reversed vertical reading), the sites are the cursor sites
`(1 − k + B_k + b₁, k + B_{k+1} + b₂)` (before the shift by `(−1,−1)` of the marks), `B_j = qPrefix`. -/
theorem stringSites_vert_iff_cons (ℓ'' : BinaryWord) (z : ℤ × ℤ) :
    z ∈ stringSites true true (Letter.q :: ℓ'') ↔
      ∃ k : ℕ, k < (Letter.q :: ℓ'').length ∧ ∃ b : ℤ × ℤ, VertOffset (Letter.q :: ℓ'') k b ∧
        z = (1 - (k : ℤ) + qPrefix (Letter.q :: ℓ'') k + b.1,
          (k : ℤ) + qPrefix (Letter.q :: ℓ'') (k + 1) + b.2) := by
  have hs : stringSites true true (Letter.q :: ℓ'') =
      ((baseSites Letter.q false).map fun b => ((1 : ℤ) + b.1, (1 : ℤ) + b.2)) ++
        (origins true true (some Letter.q) (1, 1) ℓ'').flatMap
          (fun o => (baseSites o.2.1 o.2.2).map fun b => (o.1.1 + b.1, o.1.2 + b.2)) := by
    simp [stringSites, origins, startPos]
  have e1 : ∀ j : ℕ, qPrefix (Letter.q :: ℓ'') (j + 1) = 1 + qPrefix ℓ'' j := fun j => by
    rw [qPrefix_cons_succ]
    simp
  have e2 : ∀ j : ℕ, qPrefix (Letter.q :: ℓ'') (j + 1 + 1) = 1 + qPrefix ℓ'' (j + 1) := fun j => by
    rw [qPrefix_cons_succ]
    simp
  rw [hs, List.mem_append, flatMap_vert_iff, List.mem_map]
  constructor
  · rintro (⟨a, ha, hz⟩ | ⟨j, hj, b, hb, hzb⟩)
    · refine ⟨0, by simp only [List.length_cons]; omega, a, (vertOffset_zero_iff ℓ'' a).mpr ha, ?_⟩
      rw [← hz]
      simp [qPrefix]
    · refine ⟨j + 1, by simp only [List.length_cons]; omega, b, (vertOffset_succ_iff ℓ'' j hj b).mpr hb, ?_⟩
      rw [hzb, e1 j, e2 j]
      refine Prod.ext ?_ ?_
      · simp
        try ring
      · simp
        try ring
  · rintro ⟨k, hk, b, hb, hz⟩
    cases k with
    | zero =>
      left
      refine ⟨b, (vertOffset_zero_iff ℓ'' b).mp hb, ?_⟩
      rw [hz]
      simp [qPrefix]
    | succ j =>
      right
      have hj : j < ℓ''.length := by simp only [List.length_cons] at hk; omega
      refine ⟨j, hj, b, (vertOffset_succ_iff ℓ'' j hj b).mp hb, ?_⟩
      rw [hz, e1 j, e2 j]
      refine Prod.ext ?_ ?_
      · simp
        try ring
      · simp
        try ring

end FLatticePaper.Tiles.SiteVertLink
