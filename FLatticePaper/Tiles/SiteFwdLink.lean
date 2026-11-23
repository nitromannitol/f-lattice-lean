import FLatticePaper.Tiles.SiteMarksCursor

/-! Task 53, item 4 (the forward marks by index): membership in the forward horizontal string of a ceiling word is an explicit
cursor condition.

For a forward word `ℓ` of slope `2n / (d + n)` with `0 < n < d` (so `ℓ` starts with `q`), the sites of the forward string are exactly
`(2k + 1 − B, B − 1) + b` for an index `k < |ℓ|`, with `B = qPrefix ℓ (k+1)` and an offset `b` allowed for the letter `k`:
`{0,1} × {0,1,2}` for a `p`; `{0,1}²` for a `q` not preceded by `q`; and `{0,1}² ∪ {(−1,1),(1,−1)}` for a `q` preceded by `q`. -/

namespace FLatticePaper.Tiles.SiteFwdLink

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords
  FLatticePaper.Tiles.SiteMarksCursor

/-- The offsets of the forward letter `k` of a word `ℓ`. -/
def FwdOffset (ℓ : BinaryWord) (k : ℕ) (b : ℤ × ℤ) : Prop :=
  (ℓ.getD k Letter.p = Letter.p ∧ 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 2) ∨
  (ℓ.getD k Letter.p = Letter.q ∧ ¬ (k ≠ 0 ∧ ℓ.getD (k - 1) Letter.p = Letter.q) ∧
    0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∨
  (ℓ.getD k Letter.p = Letter.q ∧ k ≠ 0 ∧ ℓ.getD (k - 1) Letter.p = Letter.q ∧
    ((0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∨ b = (-1, 1) ∨ b = (1, -1)))

theorem first_letter_q (ℓ : BinaryWord) (n d : ℤ) (hC : CeilWord ℓ (2 * n) (d + n)) (hn : 0 < n) (hnd : n < d) :
    ∃ ℓ' : BinaryWord, ℓ = Letter.q :: ℓ' := by
  have hlen : (ℓ.length : ℤ) = d + n := hC.1
  cases ℓ with
  | nil => simp at hlen; omega
  | cons l ℓ' =>
    cases l with
    | q => exact ⟨ℓ', rfl⟩
    | p =>
      exfalso
      obtain ⟨-, h2⟩ := hC.2 1 (by omega)
      have hq : qPrefix (Letter.p :: ℓ') 1 = 0 := by
        simp [qPrefix, List.take_succ_cons]
      rw [hq] at h2
      push_cast at h2
      omega

/-- **Every index occurs.** The `k`-th tile of a forward string read after `pr` is an origin, with the cursor position, letter
and flag of `origins_fwd_spec`. -/
theorem origins_fwd_surj (ls : BinaryWord) : ∀ (pr : Letter) (pos : ℤ × ℤ) (k : ℕ), k < ls.length →
    ∃ o ∈ origins false false (some pr) pos ls,
      o.1 = (pos.1 + 2 * ((k : ℤ) + 1) - qPrefix ls (k + 1), pos.2 + qPrefix ls (k + 1)) ∧
      o.2.1 = ls.getD k pr ∧
      o.2.2 = (prevLetter pr ls k == Letter.q && ls.getD k pr == Letter.q) := by
  induction ls with
  | nil => intro pr pos k hk; simp at hk
  | cons l ls ih =>
    intro pr pos k hk
    have hstep : origins false false (some pr) pos (l :: ls) =
        ((pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)), l,
          (!false && pr == Letter.q && l == Letter.q)) ::
          origins false false (some l)
            (pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)) ls := by
      simp only [origins, dxdy_fwd]
    rw [hstep]
    cases k with
    | zero =>
      refine ⟨_, List.mem_cons_self, ?_, ?_, ?_⟩
      · cases l
        · simp [qPrefix, List.take_succ_cons]
        · simp [qPrefix, List.take_succ_cons]
          omega
      · simp
      · simp [prevLetter]
    | succ k' =>
      obtain ⟨o, ho, h1, h2, h3⟩ := ih l _ k' (by simp only [List.length_cons] at hk; omega)
      refine ⟨o, List.mem_cons_of_mem _ ho, ?_, ?_, ?_⟩
      · rw [h1, qPrefix_cons_succ]
        cases l <;> refine Prod.ext ?_ ?_ <;> simp <;> omega
      · rw [h2, List.getD_cons_succ, getD_irrel ls k' (by simp only [List.length_cons] at hk; omega) l pr]
      · rw [h3, prevLetter_cons pr l ls k' (by simp only [List.length_cons] at hk; omega), List.getD_cons_succ,
          getD_irrel ls k' (by simp only [List.length_cons] at hk; omega) l pr]

/-- The base sites of a letter, as a condition on the offset. -/
theorem mem_baseSites_iff (l : Letter) (f : Bool) (b : ℤ × ℤ) :
    b ∈ baseSites l f ↔
      (l = Letter.p ∧ 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 2) ∨
      (l = Letter.q ∧ f = false ∧ 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∨
      (l = Letter.q ∧ f = true ∧ ((0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∨ b = (-1, 1) ∨ b = (1, -1))) := by
  obtain ⟨b1, b2⟩ := b
  cases l <;> cases f <;> simp [baseSites, Prod.ext_iff] <;> omega

/-- The flatMap over the origins of a forward string, indexed by the tiles. -/
theorem flatMap_fwd_iff (ℓ' : BinaryWord) (pr : Letter) (pos : ℤ × ℤ) (z : ℤ × ℤ) :
    z ∈ (origins false false (some pr) pos ℓ').flatMap
        (fun o => (baseSites o.2.1 o.2.2).map fun b => (o.1.1 + b.1, o.1.2 + b.2)) ↔
      ∃ j : ℕ, j < ℓ'.length ∧ ∃ b : ℤ × ℤ,
        b ∈ baseSites (ℓ'.getD j pr) (prevLetter pr ℓ' j == Letter.q && ℓ'.getD j pr == Letter.q) ∧
        z = (pos.1 + (2 * ((j : ℤ) + 1) - qPrefix ℓ' (j + 1)) + b.1, pos.2 + qPrefix ℓ' (j + 1) + b.2) := by
  constructor
  · intro h
    obtain ⟨o, ho, hz⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, h1, h2, h3⟩ := origins_fwd_spec ℓ' pr pos o ho
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    refine ⟨j, hj, b, ?_, ?_⟩
    · rw [h2, h3] at hb
      exact hb
    · simp [h1, add_sub_assoc]
  · rintro ⟨j, hj, b, hb, rfl⟩
    obtain ⟨o, ho, h1, h2, h3⟩ := origins_fwd_surj ℓ' pr pos j hj
    refine List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨b, ?_, ?_⟩⟩
    · rw [h2, h3]
      exact hb
    · simp [h1, add_sub_assoc]

theorem fwdOffset_zero_iff (ℓ' : BinaryWord) (b : ℤ × ℤ) :
    FwdOffset (Letter.q :: ℓ') 0 b ↔ b ∈ baseSites Letter.q false := by
  rw [mem_baseSites_iff]
  unfold FwdOffset
  simp

theorem fwdOffset_succ_iff (ℓ' : BinaryWord) (j : ℕ) (hj : j < ℓ'.length) (b : ℤ × ℤ) :
    FwdOffset (Letter.q :: ℓ') (j + 1) b ↔
      b ∈ baseSites (ℓ'.getD j Letter.q) (prevLetter Letter.q ℓ' j == Letter.q && ℓ'.getD j Letter.q == Letter.q) := by
  rw [mem_baseSites_iff]
  have h1 : (Letter.q :: ℓ').getD (j + 1) Letter.p = ℓ'.getD j Letter.q := by
    rw [List.getD_cons_succ, getD_irrel ℓ' j hj Letter.p Letter.q]
  have h2 : (Letter.q :: ℓ').getD (j + 1 - 1) Letter.p = prevLetter Letter.q ℓ' j := by
    rw [Nat.add_sub_cancel]
    cases j with
    | zero => simp [prevLetter]
    | succ j' =>
      have hj' : j' < ℓ'.length := by omega
      rw [List.getD_cons_succ, prevLetter, if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel,
        getD_irrel ℓ' j' hj' Letter.p Letter.q]
  unfold FwdOffset
  rw [h1, h2]
  by_cases hq : ℓ'.getD j Letter.q = Letter.q <;> by_cases hp : prevLetter Letter.q ℓ' j = Letter.q <;>
    simp [hp] <;> tauto

/-- **The forward string by index.** The sites of the forward horizontal string of a ceiling word are exactly the cursor sites of
its indices, with the offsets of `FwdOffset`. -/
theorem stringSites_fwd_iff (n d : ℤ) (ℓ : BinaryWord) (hC : CeilWord ℓ (2 * n) (d + n)) (hn : 0 < n) (hnd : n < d)
    (z : ℤ × ℤ) :
    z ∈ stringSites false false ℓ ↔
      ∃ k : ℕ, k < ℓ.length ∧ ∃ b : ℤ × ℤ, FwdOffset ℓ k b ∧
        z = (2 * (k : ℤ) + 1 - qPrefix ℓ (k + 1) + b.1, qPrefix ℓ (k + 1) - 1 + b.2) := by
  obtain ⟨ℓ', rfl⟩ := first_letter_q ℓ n d hC hn hnd
  have hlen : ℓ'.length + 1 = (Letter.q :: ℓ').length := rfl
  have hs : stringSites false false (Letter.q :: ℓ') =
      ((baseSites Letter.q false).map fun b => ((0 : ℤ) + b.1, (0 : ℤ) + b.2)) ++
        (origins false false (some Letter.q) (0, 0) ℓ').flatMap
          (fun o => (baseSites o.2.1 o.2.2).map fun b => (o.1.1 + b.1, o.1.2 + b.2)) := by
    simp [stringSites, origins, startPos]
  rw [hs, List.mem_append, flatMap_fwd_iff, List.mem_map]
  constructor
  · rintro (⟨a, ha, hz⟩ | ⟨j, hj, b, hb, hzb⟩)
    · refine ⟨0, by simp only [List.length_cons]; omega, a, (fwdOffset_zero_iff ℓ' a).mpr ha, ?_⟩
      rw [← hz]
      simp [qPrefix]
    · refine ⟨j + 1, by simp only [List.length_cons]; omega, b, (fwdOffset_succ_iff ℓ' j hj b).mpr hb, ?_⟩
      rw [hzb, qPrefix_cons_succ]
      refine Prod.ext ?_ ?_ <;> simp
      all_goals omega
  · rintro ⟨k, hk, b, hb, hz⟩
    cases k with
    | zero =>
      left
      refine ⟨b, (fwdOffset_zero_iff ℓ' b).mp hb, ?_⟩
      rw [hz]
      simp [qPrefix]
    | succ j =>
      right
      have hj : j < ℓ'.length := by simp only [List.length_cons] at hk; omega
      refine ⟨j, hj, b, (fwdOffset_succ_iff ℓ' j hj b).mp hb, ?_⟩
      rw [hz, qPrefix_cons_succ]
      refine Prod.ext ?_ ?_ <;> simp
      all_goals omega

end FLatticePaper.Tiles.SiteFwdLink
