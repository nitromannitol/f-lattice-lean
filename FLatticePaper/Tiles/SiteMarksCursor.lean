import FLatticePaper.Tiles.SiteStrings
import FLatticePaper.Tiles.CeilWords

/-! Task 53, item 4 (the explicit marks): the origins of a forward horizontal string are the ceiling cursor.

For a horizontal word `ℓ = ℓ₀ :: ℓ'` (forward, `rev = false`, `vert = false`), the origin of the tile of the letter `ℓ_{k+1}` is
`(2(k+1) − #q(ℓ'.take(k+1)), #q(ℓ'.take(k+1)))`: each letter contributes the step `(2 − [q], [q])`, and the first letter of the
string sits at the origin `(0,0)`. With `ℓ₀ = q` and the ceiling cursor `b_j = #q(ℓ.take j)`, this is `(2j + 1 − b_{j+1}, b_{j+1} − 1)`. -/

namespace FLatticePaper.Tiles.SiteMarksCursor

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CeilWords

theorem dxdy_fwd (pr l : Letter) :
    dxdy false false pr l = ((if l = Letter.p then 2 else 1), (if l = Letter.q then 1 else 0)) := by
  cases l <;> simp [dxdy]

theorem qPrefix_cons_succ (l : Letter) (ls : BinaryWord) (j : ℕ) :
    qPrefix (l :: ls) (j + 1) = (if l = Letter.q then 1 else 0) + qPrefix ls j := by
  cases l
  · simp [qPrefix, List.take_succ_cons]
  · simp [qPrefix, List.take_succ_cons]
    ring

theorem qPrefix_nil_zero (j : ℕ) : qPrefix [] j = 0 := by
  simp [qPrefix]

/-- The origins of a forward string, read after a first letter `pr`: the positions of the tiles of the letters after it. -/
theorem origins_fwd_fst (ls : BinaryWord) : ∀ (pr : Letter) (pos : ℤ × ℤ),
    (origins false false (some pr) pos ls).map (fun o => o.1) =
      (List.range ls.length).map fun (k : ℕ) =>
        (pos.1 + 2 * ((k : ℤ) + 1) - qPrefix ls (k + 1), pos.2 + qPrefix ls (k + 1)) := by
  induction ls with
  | nil => intro pr pos; rfl
  | cons l ls ih =>
    intro pr pos
    have hstep : origins false false (some pr) pos (l :: ls) =
        ((pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)), l,
          (!false && pr == Letter.q && l == Letter.q)) ::
          origins false false (some l)
            (pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)) ls := by
      simp only [origins, dxdy_fwd]
    rw [hstep, List.map_cons, ih l _, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · cases l
      · simp [qPrefix, List.take_succ_cons]
      · simp [qPrefix, List.take_succ_cons]
        omega
    · refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_def, qPrefix_cons_succ]
      cases l <;> refine Prod.ext ?_ ?_ <;> simp <;> omega

/-- Appending the letter `ℓ[k]` raises the `q`-prefix count by one exactly when that letter is `q`. -/
theorem qPrefix_succ (ℓ : BinaryWord) (k : ℕ) (hk : k < ℓ.length) :
    qPrefix ℓ (k + 1) = qPrefix ℓ k + (if ℓ[k] = Letter.q then 1 else 0) := by
  unfold qPrefix
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  cases hℓ : ℓ[k] <;> simp [List.count_append]

/-- **The letter rule of the cursor.** For a forward word of slope `2n / (d + n)` with `0 < n < d`, the letter at index `k` is `q`
exactly when its cursor error `(d + n) · qPrefix ℓ k − 2n · k` is below `2n`. -/
theorem letter_rule (ℓ : BinaryWord) (n d : ℤ) (hC : CeilWord ℓ (2 * n) (d + n)) (k : ℕ) (hk : k < ℓ.length) :
    ℓ[k] = Letter.q ↔ (d + n) * qPrefix ℓ k - 2 * n * (k : ℤ) < 2 * n := by
  have hlen : (ℓ.length : ℤ) = d + n := hC.1
  have hk' : (k : ℤ) + 1 ≤ d + n := by omega
  have hkk : (k : ℤ) ≤ d + n := by omega
  obtain ⟨a1, a2⟩ := hC.2 k hkk
  obtain ⟨b1, b2⟩ := hC.2 (k + 1) (by push_cast; omega)
  have hsucc := qPrefix_succ ℓ k hk
  push_cast at b1 b2
  constructor
  · intro hq
    rw [hq] at hsucc
    simp only [if_true] at hsucc
    nlinarith
  · intro h
    by_contra hne
    have hp : ℓ[k] ≠ Letter.q := hne
    rw [if_neg hp] at hsucc
    nlinarith

/-- The `t`-coordinate of a site of the forward string, written in the cursor error: with `B = qPrefix ℓ (k + 1)` and the
origin `(2k + 1 − B, B − 1)` of the tile of index `k`, the site `(2k + 1 − B + bx, B − 1 + by)` has
`t = (d + n) − 2n − ((d + n) B − 2n (k + 1)) + n bx − d by`. -/
theorem t_identity_fwd (n d k B bx by' : ℤ) :
    n * (2 * k + 1 - B + bx) - d * (B - 1 + by') =
      (d + n) - 2 * n - ((d + n) * B - 2 * n * (k + 1)) + n * bx - d * by' := by ring

/-- The identity `L s = T (x + y) + N t` of the coordinates: `L = d + n`, `s = L x + C y`, `T = d² + 2dn − n²`, `N = 2n`, `t = n x − d y`. -/
theorem s_identity (n d x y : ℤ) :
    (d + n) * ((d + n) * x + (d - n) * y) =
      (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + (2 * n) * (n * x - d * y) := by ring

/-- The default of `getD` is irrelevant inside the range. -/
theorem getD_irrel (xs : BinaryWord) (k : ℕ) (hk : k < xs.length) (d d' : Letter) : xs.getD k d = xs.getD k d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- The letter before the `k`-th letter of a forward string read after `pr`. -/
def prevLetter (pr : Letter) (ls : BinaryWord) (k : ℕ) : Letter := if k = 0 then pr else ls.getD (k - 1) pr

theorem prevLetter_cons (pr l : Letter) (ls : BinaryWord) (k : ℕ) (hk : k < ls.length) :
    prevLetter pr (l :: ls) (k + 1) = prevLetter l ls k := by
  cases k with
  | zero => simp [prevLetter]
  | succ j =>
    have hj : j < ls.length := by omega
    simpa [prevLetter, List.getD_cons_succ] using getD_irrel ls j hj pr l

/-- **The origins by index.** Every origin of a forward string read after `pr` is the `k`-th tile: its position is the cursor
`(2(k+1) − #q(ls.take(k+1)), #q(ls.take(k+1)))` from the start, its letter is `ls[k]`, and its enlargement flag is the pair
`prev = q, ls[k] = q`. -/
theorem origins_fwd_spec (ls : BinaryWord) : ∀ (pr : Letter) (pos : ℤ × ℤ) (o : (ℤ × ℤ) × Letter × Bool),
    o ∈ origins false false (some pr) pos ls →
    ∃ k : ℕ, k < ls.length ∧
      o.1 = (pos.1 + 2 * ((k : ℤ) + 1) - qPrefix ls (k + 1), pos.2 + qPrefix ls (k + 1)) ∧
      o.2.1 = ls.getD k pr ∧
      o.2.2 = (prevLetter pr ls k == Letter.q && ls.getD k pr == Letter.q) := by
  induction ls with
  | nil => intro pr pos o ho; simp [origins] at ho
  | cons l ls ih =>
    intro pr pos o ho
    have hstep : origins false false (some pr) pos (l :: ls) =
        ((pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)), l,
          (!false && pr == Letter.q && l == Letter.q)) ::
          origins false false (some l)
            (pos.1 + (if l = Letter.p then 2 else 1), pos.2 + (if l = Letter.q then 1 else 0)) ls := by
      simp only [origins, dxdy_fwd]
    rw [hstep, List.mem_cons] at ho
    rcases ho with rfl | ho
    · refine ⟨0, by simp, ?_, ?_, ?_⟩
      · cases l
        · simp [qPrefix, List.take_succ_cons]
        · simp [qPrefix, List.take_succ_cons]
          omega
      · simp
      · simp [prevLetter]
    · obtain ⟨k, hk, h1, h2, h3⟩ := ih l _ o ho
      refine ⟨k + 1, by simp; omega, ?_, ?_, ?_⟩
      · rw [h1, qPrefix_cons_succ]
        cases l <;> refine Prod.ext ?_ ?_ <;> simp <;> omega
      · rw [h2, List.getD_cons_succ, getD_irrel ls k hk l pr]
      · rw [h3, prevLetter_cons pr l ls k hk, List.getD_cons_succ, getD_irrel ls k hk l pr]

end FLatticePaper.Tiles.SiteMarksCursor
