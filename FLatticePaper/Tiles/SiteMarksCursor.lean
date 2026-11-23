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

end FLatticePaper.Tiles.SiteMarksCursor
