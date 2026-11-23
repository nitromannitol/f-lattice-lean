import FLatticePaper.Tiles.PairEvenW0Q
import FLatticePaper.Tiles.PairEvenW0P
import FLatticePaper.Tiles.PairEvenW1P
import FLatticePaper.Tiles.PairEvenW1Q
import FLatticePaper.Tiles.PairCoverW0
import FLatticePaper.Tiles.PairCoverW1

/-! Task 53, item 2 (covering reduction), section 13 (continued): the six reflected boxes of the even child `X = 2P + Q`.

The cell reflection `z ↦ R − z` with `R = (2n + r + 1, 2d + e + 4n + 2r − 1)` maps the cell of `X` to itself, `(u, v) ↦ (1 − u, 1 − v)`.
Each reflected box is the image of a base box, and each source is carried to its partner by `refl_Q` (centre `(r+1, e+2r−1)`) or
`refl_P` (centre `(d+n+1, d+3n−1)`):

* flag false: `Q@(2P+2V_P)` on `[α,1]²` from `Q@0`; `P@(V_Q+V_P)` on `[0,α]×[1−α/2,1]` from `P@Q`; `P@V_Q` on `[0,α]×[β,1−α/2]` from `P@(Q+V_P)`;
* flag true: `Q@2V_P` on `[0,β]×[α,1]` from `Q@2P`; `P@(Q+V_Q+V_P)` on `[β,1]×[1−α/2,1]` from `P@0`; `P@(Q+V_Q)` on `[β,1]×[β,1−α/2]` from `P@V_P`. -/

namespace FLatticePaper.Tiles.PairEvenRefl

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox FLatticePaper.Tiles.PairW0P FLatticePaper.Tiles.PairCoverW0
  FLatticePaper.Tiles.PairCoverW1 FLatticePaper.Tiles.PairEvenW0Q FLatticePaper.Tiles.PairEvenW0P
  FLatticePaper.Tiles.PairEvenW1P FLatticePaper.Tiles.PairEvenW1Q

/-- The cell reflection: `R − z` has cell coordinates `(1 − u, 1 − v)`, with `R = (2n+r+1, 2d+e+4n+2r−1)`. -/
theorem cellR0 (d n e r : ℤ) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r))) :
    (((2 * n + r + 1 - z.1 : ℤ) : ℚ) - 1 / 2 =
        (1 - u) * (2 * (d : ℚ) + e) + (1 - v) * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e))) ∧
    (((2 * d + e + 4 * n + 2 * r - 1 - z.2 : ℤ) : ℚ) + 1 / 2 =
        (1 - u) * (2 * (n : ℚ) + r) + (1 - v) * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r))) := by
  constructor
  · push_cast; linear_combination (-1 : ℚ) * hz1
  · push_cast; linear_combination (-1 : ℚ) * hz2

/-- `α + β = 1` from `α D = 2d` and `β D = e`. -/
theorem alpha_add_beta (d e : ℤ) (α β : ℚ) (hD : (0 : ℚ) < 2 * (d : ℚ) + e)
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ)) : α + β = 1 := by
  have h : (α + β - 1) * (2 * (d : ℚ) + e) = 0 := by linear_combination hα + hβ
  rcases mul_eq_zero.mp h with h' | h'
  · linarith
  · linarith

/-- **Flag false, `Q@(2P + 2V_P)` on `[α, 1]²`**, the reflection of `Q@0` on `[0, β]²`. -/
theorem RF2 (d n e r : ℤ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : α ≤ u) (hu1 : u ≤ 1) (hv0 : α ≤ v) (hv1 : v ≤ 1) :
    InH ⟨r, e⟩ (z.1 - 2 * n, z.2 - (4 * n + 2 * d)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := F1_box d n e r hd hn hnd hr hre hdet hodd heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) β h1 h2 hβ
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_Q r e heven _).mp key
  have hp : ((r + 1 - (2 * n + r + 1 - z.1), e + 2 * r - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2)) : ℤ × ℤ) =
      (z.1 - 2 * n, z.2 - (4 * n + 2 * d)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

/-- **Flag false, `P@(V_Q + V_P)` on `[0, α] × [1 − α/2, 1]`**, the reflection of `P@Q` on `[β, 1] × [0, α/2]`. -/
theorem RF4H (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : 2 - α ≤ 2 * v) (hv1 : v ≤ 1) :
    InH ⟨n, d⟩ (z.1 - (r - e + n - d), z.2 - (r + e + n + d)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := F3L_box d n e r hn hnd hr hre hdet hodd heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) α β h1 h2 hα hβ
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_P d n hodd _).mp key
  have hp : ((d + n + 1 - (2 * n + r + 1 - z.1 - e), d + 3 * n - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2 - r)) : ℤ × ℤ) =
      (z.1 - (r - e + n - d), z.2 - (r + e + n + d)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

/-- **Flag false, `P@V_Q` on `[0, α] × [β, 1 − α/2]`**, the reflection of `P@(Q + V_P)` on `[β, 1] × [α/2, α]`. -/
theorem RF4L (d n e r : ℤ) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : 2 * v ≤ 2 - α) :
    InH ⟨n, d⟩ (z.1 - (r - e), z.2 - (r + e)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := F3H_box d n e r hn hnd hdn hr hre hdet hodd heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) α β h1 h2 hα hβ
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_P d n hodd _).mp key
  have hp : ((d + n + 1 - (2 * n + r + 1 - z.1 - (e + (n - d))), d + 3 * n - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2 - (r + (n + d)))) : ℤ × ℤ) =
      (z.1 - (r - e), z.2 - (r + e)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

/-- **Flag true, `Q@2V_P` on `[0, β] × [α, 1]`**, the reflection of `Q@2P` on `[α, 1] × [0, β]`. -/
theorem RT2 (d n e r : ℤ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v ≤ 1) :
    InH ⟨r, e⟩ (z.1 - 2 * (n - d), z.2 - 2 * (n + d)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := T1_box d n e r hd hn hnd hr hre hdet heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) α β h1 h2 hα hβ
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_Q r e heven _).mp key
  have hp : ((r + 1 - (2 * n + r + 1 - z.1 - 2 * d), e + 2 * r - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2 - 2 * n)) : ℤ × ℤ) =
      (z.1 - 2 * (n - d), z.2 - 2 * (n + d)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

/-- **Flag true, `P@(Q + V_Q + V_P)` on `[β, 1] × [1 − α/2, 1]`**, the reflection of `P@0` on `[0, α] × [0, α/2]`. -/
theorem RT4H (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : β ≤ u) (hu1 : u ≤ 1) (hv0 : 2 - α ≤ 2 * v) (hv1 : v ≤ 1) :
    InH ⟨n, d⟩ (z.1 - (r + n - d), z.2 - (2 * r + e + n + d)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := T3L_box d n e r hn hnd hr hre hdet hodd heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) α h1 h2 hα
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_P d n hodd _).mp key
  have hp : ((d + n + 1 - (2 * n + r + 1 - z.1), d + 3 * n - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2)) : ℤ × ℤ) =
      (z.1 - (r + n - d), z.2 - (2 * r + e + n + d)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

/-- **Flag true, `P@(Q + V_Q)` on `[β, 1] × [β, 1 − α/2]`**, the reflection of `P@V_P` on `[0, α] × [α/2, α]`. -/
theorem RT4L (d n e r : ℤ) (hdn : d ≠ 2 * n ∨ 2 * d < e ∨ (d = 2 ∧ n = 1 ∧ e = 3 ∧ r = 1)) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ)) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : β ≤ u) (hu1 : u ≤ 1) (hv0 : β ≤ v) (hv1 : 2 * v ≤ 2 - α) :
    InH ⟨n, d⟩ (z.1 - r, z.2 - (2 * r + e)) := by
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by
    have : (0 : ℤ) < 2 * d + e := by omega
    exact_mod_cast this
  have hαβ := alpha_add_beta d e α β hD hα hβ
  obtain ⟨h1, h2⟩ := cellR0 d n e r z u v hz1 hz2
  have key := T3H_gen d n e r hn hnd hdn hr hre hdet hodd heven
    (2 * n + r + 1 - z.1, 2 * d + e + 4 * n + 2 * r - 1 - z.2) (1 - u) (1 - v) α h1 h2 hα
    (by linarith) (by linarith) (by linarith) (by linarith)
  have h := (refl_P d n hodd _).mp key
  have hp : ((d + n + 1 - (2 * n + r + 1 - z.1 - (n - d)), d + 3 * n - 1 - (2 * d + e + 4 * n + 2 * r - 1 - z.2 - (n + d))) : ℤ × ℤ) =
      (z.1 - r, z.2 - (2 * r + e)) := by
    ext <;> dsimp only <;> ring
  rw [hp] at h
  exact h

end FLatticePaper.Tiles.PairEvenRefl
