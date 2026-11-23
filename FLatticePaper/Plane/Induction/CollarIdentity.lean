import FLatticePaper.Plane.Induction.CollarBand

/-! Task 72 (hcollar, band (a), lemma 2): the parent identity for a free conjugate translate.

For the conjugate child `(n_c, d_c) = (D − N, D + N)` the translate `p = i U_c + j V_c` of the root `r = zTurn (c − l_v)` gives the
word-frame V point `v = zTurn (r + p) = (1, −1) − (c − l_v) + (−p.2, p.1)`, and `(−p.2, p.1) = i V_p − j U_p`. Hence, with
`s(x) = (d + n) x.1 + (d − n) x.2` and `ε = N d − D n`, `s(c) = 2n + s(l_v) + 2 i ε − j s(U_p) − s(v)`. -/

namespace FLatticePaper.CollarIdentity

open Farey FLatticePaper FLatticePaper.Induction

/-- The word `s`-grade of a site, for the word child `(n, d)`. -/
def sW (n d : ℤ) (x : ℤ × ℤ) : ℤ := (d + n) * x.1 + (d - n) * x.2

/-- The conjugate deck translate `i U_c + j V_c` for `U_c = (D + N, D − N)`, `V_c = (−2N, 2D)`, as a site. -/
def conjTranslate (N D i j : ℤ) : ℤ × ℤ :=
  (i * (D + N) + j * (-2 * N), i * (D - N) + j * (2 * D))

/-- The affine half-turn: `zTurn (zTurn x + p) = (1, −1) − x + (−p.2, p.1)`. -/
theorem zTurn_zTurn_add (x p : ℤ × ℤ) :
    zTurn (zTurn x + p) = ((1 : ℤ), (-1 : ℤ)) - x + (-p.2, p.1) := by
  unfold zTurn
  ext <;> simp <;> ring

/-- The parent identity for the `s`-grade of the centre. -/
theorem sW_centre_identity (n d N D i j : ℤ) (c lv : ℤ × ℤ) :
    sW n d c = 2 * n + sW n d lv + 2 * i * (N * d - D * n) - j * sW n d (2 * D, 2 * N)
      - sW n d (zTurn (zTurn (c - lv) + conjTranslate N D i j)) := by
  rw [zTurn_zTurn_add]
  unfold sW
  unfold conjTranslate
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  ring

end FLatticePaper.CollarIdentity
