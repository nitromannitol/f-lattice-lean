import FLatticePaper.Tiles.SurgicalCornerThird

/-! The horizontal case of `α = γ` is pure corner algebra. With the corner tiles `(A, B, C, D)` of `cornerTiles`
(`A`, `B` the first and last of the forward horizontal string, `C`, `D` the last and first of the reversed one):
`B - A = 0` (`corner_fwd`), `C - D = (-1, 0)` (`corner_affine_12`), `C - B = a_{n/d,2} - a_{1/1,2}` (`corner_3_family`,
with `a_{n/d,2} = (n, -d)` and `a_{1/1,2} = (1, -1)`). Hence `D - A - a_{n/d,2} = (0, 1)`, which is the Moreover's
first-factor difference `(0, -1)` with the sign of the pairing (reversed family against the translated forward family). -/

namespace FLatticePaper.Tiles.CornerAlpha

theorem D_sub_A_sub_a2 (tA tB tC tD : ℚ × ℚ) (n d : ℚ)
    (hBA : tB - tA = 0) (hCD : tC - tD = ((-1 : ℚ), (0 : ℚ)))
    (hCB : tC - tB = ((n - 1 : ℚ), (1 - d : ℚ))) :
    tD - tA - ((n : ℚ), (-d : ℚ)) = ((0 : ℚ), (1 : ℚ)) := by
  have h1 := congrArg Prod.fst hBA
  have h2 := congrArg Prod.snd hBA
  have h3 := congrArg Prod.fst hCD
  have h4 := congrArg Prod.snd hCD
  have h5 := congrArg Prod.fst hCB
  have h6 := congrArg Prod.snd hCB
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at h1 h2 h3 h4 h5 h6
  apply Prod.ext
  · simp only [Prod.fst_sub]
    linarith
  · simp only [Prod.snd_sub]
    linarith

end FLatticePaper.Tiles.CornerAlpha
