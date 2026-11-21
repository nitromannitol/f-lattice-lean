import FLatticePaper.Tiles.PseudoSquare

open FLatticePaper.Tiles

#print axioms FLatticePaper.Tiles.pseudoBoundaryWord_halfTurn
#print axioms FLatticePaper.Tiles.pseudoBoundaryWord_rotation
#print axioms FLatticePaper.Tiles.gPseudo_rotPseudo
#print axioms FLatticePaper.Tiles.pseudoSquare_boundaryWord
#print axioms FLatticePaper.Tiles.pseudoSquare_halfTurn
#print axioms FLatticePaper.Tiles.pseudoSquare_quarterTurn

/-! The base tiles of Section 6 (line 1912-1920 of the paper): the words (w_h, w_v) for d = 3 (w_h = q p, w_v = p p q,
the family 3^k even with k = 0), d = 5 (w_h = q p p, w_v = p p p p q, k = 1), and d = 4 (w_h = q p q p p,
w_v = p p p q, the family 3^k odd with k = 1). The Lemma 4.2 sums (line 779): Σw_1 + i = v_{n/d,1} and Σw_2 - 1 =
v_{n/d,2}, with v_{n/d,1} = (d, n) for even n/d and 2(d, n) for odd n/d, and v_{n/d,2} = (n - d, n + d). -/

-- d = 3: 1/3 is even, v_1 = (3, 1), v_2 = (-2, 4).
example : F2Word.sum (gPseudo [Letter.q, Letter.p] [Letter.p, Letter.p, Letter.q]).1 + gI = (3, 1) := by decide
example : F2Word.sum (gPseudo [Letter.q, Letter.p] [Letter.p, Letter.p, Letter.q]).2 - gOne = (-2, 4) := by decide

-- d = 5: 1/5 is even, v_1 = (5, 1), v_2 = (-4, 6).
example : F2Word.sum (gPseudo [Letter.q, Letter.p, Letter.p] [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]).1 + gI =
    (5, 1) := by decide
example : F2Word.sum (gPseudo [Letter.q, Letter.p, Letter.p] [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]).2 - gOne =
    (-4, 6) := by decide

-- d = 4: 1/4 is odd, v_1 = (8, 2), v_2 = (-3, 5).
example : F2Word.sum (gPseudo [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.q]).1 + gI = (8, 2) := by decide
example : F2Word.sum (gPseudo [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.q]).2 - gOne = (-3, 5) := by decide

-- The boundary words of the three base tiles close up, and the half-turn holds on them.
example : F2Word.sum (pseudoBoundaryWord (gPseudo [Letter.q, Letter.p] [Letter.p, Letter.p, Letter.q]).1
    (gPseudo [Letter.q, Letter.p] [Letter.p, Letter.p, Letter.q]).2) = 0 := by decide
example : F2Word.sum (pseudoBoundaryWord (gPseudo [Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]).1 (gPseudo [Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]).2) = 0 := by decide
example : F2Word.sum (pseudoBoundaryWord (gPseudo [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.q]).1 (gPseudo [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]
    [Letter.p, Letter.p, Letter.p, Letter.q]).2) = 0 := by decide
