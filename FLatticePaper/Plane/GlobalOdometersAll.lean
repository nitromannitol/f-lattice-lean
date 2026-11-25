import FLatticePaper.Plane.GlobalOdometers
import FLatticePaper.Plane.OddPhaseAlternate
import FLatticePaper.Tiles.StandardAll

/-! Task Q25, the odometer statements with the boundary-word inputs discharged. `global_odometers` and
`global_odometers_pair` take `bdOdd`, `bdEven` (and the simplicity fields of `global_odometers`), which are now
`StandardAll.standardBoundaryWord_all`, `StandardAll.simpleOdd_all` and `StandardAll.simpleEven_all`. Their other named inputs
remain as they are. -/

namespace FLatticePaper.GlobalOdometers

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.Tiles FLatticePaper.BaseAlternate
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.DeckCoverage FLatticePaper.Tiles.SeamSymm

theorem global_odometers_all {fraction : Fraction} (hint : fraction.Interior) {w : Word} {p : Parity}
    (hbirth : (parentsAt w).current p = fraction)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (planeTarget w p) gauge)
    (hsites : (p = .even ∧ tile.sites = evenTile w) ∨ (p = .odd ∧ tile.sites = oddTile w) ∨
      fraction.modifiedDeck.Covers tile.sites) :
    (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ tile.sites), planeTarget w p x = tile.height ⟨x, hx⟩ + c) ∧
    SatisfiesPeriodicity fraction (planeTarget w p) ∧
    HasQuadraticGrowth (planeTarget w p) fraction.matrix ∧
    (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((planeTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct b (siteVector x)) v) ∧
    (∀ x, laplacian (planeTarget w p) x = -1 ∨ laplacian (planeTarget w p) x = 0) ∧
    Superharmonic (planeTarget w p) ∧ Recurrent (planeTarget w p) ∧
    (∀ H : Field, SatisfiesPeriodicity fraction H →
      (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = planeTarget w p v - planeTarget w p 0) →
      ∀ gH : ℤ, tile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = planeTarget w p x + c)
  := global_odometers hint hbirth hstar hsheet harc hodd hbulk
    (fun v => (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all v).1)
    (fun v => (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all v).2)
    (fun v => FLatticePaper.Tiles.StandardAll.simpleOdd_all v)
    (fun v => FLatticePaper.Tiles.StandardAll.simpleEven_all v) tile htile hsites

end FLatticePaper.GlobalOdometers

namespace FLatticePaper.OddPhaseAlternate

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.DeckCoverage FLatticePaper.Tiles.StandardBoundary
open FLatticePaper.Tiles.StandardClause FLatticePaper.GlobalOdometers FLatticePaper.BaseAlternate

theorem global_odometers_pair_all {fraction : Fraction} (hint : fraction.Interior) {w : Word} {p : Parity}
    (hbirth : (parentsAt w).current p = fraction)
    (hstar : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → StarZoneInputs word)
    (hsheet : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word → SheetLocalInputs word)
    (harc : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      VArcInputs (frameAt word) (standardField word))
    (hodd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      S3NoFortInputs (frameAt word) (standardField word))
    (hbaseTwoId : ∀ k : ℕ, ∃ S : Field, (BaseMask.ladderOddAlt.raw (2 * (k : ℤ) + 4)).Agrees S 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S (-1) (ladderOddAltConstantV (2 * (k : ℤ) + 4)) ∧
      ∃ c : ℤ, ∀ x, (frameAt (List.replicate (k + 1) Digit.two)).alternate
        (standardField (List.replicate (k + 1) Digit.two)) x = rotateLadderAltField (2 * (k : ℤ) + 4) S x + c)
    (tile : HeightTile Site)
    (htile : ∃ gauge : ℤ, tile.Agrees (planeTarget w p) gauge)
    (hsites : (p = .even ∧ tile.sites = evenTile w) ∨ (p = .odd ∧ tile.sites = oddTile w) ∨
      fraction.modifiedDeck.Covers tile.sites)
    (hord : p = .odd → (w.getLast? = some Digit.one ∨ w.getLast? = some Digit.three))
    (altTile : HeightTile Site) (htileAlt : ∃ gauge : ℤ, altTile.Agrees (altTarget w p) gauge)
    (hcovAlt : fraction.modifiedDeck.Covers altTile.sites) :
    ((∃ c : ℤ, ∀ (x : Site) (hx : x ∈ tile.sites), planeTarget w p x = tile.height ⟨x, hx⟩ + c) ∧
      SatisfiesPeriodicity fraction (planeTarget w p) ∧
      HasQuadraticGrowth (planeTarget w p) fraction.matrix ∧
      (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
        Function.Periodic (fun x : Site => ((planeTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
          dotProduct b (siteVector x)) v) ∧
      (∀ x, laplacian (planeTarget w p) x = -1 ∨ laplacian (planeTarget w p) x = 0) ∧
      Superharmonic (planeTarget w p) ∧ Recurrent (planeTarget w p) ∧
      (∀ H : Field, SatisfiesPeriodicity fraction H →
        (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = planeTarget w p v - planeTarget w p 0) →
        ∀ gH : ℤ, tile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = planeTarget w p x + c)) ∧
    (∃ c : ℤ, ∀ (x : Site) (hx : x ∈ altTile.sites), altTarget w p x = altTile.height ⟨x, hx⟩ + c) ∧
    SatisfiesPeriodicity fraction (altTarget w p) ∧
    HasQuadraticGrowth (altTarget w p) fraction.matrix ∧
    (∃ b : Fin 2 → ℝ, ∀ v ∈ fraction.modifiedDeck.span,
      Function.Periodic (fun x : Site => ((altTarget w p x : ℤ) : ℝ) - matrixQuadratic fraction.matrix x -
        dotProduct b (siteVector x)) v) ∧
    (∀ x, laplacian (altTarget w p) x = -1 ∨ laplacian (altTarget w p) x = 0) ∧
    Superharmonic (altTarget w p) ∧ Recurrent (altTarget w p) ∧
    (∀ H : Field, SatisfiesPeriodicity fraction H →
      (∀ v ∈ fraction.modifiedDeck.span, H v - H 0 = altTarget w p v - altTarget w p 0) →
      ∀ gH : ℤ, altTile.Agrees H gH → ∃ c : ℤ, ∀ x, H x = altTarget w p x + c) ∧
    ¬ IntegerAffine (fun x => altTarget w p x - planeTarget w p x) ∧
    (∃ x, laplacian (altTarget w p) x ≠ laplacian (planeTarget w p) x) ∧
    ((p = .even →
        (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.transverse) -
          planeTarget w p (x + fraction.modifiedDeck.transverse) =
          altTarget w p x - planeTarget w p x - 1) ∧
        (∀ x : Site, altTarget w p (x + fraction.modifiedDeck.kernel) -
          planeTarget w p (x + fraction.modifiedDeck.kernel) = altTarget w p x - planeTarget w p x)) ∧
      (p = .odd → ∀ x : Site, (altTarget w p (x + fraction.modifiedDeck.kernel) -
          planeTarget w p (x + fraction.modifiedDeck.kernel)) - (altTarget w p x - planeTarget w p x) =
          -1 + ((alternateOddSlope w).1 * (fraction.modifiedDeck.kernel).1 +
            (alternateOddSlope w).2 * (fraction.modifiedDeck.kernel).2)))
  := global_odometers_pair hint hbirth hstar hsheet harc hodd hbulk hbaseTwoId
    (fun v => (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all v).1)
    (fun v => (FLatticePaper.Tiles.StandardAll.standardBoundaryWord_all v).2)
    tile htile hsites hord altTile htileAlt hcovAlt

end FLatticePaper.OddPhaseAlternate
