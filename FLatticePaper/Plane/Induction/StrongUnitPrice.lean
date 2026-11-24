import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.StrongHSpan

/-! Task 67, STRONG_PRICE §§1–3 (the unit and no-saddle fields): `HasUnitPrice` and `NoPriceSaddle` of the primitive price.

Both fields follow from one statement about each star: the three sites of the star of `c` (`c`, `incomingNeg c`, `incomingPos c`), each
moved by one deck translate `deckVec i j` common to the star, have their primitive prices in one interval of length one. Under the
deck translate the price shifts by the constant `−i` (`price_deckVec`), so the window `[a, a+1]` holds at the star itself. Then every edge
increment lies in `[−1, 1]`, and a saddle (opposite unit increments at the centre) would force two star values at distance `2`.

Each translated site of a star is of one of three kinds, and each kind gives `P ∈ [c₀ − 1, c₀]`:
* an interior site of `E` (the closed polygon, `hPR`);
* an H-band site (`StrongHSpan.price_mem_of_sRange`, the single two-level span);
* a V site whose two sources are the harmonic grid (`StrongPriceValues.price_eq_cutPrice_of_harmonic`, the value `c₀`).
The classification `StarClassified` is the named input (STRONG_PRICE_AND_ALTERNATE_STEP §3, as stated there: full stars up to one deck
translate). It was checked numerically on the proper words of length at most four: for every centre in a window of radius 8, some
`(i, j)` with `|i|, |j| ≤ 3` classifies the star; the identity translate alone fails at most centres. -/

namespace FLatticePaper.StrongUnitPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.StrongHSpan FLatticePaper.StrongPriceValues

/-- The V source condition at a site: `F` equals the harmonic grid at the site and at its parent shift. -/
def VSource (frame : ChildFrame) (F : Field) (x : Site) : Prop :=
  F x = harmonicGrid x ∧ F (x - frame.parentShift) = harmonicGrid (x - frame.parentShift)

/-- The deck translate `i • kernel + j • transverse` of the modified deck, in coordinates. -/
def deckVec (frame : ChildFrame) (i j : ℤ) : Site :=
  (i * frame.child.modifiedDeck.kernel.1 + j * frame.child.modifiedDeck.transverse.1,
    i * frame.child.modifiedDeck.kernel.2 + j * frame.child.modifiedDeck.transverse.2)

/-- The full-star classification of STRONG_PRICE_AND_ALTERNATE_STEP §3: for every centre `c` there is one deck translate `deckVec i j`,
common to the star of `c`, such that each site `x` of that star, moved by the translate, lies in the closed polygon, in the H-star band,
or is a V source.

No restriction of the centres is needed. If `τ` classifies the star of `c`, then `τ − μ` classifies the star of `c + μ` (the translate
moves the two stars together), so the statement over all centres is the statement over a fundamental domain of the deck. Every star is
full: each of its centres has both incoming inputs. -/
def StarClassified (frame : ChildFrame) (F : Field) : Prop :=
  ∀ c : Site, ∃ i j : ℤ, ∀ x : Site,
    (x = c ∨ x = FLatticePaper.incomingNeg c ∨ x = FLatticePaper.incomingPos c) →
      x + deckVec frame i j ∈ frame.closedPolygon ∨ HStarBand frame (x + deckVec frame i j) ∨
        VSource frame F (x + deckVec frame i j)

/-- The price along integer multiples of the kernel: each unit of `n` lowers the price by one. -/
theorem price_mul_kernel (frame : ChildFrame) (F : Field)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1) (n : ℤ) (z : Site) :
    frame.price F (z + (n * frame.child.modifiedDeck.kernel.1, n * frame.child.modifiedDeck.kernel.2)) =
      frame.price F z - n := by
  induction n using Int.induction_on with
  | zero =>
    have e : z + ((0 : ℤ) * frame.child.modifiedDeck.kernel.1, (0 : ℤ) * frame.child.modifiedDeck.kernel.2) = z := by
      ext <;> simp
    rw [e]
    simp
  | succ i ih =>
    have h : z + (((i : ℤ) + 1) * frame.child.modifiedDeck.kernel.1, ((i : ℤ) + 1) * frame.child.modifiedDeck.kernel.2) =
        (z + ((i : ℤ) * frame.child.modifiedDeck.kernel.1, (i : ℤ) * frame.child.modifiedDeck.kernel.2)) +
          frame.child.modifiedDeck.kernel := by
      ext <;> simp <;> ring
    rw [h, hPU, ih]
    ring
  | pred i ih =>
    have h := hPU (z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.kernel.1,
      (-(i : ℤ) - 1) * frame.child.modifiedDeck.kernel.2))
    have e : z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.kernel.1, (-(i : ℤ) - 1) * frame.child.modifiedDeck.kernel.2) +
        frame.child.modifiedDeck.kernel =
        z + (-(i : ℤ) * frame.child.modifiedDeck.kernel.1, -(i : ℤ) * frame.child.modifiedDeck.kernel.2) := by
      ext <;> simp <;> ring
    rw [e] at h
    linarith

/-- The price along integer multiples of the transverse vector is constant. -/
theorem price_mul_transverse (frame : ChildFrame) (F : Field)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w) (m : ℤ) (z : Site) :
    frame.price F (z + (m * frame.child.modifiedDeck.transverse.1, m * frame.child.modifiedDeck.transverse.2)) =
      frame.price F z := by
  induction m using Int.induction_on with
  | zero =>
    have e : z + ((0 : ℤ) * frame.child.modifiedDeck.transverse.1, (0 : ℤ) * frame.child.modifiedDeck.transverse.2) = z := by
      ext <;> simp
    rw [e]
  | succ i ih =>
    have h : z + (((i : ℤ) + 1) * frame.child.modifiedDeck.transverse.1, ((i : ℤ) + 1) * frame.child.modifiedDeck.transverse.2) =
        (z + ((i : ℤ) * frame.child.modifiedDeck.transverse.1, (i : ℤ) * frame.child.modifiedDeck.transverse.2)) +
          frame.child.modifiedDeck.transverse := by
      ext <;> simp <;> ring
    rw [h, hPV, ih]
  | pred i ih =>
    have h := hPV (z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.1,
      (-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.2))
    have e : z + ((-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.1, (-(i : ℤ) - 1) * frame.child.modifiedDeck.transverse.2) +
        frame.child.modifiedDeck.transverse =
        z + (-(i : ℤ) * frame.child.modifiedDeck.transverse.1, -(i : ℤ) * frame.child.modifiedDeck.transverse.2) := by
      ext <;> simp <;> ring
    rw [e] at h
    linarith

/-- The deck translate lowers the price by `i`: the kernel contributes `−1` per unit and the transverse vector contributes `0`. -/
theorem price_deckVec (frame : ChildFrame) (F : Field)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w) (i j : ℤ) (z : Site) :
    frame.price F (z + deckVec frame i j) = frame.price F z - i := by
  have e : z + deckVec frame i j =
      (z + (j * frame.child.modifiedDeck.transverse.1, j * frame.child.modifiedDeck.transverse.2)) +
        (i * frame.child.modifiedDeck.kernel.1, i * frame.child.modifiedDeck.kernel.2) := by
    ext <;> simp [deckVec] <;> ring
  rw [e, price_mul_kernel frame F hPU i, price_mul_transverse frame F hPV j]

/-- **The price window of a star.** Under the classification, the three sites of the star of `c` have primitive prices in one interval
`[a, a + 1]` (the common deck translate shifts the window by a constant, and the translated window is `[c₀ − 1, c₀]`). -/
theorem star_window (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hcls : StarClassified frame F) (c : Site) :
    ∃ a : ℤ, ∀ x : Site, (x = c ∨ x = FLatticePaper.incomingNeg c ∨ x = FLatticePaper.incomingPos c) →
      a ≤ frame.price F x ∧ frame.price F x ≤ a + 1 := by
  obtain ⟨i, j, hij⟩ := hcls c
  refine ⟨frame.cutPrice - 1 + i, fun x hx => ?_⟩
  have hy : frame.cutPrice - 1 ≤ frame.price F (x + deckVec frame i j) ∧
      frame.price F (x + deckVec frame i j) ≤ frame.cutPrice := by
    rcases hij x hx with hE | hH | ⟨h1, h2⟩
    · exact hPR _ hE
    · exact StrongHSpan.price_mem_of_sRange frame F hPR hPV _ (StrongHSpan.sRange_of_HStarBand frame _ hH)
    · have hc := StrongPriceValues.price_eq_cutPrice_of_harmonic frame F _ h1 h2
      constructor <;> linarith
  have hd := price_deckVec frame F hPU hPV i j x
  constructor <;> linarith [hy.1, hy.2, hd]

/-- **`HasUnitPrice` and `NoPriceSaddle`.** Under the star classification, the primitive price has unit increments on every edge and no
saddle at any star. -/
theorem unitPrice_and_noSaddle (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPU : ∀ w, frame.price F (w + frame.child.modifiedDeck.kernel) = frame.price F w - 1)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hcls : StarClassified frame F) :
    HasUnitPrice frame F ∧ NoPriceSaddle frame F := by
  constructor
  · intro center input hE
    have hin : input = FLatticePaper.incomingNeg center ∨ input = FLatticePaper.incomingPos center := hE
    obtain ⟨a, ha⟩ := star_window frame F hPR hPU hPV hcls center
    have hi := ha input (Or.inr hin)
    have hc := ha center (Or.inl rfl)
    unfold priceIncrement
    constructor <;> linarith [hi.1, hi.2, hc.1, hc.2]
  · intro site
    obtain ⟨a, ha⟩ := star_window frame F hPR hPU hPV hcls site
    have hn := ha (FLatticePaper.incomingNeg site) (Or.inr (Or.inl rfl))
    have hp := ha (FLatticePaper.incomingPos site) (Or.inr (Or.inr rfl))
    have hs := ha site (Or.inl rfl)
    unfold priceIncrement
    simp only
    omega

end FLatticePaper.StrongUnitPrice
