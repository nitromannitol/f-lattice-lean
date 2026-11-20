import FLatticePaper.Plane.AlternateMidpoint
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Prod

namespace FLatticePaper

inductive QuarterTurn
  | clockwise | counterclockwise

def QuarterTurn.turn : QuarterTurn → Site → Site
  | .clockwise, site => (site.2, -site.1)
  | .counterclockwise, site => (-site.2, site.1)

def QuarterTurn.inverse : QuarterTurn → QuarterTurn
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

def QuarterTurn.mapSite (direction : QuarterTurn) (offset site : Site) : Site :=
  direction.turn site + offset

def QuarterTurn.siteEquiv (direction : QuarterTurn) (offset : Site) : Site ≃ Site where
  toFun := direction.mapSite offset
  invFun site := direction.inverse.turn (site - offset)
  left_inv site := by
    change direction.inverse.turn (direction.turn site + offset - offset) = site
    rw [add_sub_cancel_right]
    cases direction <;> apply Prod.ext <;> dsimp [QuarterTurn.inverse, QuarterTurn.turn] <;> omega
  right_inv site := by
    change direction.turn (direction.inverse.turn (site - offset)) + offset = site
    have h (point : Site) : direction.turn (direction.inverse.turn point) = point := by
      cases direction <;> apply Prod.ext <;> dsimp [QuarterTurn.inverse, QuarterTurn.turn] <;> omega
    rw [h, sub_add_cancel]

/-- The required checkerboard shift for a quarter-turn is an odd translation. -/
theorem QuarterTurn.evenSite_mapSite_iff (direction : QuarterTurn) (offset site : Site)
    (hoffset : ¬ EvenSite offset) : EvenSite (direction.mapSite offset site) ↔ ¬ EvenSite site := by
  cases direction <;> dsimp [EvenSite, QuarterTurn.mapSite, QuarterTurn.turn] at hoffset ⊢ <;> omega

/-- The two incoming slots are preserved as an unordered physical star. -/
theorem QuarterTurn.incoming_star (direction : QuarterTurn) (offset site : Site)
    (hoffset : ¬ EvenSite offset) :
    let rot := direction.mapSite offset
    (incomingNeg (rot site) = rot (incomingNeg site) ∧
      incomingPos (rot site) = rot (incomingPos site)) ∨
    (incomingNeg (rot site) = rot (incomingPos site) ∧
      incomingPos (rot site) = rot (incomingNeg site)) := by
  have hp := direction.evenSite_mapSite_iff offset site hoffset
  by_cases heven : EvenSite site
  · have hrot : ¬ EvenSite (direction.mapSite offset site) := fun h => (hp.mp h) heven
    cases direction
    · right
      constructor <;> simp only [incomingNeg, incomingPos, if_pos heven, if_neg hrot] <;>
        apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
    · left
      constructor <;> simp only [incomingNeg, incomingPos, if_pos heven, if_neg hrot] <;>
        apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
  · have hrot : EvenSite (direction.mapSite offset site) := hp.mpr heven
    cases direction
    · left
      constructor <;> simp only [incomingNeg, incomingPos, if_neg heven, if_pos hrot] <;>
        apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
    · right
      constructor <;> simp only [incomingNeg, incomingPos, if_neg heven, if_pos hrot] <;>
        apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega

theorem QuarterTurn.edge_mapSite_iff (direction : QuarterTurn) (offset center input : Site)
    (hoffset : ¬ EvenSite offset) :
    Edge (direction.mapSite offset input) (direction.mapSite offset center) ↔ Edge input center := by
  have hinj : Function.Injective (direction.mapSite offset) := (direction.siteEquiv offset).injective
  unfold Edge
  rcases direction.incoming_star offset center hoffset with ⟨hn, hp⟩ | ⟨hn, hp⟩ <;>
    rw [hn, hp, hinj.eq_iff, hinj.eq_iff]
  exact or_comm

def Harmonic (field : Field) : Prop := ∀ site, laplacian field site = 0

theorem laplacian_quarterTurn_add_harmonic (direction : QuarterTurn) (offset : Site)
    (hoffset : ¬ EvenSite offset) (field correction : Field) (hcorrection : Harmonic correction)
    (site : Site) :
    laplacian (fun input => field (direction.mapSite offset input) + correction input) site =
      laplacian field (direction.mapSite offset site) := by
  have hsum := hcorrection site
  unfold laplacian at hsum ⊢
  dsimp only
  rcases direction.incoming_star offset site hoffset with ⟨hn, hp⟩ | ⟨hn, hp⟩ <;>
    rw [hn, hp] <;> omega

/-- Transport both the physical rank and the admissible-input constraint
by a parity-correct quarter-turn and arbitrary harmonic height correction. -/
theorem IsConstrainedBurningRank.quarterTurn {α : Type*} [LT α] {field : Field} {rank : Site → α}
    {permits : Site → Site → Prop} (h : IsConstrainedBurningRank field rank permits)
    (direction : QuarterTurn) (offset : Site) (hoffset : ¬ EvenSite offset)
    {correction : Field} (hcorrection : Harmonic correction) :
    IsConstrainedBurningRank (fun site => field (direction.mapSite offset site) + correction site)
      (fun site => rank (direction.mapSite offset site))
      (fun center input => permits (direction.mapSite offset center) (direction.mapSite offset input)) := by
  intro site
  dsimp only
  rw [laplacian_quarterTurn_add_harmonic direction offset hoffset field correction hcorrection site]
  have hstar := h (direction.mapSite offset site)
  dsimp only at hstar
  rcases direction.incoming_star offset site hoffset with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · rwa [hn, hp] at hstar
  · rw [hn, hp] at hstar
    rcases hstar with ⟨hlap, hpos, hneg⟩ | ⟨hlap, hpos | hneg⟩
    · exact Or.inl ⟨hlap, hneg, hpos⟩
    · exact Or.inr ⟨hlap, Or.inr hpos⟩
    · exact Or.inr ⟨hlap, Or.inl hneg⟩

theorem IsBurningRank.quarterTurn {α : Type*} [LT α] {field : Field} {rank : Site → α}
    (h : IsBurningRank field rank) (direction : QuarterTurn) (offset : Site)
    (hoffset : ¬ EvenSite offset) {correction : Field} (hcorrection : Harmonic correction) :
    IsBurningRank (fun site => field (direction.mapSite offset site) + correction site)
      (fun site => rank (direction.mapSite offset site)) := by
  have h' : IsConstrainedBurningRank field rank (fun _ _ => True) := by
    intro site
    simpa only [true_and] using h site
  exact (h'.quarterTurn direction offset hoffset hcorrection).toIsBurningRank

end FLatticePaper
