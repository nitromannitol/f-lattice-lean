import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.BaseWeakLattice

/-! The base case of the tile properties, with the lattice compatibilities of the base odometers taken from
`BaseWeakLattice.weakProps_base` (so that no `WeakProps` hypothesis is needed). The helpers `tileProps_empty`,
`tileProps_three`, `tileProps_two` stay in `BaseTileProps`. -/

namespace FLatticePaper.Tiles.BaseTileProps

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.TileTranslation
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.BaseWeakLattice

/-- The base case of the tile properties (`lemma:tile-odometer-existence` (a), (b) at the base words), with the paper base
conditions as hypotheses. The lattice compatibilities `WeakProps` are those of `weakProps_base`, which is proved from the
paper base condition alone. -/
theorem base_tileProps (w : Word) (hw : IsBase w) (O E aO aE : PartialOdometer) (hS : PaperBaseCond w O E)
    (hA : PaperAltBaseCond w aO aE) : TileProps w O E aO aE := by
  have hW : WeakProps w O E := weakProps_base w hw O E hS
  rcases hw with rfl | h3 | h2
  · exact tileProps_empty O E aO aE hS hA hW
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h3⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact tileProps_empty O E aO aE hS hA hW
    · exact tileProps_three k hk O E aO aE hS hA hW
  · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two := ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, h2⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact tileProps_empty O E aO aE hS hA hW
    · exact tileProps_two k hk O E aO aE hS hA hW

end FLatticePaper.Tiles.BaseTileProps
