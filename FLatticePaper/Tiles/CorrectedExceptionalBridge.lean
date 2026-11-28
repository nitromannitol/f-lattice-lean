import FLatticePaper.Tiles.CorrectedPureBridges
import FLatticePaper.Tiles.AltRotBase

/-! The shifted zero-tile bridge after rotation at a pure exit, including its contacts with the stem and head. -/

namespace FLatticePaper.Tiles.CorrectedExceptionalBridge

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard JointFamily PaperAltBase

def middle (plus : Bool) : Tile :=
  if plus then CorrectedPureBridges.grid else shift enlOdo.dom (1,1)
def rotated (plus : Bool) : Tile := shift (rot zeroTile) (if plus then (2,0) else (2,1))
def stemOffset (d : ℤ) (plus : Bool) : Site := if plus then (1,1) else (-d,3-2*d)
def headOffset (d : ℤ) (plus : Bool) : Site := if plus then (0,2) else (2-d,4-3*d)
def stem (d : ℤ) (plus : Bool) : Tile := shift (nstairN d) (stemOffset d plus)
def head (d : ℤ) (plus : Bool) : Tile := shift (shift (nearStairAltF d) (0,-1)) (headOffset d plus)

private theorem missing : middle true \ rotated true=({(0,2),(1,2),(2,2)} : Tile) ∧
    rotated true \ middle true=∅ ∧ middle false \ rotated false=({(2,0)} : Tile) ∧
    rotated false \ middle false=({(0,1)} : Tile) := by decide

/-- Relative to the bridge offset, all three extra upper sites at the positive foot lie on
the first head. At the other foot, the two exchanged sites lie in the first head and the last stem. -/
theorem contacts (d : ℤ) (hd : 3≤d) (plus : Bool) :
    middle plus \ rotated plus ⊆ head d plus ∧ rotated plus \ middle plus ⊆ stem d plus := by
  obtain ⟨upper,empty,left,right⟩ := missing
  cases plus
  · rw [left,right]
    constructor
    · intro z hz
      obtain rfl := Finset.mem_singleton.mp hz
      simp only [head,headOffset,Bool.false_eq_true,if_false,mem_shift,AltRotBase.mem_nearStairAltF_iff,
        AltRotBase.boxP,AltRotBase.nearP,Prod.fst_sub,Prod.snd_sub]
      omega
    · intro z hz
      obtain rfl := Finset.mem_singleton.mp hz
      rw [stem,stemOffset,if_neg (by decide),mem_shift,nstairN,mem_shift,mem_nstairF (by omega)]
      left; dsimp; omega
  · rw [upper,empty]
    refine ⟨?_,Finset.empty_subset _⟩
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    all_goals simp only [head,headOffset,if_true,mem_shift,AltRotBase.mem_nearStairAltF_iff,
      AltRotBase.boxP,AltRotBase.nearP,Prod.fst_sub,Prod.snd_sub]
    all_goals omega

/-- The two bridge choices give exactly the same union in the presence of the two incident tiles. -/
theorem union_eq (d : ℤ) (hd : 3≤d) (plus : Bool) :
    (stem d plus ∪ head d plus) ∪ middle plus=(stem d plus ∪ head d plus) ∪ rotated plus := by
  obtain ⟨h,s⟩ := contacts d hd plus
  ext z
  simp only [Finset.mem_union]
  constructor
  · rintro (old|m)
    · exact Or.inl old
    · by_cases r : z∈rotated plus
      · exact Or.inr r
      · exact Or.inl (Or.inr (h (Finset.mem_sdiff.mpr ⟨m,r⟩)))
  · rintro (old|r)
    · exact Or.inl old
    · by_cases m : z∈middle plus
      · exact Or.inr m
      · exact Or.inl (Or.inl (s (Finset.mem_sdiff.mpr ⟨r,m⟩)))

end FLatticePaper.Tiles.CorrectedExceptionalBridge
