import FLatticePaper.Farey.RotationLattice

namespace FLatticePaper.Checks

open Farey

example := lattice_rotation_odd (fraction := ⟨1, 2⟩) (by norm_num [Fraction.Odd])
example := lattice_rotation_even (fraction := ⟨1, 3⟩) (by norm_num [Fraction.Even])

#print axioms rot_parity_laplace
#print axioms lattice_rotation_odd
#print axioms lattice_rotation_even

end FLatticePaper.Checks
