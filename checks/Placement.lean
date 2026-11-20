import FLatticePaper.Construction.PlacedAssembly

namespace FLatticePaper.Checks

open Construction

private def sparse : HeightTile Site where
  sites := {(-2, 5), (1, 3), (3, 3), (2, 8)}
  height site := site.val.1 - site.val.2

private theorem sparse_nonempty : sparse.sites.Nonempty := ⟨(1, 3), by decide⟩

example : sparse.lowerLeft sparse_nonempty = (1, 3) := by decide

example : sparse.upperRight sparse_nonempty = (2, 8) := by decide

example : sparse.boxOrigin sparse_nonempty = (-2, 3) := by decide

example : (0 : Site) ∉ (sparse.trim sparse_nonempty).sites := by decide

example : (0 : Site) ∈ (sparse.llCenter sparse_nonempty).sites :=
  sparse.zero_mem_llCenter sparse_nonempty

example :
    (sparse.place (-1000000, 1000000) (1, 0)).height ⟨(-999999, 1000003), by decide⟩ =
      -1000001 := by decide

example : (sparse.meldCorrection [] trivial sparse_nonempty).height ⟨(5, 0), by decide⟩ = 0 :=
  by decide

#print axioms HeightTile.place_height_at_add
#print axioms HeightTile.Agrees.place
#print axioms HeightTile.zero_mem_llCenter
#print axioms HeightTile.meldPlaced_agrees
#print axioms HeightTile.meldCorrection_agrees

end FLatticePaper.Checks
