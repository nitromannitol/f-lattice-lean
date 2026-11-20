import FLatticePaper.GeneralK.Columns

namespace FLatticePaper.GeneralK.Checks

private def sampleColumns : Field := fun site => 7 * site.2 + site.1

theorem three_retained_star_at_origin :
    laplacian 3 (liftColumns 3 sampleColumns) (0, 0) = 1 := by
  change laplacian 3 (liftColumns 3 sampleColumns) (columnSite 3 0 0 0) = 1
  rw [laplacian_liftColumns_columnSite (by decide : (2 : ℤ) ≤ 3)]
  decide

theorem three_chain_slope_drop_in_negative_column :
    laplacian 3 (liftColumns 3 sampleColumns) (-1, -1) = -1 := by
  change laplacian 3 (liftColumns 3 sampleColumns) (columnSite 3 (-1) (-1) 1) = -1
  rw [laplacian_liftColumns_openChain (by decide : (2 : ℤ) ≤ 3) _ _ _ _ (by decide) (by decide)]
  decide

#print axioms laplacian_two
#print axioms interpolate_first
#print axioms interpolate_last
#print axioms laplacian_liftColumns_columnSite
#print axioms laplacian_liftColumns_openChain
#print axioms superharmonic_liftColumns_iff
#print axioms three_retained_star_at_origin
#print axioms three_chain_slope_drop_in_negative_column

end FLatticePaper.GeneralK.Checks
