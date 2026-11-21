import FLatticePaper.GeneralK.ColumnGraph
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace FLatticePaper.GeneralK.ColumnSlice

/-- A simple directed cycle of the finite shape graph. Its length is
positive and at most the number of vertices. Each slot has one outgoing edge,
including the last slot back to the first. -/
abbrev SimpleCycle (slice : ColumnSlice) (sector : ℤ) :=
  Σ size : Fin (Fintype.card (slice.Vertex sector) + 1),
    {vertices : Fin size.val → slice.Vertex sector //
      0 < size.val ∧ Function.Injective vertices ∧ ∀ i, IsEdge (vertices i) (vertices (cyclicSucc i))}

/-- The zero shape gives one legal cycle through all column phases. -/
def zeroCycle (slice : ColumnSlice) (sector : ℤ) : slice.SimpleCycle sector := by
  let vertices (phase : Fin slice.phasePeriod) : slice.Vertex sector :=
    (phase, slice.zeroShape sector, slice.zeroShape sector)
  have hinj : Function.Injective vertices := fun _ _ heq => congrArg Prod.fst heq
  have hsize : slice.phasePeriod < Fintype.card (slice.Vertex sector) + 1 := by
    have h := Fintype.card_le_of_injective vertices hinj
    rw [Fintype.card_fin] at h
    omega
  exact ⟨⟨slice.phasePeriod, hsize⟩, vertices, slice.phasePeriod_pos, hinj,
    fun _ => ⟨rfl, rfl⟩⟩

/-- The arithmetic mean of the physical row weights along a simple cycle. -/
def cycleMean (slice : ColumnSlice) (sector : ℤ) (cycle : slice.SimpleCycle sector) : ℚ :=
  (∑ i : Fin cycle.1.val, (slice.edgeWeight sector (cycle.2.val i) (cycle.2.val (cyclicSucc i)) : ℚ)) /
    (cycle.1.val : ℚ)

/-- The sectors `0 ≤ d < kL`. -/
abbrev Sector (slice : ColumnSlice) := Fin (slice.k.toNat * slice.length)

theorem sectorCount_pos (slice : ColumnSlice) : 0 < slice.k.toNat * slice.length :=
  Nat.mul_pos (by have := slice.hk; omega) slice.length_pos

private abbrev SectorCycle (slice : ColumnSlice) := Σ sector : slice.Sector, slice.SimpleCycle sector.val

private noncomputable def cycleMeans (slice : ColumnSlice) : Finset ℚ := by
  classical
  exact Finset.univ.image (fun cycle : slice.SectorCycle => slice.cycleMean cycle.1.val cycle.2)

private theorem mem_cycleMeans (slice : ColumnSlice) (sector : slice.Sector) (cycle : slice.SimpleCycle sector.val) :
    slice.cycleMean sector.val cycle ∈ slice.cycleMeans := by
  classical
  exact Finset.mem_image_of_mem (fun cycle : slice.SectorCycle => slice.cycleMean cycle.1.val cycle.2)
    (Finset.mem_univ ⟨sector, cycle⟩)

private theorem cycleMeans_nonempty (slice : ColumnSlice) : slice.cycleMeans.Nonempty := by
  let sector : slice.Sector := ⟨0, slice.sectorCount_pos⟩
  exact ⟨_, slice.mem_cycleMeans sector (slice.zeroCycle sector.val)⟩

/-- The explicit rational first-entry formula in the column classification.
The maximum ranges over every sector and simple directed cycle in that sector. -/
noncomputable def cyclePeak (slice : ColumnSlice) : ℚ :=
  (slice.a₀ : ℚ) + slice.cycleMeans.max' slice.cycleMeans_nonempty

theorem le_cyclePeak (slice : ColumnSlice) (sector : slice.Sector) (cycle : slice.SimpleCycle sector.val) :
    (slice.a₀ : ℚ) + slice.cycleMean sector.val cycle ≤ slice.cyclePeak := by
  unfold cyclePeak
  exact add_le_add_right (Finset.le_max' _ _ (slice.mem_cycleMeans sector cycle)) _

theorem cyclePeak_attained (slice : ColumnSlice) :
    ∃ (sector : slice.Sector) (cycle : slice.SimpleCycle sector.val),
      slice.cyclePeak = (slice.a₀ : ℚ) + slice.cycleMean sector.val cycle := by
  classical
  have hmem := Finset.max'_mem slice.cycleMeans slice.cycleMeans_nonempty
  unfold cycleMeans at hmem
  obtain ⟨⟨sector, cycle⟩, _, hmax⟩ := Finset.mem_image.mp hmem
  exact ⟨sector, cycle, congrArg ((slice.a₀ : ℚ) + ·) hmax.symm⟩

end FLatticePaper.GeneralK.ColumnSlice
