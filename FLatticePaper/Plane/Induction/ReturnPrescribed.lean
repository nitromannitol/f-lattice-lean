import FLatticePaper.Plane.Induction.ReturnTable
import FLatticePaper.Plane.Induction.FreeAdjacency
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.GameFort

/-! # The prescription edge and the reflected shape (AUDIT §2 under the sign convention of `prescribedH`)

The policy the table runs on is `oldPolicyData_of_canonical`, whose free whites keep their prescribed input (`PrescribedAt`).
`prescribedH η` is `E` at even H sites (away from `hFirst`, `hLast`) and `N` at odd ones: the audit's horizontal sign `+` table is
the reflected `I − z` picture (`W` ↔ `E`, `S` ↔ `N`). Under this convention the audit's shape 1 (`z+N → z+E+N → z+E → z`) becomes the
disjunct `z+S → z+SW → z+W → z` (the disjunct 7 of `TableShape`), whose last edge `z+W → z` is a prescription (`z+W` even, prescribed `E`).

`EdgeP` adds the prescription case to `EdgeOK`. `shapeSeven_of_edgeP` gives the table's disjunct 7 from its three edges;
its middle edge `z+SW → z+W` is secured by free adjacency (`edgeOK_of_free_input`), its last edge by the prescription, and its first
edge `z+S → z+SW` is the fan edge (named). -/

namespace FLatticePaper.ReturnPrescribed

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1FreeHfree FLatticePaper.ReturnTable
  FLatticePaper.FreeAdjacency FLatticePaper.GameFort

/-- A return edge secured for the policy of sign `η`: `EdgeOK`, or a free white `x` with its prescribed input `y`. -/
def EdgeP (frame : ChildFrame) (η : ℤ) (G : Field) (seed : Site → Site → Prop) (x y : Site) : Prop :=
  EdgeOK G seed x y ∨ (x ∈ frame.freeH ∧ laplacian G x = 0 ∧ y = x + frame.prescribedH η x) ∨
    (x ∈ frame.freeV ∧ laplacian G x = 0 ∧ y = x + frame.prescribedV η x)

/-- A secured prescription edge is retained by the policy (`PrescribedAt` of the canonical policy). -/
theorem edgeP_retained {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) (hpres : PrescribedAt frame G η P.retained) {x y : Site}
    (h : EdgeP frame η G seed x y) : P.retained x y := by
  rcases h with h | ⟨hf, hl, hy⟩ | ⟨hf, hl, hy⟩
  · exact edgeOK_retained P h
  · rw [hy]
    exact (hpres.1 x hf hl _).mpr rfl
  · rw [hy]
    exact (hpres.2 x hf hl _).mpr rfl

/-- The table transfers to the policy with the prescription edges. -/
theorem tableShape_of_edgeP {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) (hpres : PrescribedAt frame G η P.retained) {S : Set Site} {z : Site}
    (h : TableShape (EdgeP frame η G seed) S z) : TableShape P.retained S z :=
  tableShape_mono (fun _ _ hq => edgeP_retained P hpres hq) h

/-- The prescribed horizontal direction at an even H site away from `hFirst`, `hLast` is `E`. -/
theorem prescribedH_even {frame : ChildFrame} (η : ℤ) {x : Site} (he : EvenSite x)
    (h1 : x ≠ hFirst) (h2 : x ≠ frame.hLast) : frame.prescribedH η x = (1, 0) := by
  unfold ChildFrame.prescribedH
  rw [if_neg h1, if_neg h2, if_pos he]

/-- **A white with a free white input.** A non-free white `x` with an input `y` that is a free white (`y ∈ freeH ∪ freeV`, `laplacian y = 0`)
retains `y` (`forced_input_of_free`); a black `x` retains both inputs. -/
theorem edgeOK_of_free_input {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hs : ∀ y i, ¬ seed y i) {x y : Site}
    (hbin : laplacian G x = -1 ∨ laplacian G x = 0)
    (hF : laplacian G x = 0 → ∃ i, ForcedEdge G seed x i)
    (hy : y = incomingNeg x ∨ y = incomingPos x) (hyfree : y ∈ frame.freeH ∪ frame.freeV)
    (hyw : laplacian G y = 0) : EdgeOK G seed x y := by
  rcases hbin with hb | hw
  · exact Or.inl ⟨hb, hy⟩
  · obtain ⟨i, hi⟩ := hF hw
    have hyi : y = i := forced_input_of_free P hs hi hy hyw (not_nonfree_of_free frame hyfree)
    exact Or.inr (by rw [hyi]; exact hi)

/-- **Shape 7 (the reflected audit shape 1) from its three edges.** `z+S → z+SW` (the fan edge, named as `e1`), `z+SW → z+W`
(free adjacency, `e2`), `z+W → z` (the prescription, `e3`), with the `S`-memberships of the chain points. -/
theorem shapeSeven_of_edgeP {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) (hpres : PrescribedAt frame G η P.retained) {S : Set Site} {z1 z2 : ℤ}
    (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 - 1) ∈ S ∧ (z1 - 1, z2 - 1) ∈ S ∧ (z1 - 1, z2) ∈ S)
    (e1 : EdgeP frame η G seed (z1, z2 - 1) (z1 - 1, z2 - 1))
    (e2 : EdgeP frame η G seed (z1 - 1, z2 - 1) (z1 - 1, z2))
    (e3 : EdgeP frame η G seed (z1 - 1, z2) (z1, z2)) :
    TableShape P.retained S (z1, z2) :=
  tableShape_of_edgeP P hpres
    ⟨z1, z2, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz, hS, e1, e2, e3⟩)))))⟩

end FLatticePaper.ReturnPrescribed
