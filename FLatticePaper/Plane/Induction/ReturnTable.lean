import FLatticePaper.Plane.Induction.W1FreeHfree
import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.FanCompat

/-! # The return table, reduced to the policy's quota and forced edges (AUDIT_FREE_THREE_STEP_RETURNS §2)

The table's three-edge returns (`TableShape`) are stated for the policy's retained relation `P.retained`. Its two sources of retained
edges are: a black centre retains both inputs (the quota `RetainQuota`), and every forced edge is retained (`forcedRetained`). So a
return edge `x → y` is secured by `EdgeOK G seed x y`: `x` is black with `y` an input, or `ForcedEdge G seed x y`. The table at a free root
therefore reduces to the seven shapes with `EdgeOK` edges and the `S`-memberships; `tableShape_of_edgeOK` transfers it to the policy.
The per-root obligations (which shape, which edges are forced by the fan, which sites lie in `S`) are not discharged here. -/

namespace FLatticePaper.ReturnTable

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1FreeHfree

/-- A return edge `x → y` is secured for the field `G`: `x` black with `y` one of its inputs, or a forced edge. -/
def EdgeOK (G : Field) (seed : Site → Site → Prop) (x y : Site) : Prop :=
  (laplacian G x = -1 ∧ (y = incomingNeg x ∨ y = incomingPos x)) ∨ ForcedEdge G seed x y

/-- A secured return edge is retained by the policy. -/
theorem edgeOK_retained {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) {x y : Site} (h : EdgeOK G seed x y) : P.retained x y := by
  rcases h with ⟨hb, hy⟩ | hf
  · have hq := P.quota
    unfold RetainQuota at hq
    obtain ⟨hq1, -⟩ := hq
    obtain ⟨h1, h2⟩ := hq1 x hb
    rcases hy with rfl | rfl
    · exact h1
    · exact h2
  · exact P.forcedRetained x y hf

/-- The table is monotone in its edge relation. -/
theorem tableShape_mono {Q R : Site → Site → Prop} (hQR : ∀ x y, Q x y → R x y) {S : Set Site} {z : Site}
    (h : TableShape Q S z) : TableShape R S z := by
  obtain ⟨z1, z2, hz, h⟩ := h
  refine ⟨z1, z2, hz, ?_⟩
  rcases h with ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ |
    ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩
  · exact Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩
  · exact Or.inr (Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, hQR _ _ c, hQR _ _ d, hQR _ _ e⟩)))))

/-- **The table transfers to the policy**: a table whose return edges are secured for `G` is a table for the retained relation. -/
theorem tableShape_of_edgeOK {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) {S : Set Site} {z : Site}
    (h : TableShape (EdgeOK G seed) S z) : TableShape P.retained S z :=
  tableShape_mono (fun _ _ hq => edgeOK_retained P hq) h


/-- A forcing derivation whose squares lie in `R` forces its conclusion white into `R` (the conclusion is a corner of its first square). -/
theorem forcedEdgeIn_mem {F : Field} {R : Site → Prop} {seed : Site → Site → Prop} {c i : Site}
    (h : FLatticePaper.W1.ForcedEdgeIn F R seed c i) : ¬ seed c i → R c := by
  induction h with
  | seed hs => exact fun hns => absurd hs hns
  | @unit _ _ c' _ _ hR hc _ _ _ _ _ _ => exact fun _ => hR c' hc

/-- **Strict forced whites are non-free.** A strict-interior site is non-free (`strictInterior_nonfree`). -/
theorem forcedNF_of_strict {frame : ChildFrame} (y : Site)
    (hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den y) : Nonfree frame y :=
  FLatticePaper.Induction.strictInterior_nonfree frame hSI

/-- An empty seed (the table's hypothesis `seed = fun _ _ => False`) has no seed edges. -/
theorem not_seed_of_empty {seed : Site → Site → Prop} (hs : seed = fun _ _ => False) :
    ∀ y i, ¬ seed y i := by
  intro y i
  rw [hs]
  exact fun h => h

/-- **Fan compatibility with the forced whites**, with the forced-nonfree premise `hforcedNF` explicit. The premise is not derivable:
a forced white need not be strict (`forcedNF_of_strict` covers strict sites), and a free forced white is possible. -/
theorem fan_agrees_of_witness {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hs : ∀ y i, ¬ seed y i)
    {sel : Site → Site} {D : Set Site}
    (hbin : ∀ y, laplacian G y = -1 ∨ laplacian G y = 0)
    (hblack : ∀ y ∈ D, laplacian G y = -1 → incomingNeg y ∈ D ∧ incomingPos y ∈ D)
    (hwhite : ∀ y ∈ D, laplacian G y = 0 → Nonfree frame y →
      sel y ∈ D ∧ (sel y = incomingNeg y ∨ sel y = incomingPos y))
    (hacyc : ∀ y, ¬ Relation.TransGen
      (FLatticePaper.FanCompat.fanRel G D (fun x => ¬ Nonfree frame x) sel) y y)
    (hforcedNF : ∀ y i, ForcedEdge G seed y i → laplacian G y = 0 → Nonfree frame y) :
    ∀ c i, ForcedEdge G seed c i → c ∈ D → Nonfree frame c → sel c = i := by
  intro c i h hD hnf
  exact FLatticePaper.FanCompat.fan_agrees_forced hbin hblack
    (fun y hy hw hnf' => hwhite y hy hw (not_not.mp hnf')) hacyc
    (fun y i' h' _ _ => absurd h' (hs y i'))
    (fun y i' hF hw => not_not.mpr (hforcedNF y i' hF hw))
    c i h hD (not_not.mpr hnf)

end FLatticePaper.ReturnTable
