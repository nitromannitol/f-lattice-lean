import FLatticePaper.Tiles.PTAffineTransport

/-! The concatenation of two placed families along a string: the tile list of `F.append G` is `F.ts ++ G.ts`, the first `F.n`
tiles keep the affine data of `F`, the next `G.n` tiles that of `G`. The `Respects` clause of the concatenation is the clause of
each block, plus the clause at the seam (the last tile of `F` against the first tile of `G`), which is a hypothesis here: it is
the junction condition that T1 has to verify from H2 and H3. -/

namespace FLatticePaper.Tiles

/-- The concatenation of two families. -/
def PTFamily.append (F G : PTFamily) : PTFamily :=
  { ts := F.ts ++ G.ts,
    a := fun k => if k < F.ts.length then F.a k else G.a (k - F.ts.length),
    b := fun k => if k < F.ts.length then F.b k else G.b (k - F.ts.length) }

theorem PTFamily.append_n (F G : PTFamily) : (F.append G).n = F.n + G.n := by
  simp [PTFamily.n, PTFamily.append]

theorem PTFamily.append_tile_lt (F G : PTFamily) (k : ℕ) (hk : k < F.n) :
    (F.append G).tile k = F.tile k := by
  unfold PTFamily.tile PTFamily.n at *
  simp only [PTFamily.append]
  rw [List.getD_append _ _ _ _ hk]

theorem PTFamily.append_tile_ge (F G : PTFamily) (k : ℕ) :
    (F.append G).tile (F.n + k) = G.tile k := by
  unfold PTFamily.tile PTFamily.n
  simp only [PTFamily.append]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem PTFamily.append_a_lt (F G : PTFamily) (k : ℕ) (hk : k < F.n) : (F.append G).a k = F.a k := by
  unfold PTFamily.n at hk
  simp [PTFamily.append, hk]

theorem PTFamily.append_a_ge (F G : PTFamily) (k : ℕ) : (F.append G).a (F.n + k) = G.a k := by
  unfold PTFamily.n
  simp [PTFamily.append]

theorem PTFamily.append_b_lt (F G : PTFamily) (k : ℕ) (hk : k < F.n) : (F.append G).b k = F.b k := by
  unfold PTFamily.n at hk
  simp [PTFamily.append, hk]

theorem PTFamily.append_b_ge (F G : PTFamily) (k : ℕ) : (F.append G).b (F.n + k) = G.b k := by
  unfold PTFamily.n
  simp [PTFamily.append]

theorem PTFamily.append_odo_lt (F G : PTFamily) (k : ℕ) (hk : k < F.n) (x : GInt) :
    (F.append G).odo k x = F.odo k x := by
  unfold PTFamily.odo
  rw [PTFamily.append_tile_lt F G k hk, PTFamily.append_a_lt F G k hk, PTFamily.append_b_lt F G k hk]

theorem PTFamily.append_odo_ge (F G : PTFamily) (k : ℕ) (x : GInt) :
    (F.append G).odo (F.n + k) x = G.odo k x := by
  unfold PTFamily.odo
  rw [PTFamily.append_tile_ge F G k, PTFamily.append_a_ge F G k, PTFamily.append_b_ge F G k]

theorem PTFamily.append_dom_lt (F G : PTFamily) (k : ℕ) (hk : k < F.n) :
    (F.append G).dom k = F.dom k := by
  unfold PTFamily.dom
  rw [PTFamily.append_tile_lt F G k hk]

theorem PTFamily.append_dom_ge (F G : PTFamily) (k : ℕ) : (F.append G).dom (F.n + k) = G.dom k := by
  unfold PTFamily.dom
  rw [PTFamily.append_tile_ge F G k]

/-- The seam clause: the `Respects` clause of the two blocks joined at the last tile of `F` and the first tile of `G`. -/
def PTFamily.SeamClause (o : Orientation) (rev : Bool) (F G : PTFamily) : Prop :=
  slopeOf (G.odo 0) (G.dom 0) - slopeOf (F.odo (F.n - 1)) (F.dom (F.n - 1)) =
      surgicalSlopeDiff o rev (zTileLetter (F.tile (F.n - 1)).1) (zTileLetter (G.tile 0).1) ∧
    ((¬ ∃ x, x ∈ F.dom (F.n - 1) ∧ x ∈ G.dom 0) →
      ∀ x ∈ F.dom (F.n - 1), ∀ y ∈ G.dom 0, unitApart x y →
        (o = .horizontal →
            F.odo (F.n - 1) x - ptDot (F.a (F.n - 1)) x = G.odo 0 y - ptDot (F.a (F.n - 1)) y) ∧
          (o = .vertical →
            (G.odo 0 y - ptDot (F.a (F.n - 1)) y) - (F.odo (F.n - 1) x - ptDot (F.a (F.n - 1)) x) = -1))

/-- **The concatenation respects the string** when both blocks respect it and the seam clause holds. -/
theorem PTFamily.append_respects (F G : PTFamily) (o : Orientation) (rev : Bool)
    (hF : F.Respects o rev) (hG : G.Respects o rev) (hF0 : 0 < F.n) (hG0 : 0 < G.n)
    (hseam : PTFamily.SeamClause o rev F G) : (F.append G).Respects o rev := by
  intro k hk
  rw [PTFamily.append_n] at hk
  rcases lt_trichotomy (k + 1) F.n with h1 | h1 | h1
  · -- inside F
    have hk' : k < F.n := by omega
    have hk1 : k + 1 < F.n := h1
    obtain ⟨hsl, hcl⟩ := hF k hk1
    refine ⟨?_, ?_⟩
    · have e : (F.append G).odo k = F.odo k := funext (PTFamily.append_odo_lt F G k hk')
      have e' : (F.append G).odo (k + 1) = F.odo (k + 1) := funext (PTFamily.append_odo_lt F G (k + 1) hk1)
      rw [e, e', PTFamily.append_dom_lt F G k hk', PTFamily.append_dom_lt F G (k + 1) hk1]
      have ht0 : (F.append G).tile k = F.tile k := PTFamily.append_tile_lt F G k hk'
      have ht1 : (F.append G).tile (k + 1) = F.tile (k + 1) := PTFamily.append_tile_lt F G (k + 1) hk1
      rw [ht0, ht1]
      exact hsl
    · intro hno x hx y hy hu
      have hno' : ¬ ∃ z, z ∈ F.dom k ∧ z ∈ F.dom (k + 1) := by
        rintro ⟨z, h1', h2'⟩
        apply hno
        refine ⟨z, ?_, ?_⟩
        · rw [PTFamily.append_dom_lt F G k hk']; exact h1'
        · rw [PTFamily.append_dom_lt F G (k + 1) hk1]; exact h2'
      have hx' : x ∈ F.dom k := by rw [← PTFamily.append_dom_lt F G k hk']; exact hx
      have hy' : y ∈ F.dom (k + 1) := by rw [← PTFamily.append_dom_lt F G (k + 1) hk1]; exact hy
      obtain ⟨hH, hV⟩ := hcl hno' x hx' y hy' hu
      have ha0 : (F.append G).a k = F.a k := PTFamily.append_a_lt F G k hk'
      rw [PTFamily.append_odo_lt F G k hk' x, PTFamily.append_odo_lt F G (k + 1) hk1 y, ha0]
      exact ⟨fun h0 => hH h0, fun h0 => hV h0⟩
  · -- the seam
    have hk' : k = F.n - 1 := by omega
    subst hk'
    have hn : F.n - 1 + 1 = F.n := by omega
    have hsame : (F.append G).tile (F.n - 1) = F.tile (F.n - 1) := PTFamily.append_tile_lt F G (F.n - 1) (by omega)
    refine ⟨?_, ?_⟩
    · have e0 : (F.append G).odo (F.n - 1) = F.odo (F.n - 1) := funext (PTFamily.append_odo_lt F G (F.n - 1) (by omega))
      have e1 : (F.append G).odo (F.n - 1 + 1) = G.odo 0 := by
        rw [hn]
        have := PTFamily.append_odo_ge F G 0
        rw [Nat.add_zero] at this
        exact funext fun x => this x
      have d0 : (F.append G).dom (F.n - 1) = F.dom (F.n - 1) := PTFamily.append_dom_lt F G (F.n - 1) (by omega)
      have d1 : (F.append G).dom (F.n - 1 + 1) = G.dom 0 := by
        rw [hn]
        have := PTFamily.append_dom_ge F G 0
        rw [Nat.add_zero] at this
        exact this
      have ht1 : (F.append G).tile (F.n - 1 + 1) = G.tile 0 := by
        rw [hn]
        have := PTFamily.append_tile_ge F G 0
        rw [Nat.add_zero] at this
        exact this
      rw [e0, e1, d0, d1, hsame, ht1]
      exact hseam.1
    · intro hno x hx y hy hu
      have hn' : ¬ ∃ z, z ∈ F.dom (F.n - 1) ∧ z ∈ G.dom 0 := by
        rintro ⟨z, h1', h2'⟩
        apply hno
        refine ⟨z, ?_, ?_⟩
        · rw [PTFamily.append_dom_lt F G (F.n - 1) (by omega)]; exact h1'
        · rw [hn]
          have := PTFamily.append_dom_ge F G 0
          rw [Nat.add_zero] at this
          rw [this]; exact h2'
      have hx' : x ∈ F.dom (F.n - 1) := by rw [← PTFamily.append_dom_lt F G (F.n - 1) (by omega)]; exact hx
      have hy' : y ∈ G.dom 0 := by
        have := PTFamily.append_dom_ge F G 0
        rw [Nat.add_zero] at this
        rw [← this]
        rw [hn] at hy
        exact hy
      obtain ⟨hH, hV⟩ := hseam.2 hn' x hx' y hy' hu
      have ha0 : (F.append G).a (F.n - 1) = F.a (F.n - 1) := PTFamily.append_a_lt F G (F.n - 1) (by omega)
      have o0 : (F.append G).odo (F.n - 1) x = F.odo (F.n - 1) x := PTFamily.append_odo_lt F G (F.n - 1) (by omega) x
      have o1 : (F.append G).odo (F.n - 1 + 1) y = G.odo 0 y := by
        rw [hn]
        have := PTFamily.append_odo_ge F G 0 y
        rw [Nat.add_zero] at this
        exact this
      rw [o0, o1, ha0]
      exact ⟨fun h0 => hH h0, fun h0 => hV h0⟩
  · -- inside G
    obtain ⟨j, hj⟩ : ∃ j, k = F.n + j := ⟨k - F.n, by omega⟩
    subst hj
    have hj1 : j + 1 < G.n := by omega
    obtain ⟨hsl, hcl⟩ := hG j hj1
    have hsucc : F.n + j + 1 = F.n + (j + 1) := by omega
    rw [hsucc]
    refine ⟨?_, ?_⟩
    · have hjG : j < G.n := by omega
      have e0 : (F.append G).odo (F.n + j) = G.odo j := funext (PTFamily.append_odo_ge F G j)
      have e1 : (F.append G).odo (F.n + (j + 1)) = G.odo (j + 1) := funext (PTFamily.append_odo_ge F G (j + 1))
      have d0 : (F.append G).dom (F.n + j) = G.dom j := PTFamily.append_dom_ge F G j
      have d1 : (F.append G).dom (F.n + (j + 1)) = G.dom (j + 1) := PTFamily.append_dom_ge F G (j + 1)
      rw [e0, e1, d0, d1]
      have ht0 : (F.append G).tile (F.n + j) = G.tile j := PTFamily.append_tile_ge F G j
      have ht1 : (F.append G).tile (F.n + (j + 1)) = G.tile (j + 1) := PTFamily.append_tile_ge F G (j + 1)
      rw [ht0, ht1]
      exact hsl
    · intro hno x hx y hy hu
      have hno' : ¬ ∃ z, z ∈ G.dom j ∧ z ∈ G.dom (j + 1) := by
        rintro ⟨z, h1', h2'⟩
        apply hno
        refine ⟨z, ?_, ?_⟩
        · rw [PTFamily.append_dom_ge F G j]; exact h1'
        · rw [PTFamily.append_dom_ge F G (j + 1)]; exact h2'
      have hx' : x ∈ G.dom j := by rw [← PTFamily.append_dom_ge F G j]; exact hx
      have hy' : y ∈ G.dom (j + 1) := by rw [← PTFamily.append_dom_ge F G (j + 1)]; exact hy
      obtain ⟨hH, hV⟩ := hcl hno' x hx' y hy' hu
      have ha0 : (F.append G).a (F.n + j) = G.a j := PTFamily.append_a_ge F G j
      rw [PTFamily.append_odo_ge F G j x, PTFamily.append_odo_ge F G (j + 1) y, ha0]
      exact ⟨fun h0 => hH h0, fun h0 => hV h0⟩

end FLatticePaper.Tiles
