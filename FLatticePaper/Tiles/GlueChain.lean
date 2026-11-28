import FLatticePaper.Tiles.PTChain
import FLatticePaper.Tiles.GlueStringDecomp

/-! # Chains of placed register families along a child string

The family of a child string is the chain (`PTFamily.chainR`) of the families of the register strings, each placed at the
offset of its copy with the affine factor and constant of its subodometer (`PTFamily.placed`). This module gives the tile list
of a placed family (the register string started at the copy's offset, `placed_ts_*`), and the value clause of a chain: a
function agreeing with every placed block on the block's tiles agrees with the chain (`chainR_val`, `placed_val`). -/

namespace FLatticePaper.Tiles.GlueChain

open FLatticePaper.Tiles

/-! ### Translating a string -/

theorem zip_scanl_shift {α : Type*} : ∀ (L : List GInt) (ts : List α) (c s : GInt),
    (ts.zip (List.scanl (· + ·) c L)).map (fun p => (p.1, p.2 + s)) = ts.zip (List.scanl (· + ·) (c + s) L)
  | [], ts, c, s => by cases ts <;> simp
  | a :: L, ts, c, s => by
    cases ts with
    | nil => simp
    | cons t ts' =>
      simp only [List.scanl_cons, List.zip_cons_cons, List.map_cons]
      rw [zip_scanl_shift L ts' (c + a) s, show c + s + a = c + a + s by abel]

theorem hStringAt_shift (w : BinaryWord) (c s : GInt) :
    (hStringAt w c).map (fun p => (p.1, p.2 + s)) = hStringAt w (c + s) :=
  zip_scanl_shift _ _ c s

theorem hRevStringAt_shift (w : BinaryWord) (c s : GInt) :
    (hRevStringAt w c).map (fun p => (p.1, p.2 + s)) = hRevStringAt w (c + s) :=
  zip_scanl_shift _ _ c s

theorem vStringAt_shift (w : BinaryWord) (c s : GInt) :
    (vStringAt w c).map (fun p => (p.1, p.2 + s)) = vStringAt w (c + s) :=
  zip_scanl_shift _ _ c s

theorem vRevStringAt_shift (w : BinaryWord) (c s : GInt) :
    (vRevStringAt w c).map (fun p => (p.1, p.2 + s)) = vRevStringAt w (c + s) :=
  zip_scanl_shift _ _ c s

/-! ### Placed families -/

theorem placed_ts (F : PTFamily) (off a : GInt) (c : ℤ) :
    (F.placed off a c).ts = F.ts.map (fun p => (p.1, p.2 + off)) := rfl

theorem placed_dom (F : PTFamily) (off a : GInt) (c : ℤ) (k : ℕ) (hk : k < F.n) :
    (F.placed off a c).dom k = (F.dom k).map (· + off) :=
  PTFamily.translate_dom F off k hk

theorem placed_odo (F : PTFamily) (off a : GInt) (c : ℤ) (k : ℕ) (hk : k < F.n) (x : GInt) :
    (F.placed off a c).odo k x = F.odo k (x - off) + a.1 * x.1 + a.2 * x.2 + c := by
  unfold PTFamily.placed
  rw [PTFamily.affineAdd_odo, PTFamily.translate_odo F off k hk]

/-- **The value clause of a placed block.** If `o` is the odometer of the register family `F` on its tiles, and `g` is the
placed subodometer `o(x - off) + a^T x + c` on the tiles of the block, then `g` is the odometer of the placed family there. -/
theorem placed_val (F : PTFamily) (o g : GInt → ℤ) (off a : GInt) (c : ℤ)
    (hF : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y)
    (hg : ∀ k < F.n, ∀ x ∈ (F.placed off a c).dom k, g x = o (x - off) + a.1 * x.1 + a.2 * x.2 + c) :
    ∀ k < (F.placed off a c).n, ∀ x ∈ (F.placed off a c).dom k, g x = (F.placed off a c).odo k x := by
  intro k hk x hx
  rw [PTFamily.placed_n] at hk
  rw [hg k hk x hx, placed_odo F off a c k hk]
  have hx' := hx
  rw [placed_dom F off a c k hk] at hx'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
  rw [add_sub_cancel_right, hF k hk y hy]

/-! ### Chains -/

/-- **The value clause of a chain**: a function agreeing with each block on its tiles agrees with the chain. -/
theorem chainR_val (g : GInt → ℤ) (rest : List PTFamily) : ∀ (B : PTFamily),
    (∀ k < B.n, ∀ x ∈ B.dom k, g x = B.odo k x) →
    (∀ C ∈ rest, ∀ k < C.n, ∀ x ∈ C.dom k, g x = C.odo k x) →
    ∀ k < (PTFamily.chainR B rest).n, ∀ x ∈ (PTFamily.chainR B rest).dom k, g x = (PTFamily.chainR B rest).odo k x := by
  induction rest with
  | nil => intro B hB _; exact hB
  | cons C rest ih =>
    intro B hB hrest k hk x hx
    have hR := ih C (hrest C List.mem_cons_self) (fun D hD => hrest D (List.mem_cons_of_mem C hD))
    show g x = (B.append (PTFamily.chainR C rest)).odo k x
    change k < (B.append (PTFamily.chainR C rest)).n at hk
    change x ∈ (B.append (PTFamily.chainR C rest)).dom k at hx
    rw [PTFamily.append_n] at hk
    by_cases hkB : k < B.n
    · rw [PTFamily.append_dom_lt B _ k hkB] at hx
      rw [PTFamily.append_odo_lt B _ k hkB]
      exact hB k hkB x hx
    · obtain ⟨j, rfl⟩ : ∃ j, k = B.n + j := ⟨k - B.n, by omega⟩
      rw [PTFamily.append_dom_ge] at hx
      rw [PTFamily.append_odo_ge]
      exact hR j (by omega) x hx

theorem chainR_ts_two (B C : PTFamily) : (PTFamily.chainR B [C]).ts = B.ts ++ C.ts := rfl

theorem chainR_ts_three (B C D : PTFamily) : (PTFamily.chainR B [C, D]).ts = B.ts ++ C.ts ++ D.ts := by
  show B.ts ++ (C.ts ++ D.ts) = _
  rw [List.append_assoc]

end FLatticePaper.Tiles.GlueChain
