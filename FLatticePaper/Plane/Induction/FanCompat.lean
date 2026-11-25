import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.FanAcyclic
import FLatticePaper.Plane.Induction.AndOrRank

/-! # Fan compatibility with the W1-forced whites (AUDIT_FREE_THREE_STEP_RETURNS §1, "Fan compatibility")

Let `G` be a directed graph on a vertex set `V` with: each black vertex has both inputs as successors; each white vertex has one successor,
an input; successors of vertices of `V` lie in `V`; and `G` lowers a rank strictly along its edges (the contact fan's rank, `FanAcyclic`).
Then every W1-forced white of `V` (a `ForcedEdge` at a vertex of `V`) is selected by `G` with the forced input. The proof is the audit's:
a conflicting selection starts a walk inside the forcing square, which by the induction hypothesis stays in `G` and must close, contradicting
the strictly decreasing rank. -/

namespace FLatticePaper.FanCompat

open FLatticePaper FLatticePaper.Induction FLatticePaper.AndOrRank FLatticePaper.SquareClauses

/-- Exactly one input of a corner of a unit square lies in the square. -/
theorem mem_squareCorners_iff (a b : ℤ) (p : Site) :
    p ∈ squareCorners a b ↔ (p.1 = a ∨ p.1 = a + 1) ∧ (p.2 = b ∨ p.2 = b + 1) := by
  obtain ⟨x, y⟩ := p
  unfold squareCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem square_one_input (a b : ℤ) {c : Site} (hc : c ∈ squareCorners a b) :
    (incomingNeg c ∈ squareCorners a b) ↔ ¬ (incomingPos c ∈ squareCorners a b) := by
  rw [mem_squareCorners_iff] at hc
  simp only [mem_squareCorners_iff]
  obtain ⟨x, y⟩ := c
  unfold incomingNeg incomingPos EvenSite at *
  by_cases hp : (x + y) % 2 = 0
  · rw [if_pos hp, if_pos hp]
    dsimp only at hc ⊢
    constructor <;> intro h <;> omega
  · rw [if_neg hp, if_neg hp]
    dsimp only at hc ⊢
    constructor <;> intro h <;> omega

/-- The corners of a unit square have at most four elements. -/
theorem squareCorners_card_le (a b : ℤ) : (squareCorners a b).card ≤ 4 := by
  unfold squareCorners
  have h1 := Finset.card_insert_le (a, b) ({(a + 1, b), (a, b + 1), (a + 1, b + 1)} : Finset Site)
  have h2 := Finset.card_insert_le (a + 1, b) ({(a, b + 1), (a + 1, b + 1)} : Finset Site)
  have h3 := Finset.card_insert_le (a, b + 1) ({(a + 1, b + 1)} : Finset Site)
  have h4 := Finset.card_singleton (a + 1, b + 1)
  omega

/-- The input of a corner `x` of the square that lies in the square (`square_one_input`). -/
def sqIn (a b : ℤ) (x : Site) : Site :=
  if incomingNeg x ∈ squareCorners a b then incomingNeg x else incomingPos x

theorem sqIn_spec {a b : ℤ} {x : Site} (hx : x ∈ squareCorners a b) :
    sqIn a b x ∈ squareCorners a b ∧ (sqIn a b x = incomingNeg x ∨ sqIn a b x = incomingPos x) := by
  have h := square_one_input a b hx
  unfold sqIn
  split_ifs with hn
  · exact ⟨hn, Or.inl rfl⟩
  · refine ⟨?_, Or.inr rfl⟩
    by_contra hp
    exact hn (h.mpr hp)

theorem sqIn_eq_of_input {a b : ℤ} {x y : Site} (hx : x ∈ squareCorners a b) (hy : y ∈ squareCorners a b)
    (hyin : y = incomingNeg x ∨ y = incomingPos x) : sqIn a b x = y := by
  have h := square_one_input a b hx
  unfold sqIn
  rcases hyin with rfl | rfl
  · rw [if_pos hy]
  · rw [if_neg]
    intro hn
    exact (h.mp hn) hy

/-- The fan relation on the physical subgraph `D`: both inputs at a black site, the selected input at a non-free white site. -/
def fanRel (F : Field) (D : Set Site) (free : Site → Prop) (sel : Site → Site) (x y : Site) : Prop :=
  x ∈ D ∧ ((laplacian F x = -1 ∧ (y = incomingNeg x ∨ y = incomingPos x) ∧ y ∈ D) ∨
    (laplacian F x = 0 ∧ ¬ free x ∧ y = sel x ∧ y ∈ D))

/-- **Fan compatibility (audit §1).** On a physical subgraph `D` whose black sites have both inputs in `D`, whose non-free white
sites have their selected input in `D`, and which has no fan-relation cycle, every W1-forced non-free white of `D` selects its forced
input. The proof: if it selected the other input, the in-square inputs of the four corners form a closed walk in the fan relation,
which has a repeated corner by pigeonhole, a cycle. The hypothesis `hforcedNF` (forced whites are non-free) is the audit's
structural input; it is the part of the forcing square that the W1 adjacency lemma must supply. -/
theorem fan_agrees_forced {F : Field} {seed : Site → Site → Prop} {sel : Site → Site}
    {D : Set Site} {free : Site → Prop}
    (hbin : ∀ y, laplacian F y = -1 ∨ laplacian F y = 0)
    (hblack : ∀ y ∈ D, laplacian F y = -1 → incomingNeg y ∈ D ∧ incomingPos y ∈ D)
    (hwhite : ∀ y ∈ D, laplacian F y = 0 → ¬ free y →
      sel y ∈ D ∧ (sel y = incomingNeg y ∨ sel y = incomingPos y))
    (hacyc : ∀ y, ¬ Relation.TransGen (fanRel F D free sel) y y)
    (hseed : ∀ y i, seed y i → y ∈ D → ¬ free y → sel y = i)
    (hforcedNF : ∀ y i, ForcedEdge F seed y i → laplacian F y = 0 → ¬ free y) :
    ∀ c i, ForcedEdge F seed c i → c ∈ D → ¬ free c → sel c = i := by
  intro c i h
  induction h with
  | seed hs => exact fun hD hnf => hseed _ _ hs hD hnf
  | @unit a b x o inside hx hw ho hout hin hforced ih =>
    intro hD hnf
    obtain ⟨hselD, hselIn⟩ := hwhite x hD hw hnf
    by_contra hne
    have hiff := square_one_input a b hx
    have hsel_sq : sel x ∈ squareCorners a b := by
      rcases ho with ho | ho
      · rcases hselIn with hs | hs
        · exact absurd (hs.trans ho.symm) hne
        · rw [hs]
          by_contra hp
          exact hout (by rw [ho]; exact hiff.mpr hp)
      · rcases hselIn with hs | hs
        · rw [hs]
          by_contra hn
          exact hout (by rw [ho]; by_contra hp; exact hn (hiff.mpr hp))
        · exact absurd (hs.trans ho.symm) hne
    have hsc : sel x = sqIn a b x := (sqIn_eq_of_input hx hsel_sq hselIn).symm
    have hedge : ∀ y, y ∈ squareCorners a b → y ∈ D →
        sqIn a b y ∈ squareCorners a b ∧ sqIn a b y ∈ D ∧ fanRel F D free sel y (sqIn a b y) := by
      intro y hy hyD
      have hspec := sqIn_spec hy
      rcases hbin y with hb | hw0
      · obtain ⟨h1, h2⟩ := hblack y hyD hb
        have hmemD : sqIn a b y ∈ D := by
          rcases hspec.2 with h | h
          · rw [h]; exact h1
          · rw [h]; exact h2
        refine ⟨hspec.1, hmemD, ?_⟩
        unfold fanRel
        exact ⟨hyD, Or.inl ⟨hb, hspec.2, hmemD⟩⟩
      · by_cases hyx : y = x
        · subst hyx
          have hmemD : sqIn a b y ∈ D := by rw [← hsc]; exact hselD
          refine ⟨hspec.1, hmemD, ?_⟩
          unfold fanRel
          exact ⟨hyD, Or.inr ⟨hw0, hnf, hsc.symm, hmemD⟩⟩
        · have hfy := hforced y hy hyx hw0
          have hnfy : ¬ free y := hforcedNF y _ hfy hw0
          have hyeq : sqIn a b y = sel y := by
            rcases hin y hy hyx with hb | ⟨-, hins, hinp⟩
            · omega
            · exact (sqIn_eq_of_input hy hins hinp).trans (ih y hy hyx hw0 hyD hnfy).symm
          have hmemD : sqIn a b y ∈ D := by rw [hyeq]; exact (hwhite y hyD hw0 hnfy).1
          refine ⟨hspec.1, hmemD, ?_⟩
          unfold fanRel
          exact ⟨hyD, Or.inr ⟨hw0, hnfy, hyeq, hmemD⟩⟩
    have hchain : ∀ n : ℕ, (sqIn a b)^[n] x ∈ squareCorners a b ∧ (sqIn a b)^[n] x ∈ D := by
      intro n
      induction n with
      | zero => exact ⟨hx, hD⟩
      | succ n ihn =>
        rw [Function.iterate_succ_apply']
        obtain ⟨h1, h2⟩ := ihn
        exact ⟨(hedge _ h1 h2).1, (hedge _ h1 h2).2.1⟩
    have hrel : ∀ n : ℕ, fanRel F D free sel ((sqIn a b)^[n] x) ((sqIn a b)^[n + 1] x) := by
      intro n
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := hchain n
      exact (hedge _ h1 h2).2.2
    have hpath : ∀ j m : ℕ, Relation.TransGen (fanRel F D free sel)
        ((sqIn a b)^[j] x) ((sqIn a b)^[j + m + 1] x) := by
      intro j m
      induction m with
      | zero => exact Relation.TransGen.single (hrel j)
      | succ m ihm =>
        have h := hrel (j + m + 1)
        have e : j + (m + 1) + 1 = j + m + 1 + 1 := by omega
        rw [e]
        exact ihm.tail h
    have hcyc : ∀ j m : ℕ, (sqIn a b)^[j] x ≠ (sqIn a b)^[j + m + 1] x := by
      intro j m heq
      have h2 := hpath j m
      rw [← heq] at h2
      exact hacyc _ h2
    have hcard : (squareCorners a b).card < (Finset.range 5).card := by
      rw [Finset.card_range]
      have := squareCorners_card_le a b
      omega
    obtain ⟨p, -, q, -, hpq, hfeq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun n : ℕ => (sqIn a b)^[n] x) hcard
        (fun n _ => (hchain n).1)
    rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
    · obtain ⟨m, hm⟩ : ∃ m, q = p + m + 1 := ⟨q - p - 1, by omega⟩
      subst hm
      exact hcyc p m hfeq
    · obtain ⟨m, hm⟩ : ∃ m, p = q + m + 1 := ⟨p - q - 1, by omega⟩
      subst hm
      exact hcyc q m hfeq.symm

end FLatticePaper.FanCompat
