import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Gluing partial odometers along constant overlap offsets (`lemma:pairwise_compatibility`). -/

namespace FLatticePaper.Tiles

variable {α ι : Type*}

/-- The overlap graph of a family of domains: distinct indices are adjacent when their domains meet. -/
def overlapGraph (domain : ι → Set α) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (domain i ∩ domain j).Nonempty
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [Set.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- The sum of the overlap constants along a walk of the overlap graph. -/
def walkSum {domain : ι → Set α} (offset : ι → ι → ℤ) {i j : ι}
    (walk : (overlapGraph domain).Walk i j) : ℤ :=
  (walk.darts.map fun dart => offset dart.fst dart.snd).sum

/-- A function on the whole carrier is compatible with a partial odometer when their difference is constant on its
domain. -/
def CompatibleWith (f : α → ℤ) (domain : Set α) (odometer : α → ℤ) : Prop :=
  ∃ c : ℤ, ∀ x ∈ domain, f x - odometer x = c

theorem walkSum_nil {domain : ι → Set α} (offset : ι → ι → ℤ) {i : ι} :
    walkSum offset (SimpleGraph.Walk.nil : (overlapGraph domain).Walk i i) = 0 := by
  simp [walkSum, SimpleGraph.Walk.darts_nil]

theorem walkSum_cons {domain : ι → Set α} (offset : ι → ι → ℤ) {u v w : ι}
    (h : (overlapGraph domain).Adj u v) (p : (overlapGraph domain).Walk v w) :
    walkSum offset (SimpleGraph.Walk.cons h p) = offset u v + walkSum offset p := by
  simp [walkSum, SimpleGraph.Walk.darts_cons]

theorem walkSum_append {domain : ι → Set α} (offset : ι → ι → ℤ) {u v w : ι}
    (p : (overlapGraph domain).Walk u v) (q : (overlapGraph domain).Walk v w) :
    walkSum offset (p.append q) = walkSum offset p + walkSum offset q := by
  simp [walkSum, SimpleGraph.Walk.darts_append]

/-- Reversing a walk negates its sum when the offsets are antisymmetric on edges. -/
theorem walkSum_reverse_eq {domain : ι → Set α} {offset : ι → ι → ℤ}
    (hanti : ∀ i j, (overlapGraph domain).Adj i j → offset j i = -offset i j) :
    ∀ {i j : ι} (p : (overlapGraph domain).Walk i j),
      walkSum offset p.reverse = -walkSum offset p := by
  intro i j p
  induction p with
  | nil => simp [walkSum_nil]
  | @cons u v w h p ih =>
    simp only [SimpleGraph.Walk.reverse_cons, walkSum_append, ih, walkSum_cons, walkSum_nil]
    linarith [hanti u v h]

/-- `lemma:pairwise_compatibility`: existence. -/
theorem exists_compatible_iff_walkSum_eq_zero (domain : ι → Set α) (odometer : ι → α → ℤ)
    (offset : ι → ι → ℤ) (hcover : ∀ x, ∃ i, x ∈ domain i)
    (hconnected : (overlapGraph domain).Connected)
    (hoffset : ∀ i j, ∀ x ∈ domain i ∩ domain j, odometer i x - odometer j x = offset i j) :
    (∃ f : α → ℤ, ∀ i, CompatibleWith f (domain i) (odometer i)) ↔
      ∀ (i : ι) (walk : (overlapGraph domain).Walk i i), walkSum offset walk = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    have hf' : ∀ i, ∃ c : ℤ, ∀ x ∈ domain i, f x - odometer i x = c := hf
    choose b hb using hf'
    have hedge : ∀ u v, (overlapGraph domain).Adj u v → offset u v = b v - b u := by
      rintro u v ⟨-, x, hxu, hxv⟩
      have h1 := hoffset u v x ⟨hxu, hxv⟩
      have h2 := hb u x hxu
      have h3 := hb v x hxv
      linarith
    have hpath : ∀ {u v : ι} (p : (overlapGraph domain).Walk u v),
        walkSum offset p = b v - b u := by
      intro u v p
      induction p with
      | nil => simp [walkSum_nil]
      | @cons u' v' w h p ih =>
        rw [walkSum_cons, ih, hedge u' v' h]
        ring
    intro i walk
    rw [hpath walk, sub_self]
  · intro hzero
    obtain ⟨i0⟩ := hconnected.nonempty
    have hanti : ∀ i j, (overlapGraph domain).Adj i j → offset j i = -offset i j := by
      rintro i j ⟨-, x, hxi, hxj⟩
      have h1 := hoffset i j x ⟨hxi, hxj⟩
      have h2 := hoffset j i x ⟨hxj, hxi⟩
      linarith
    have hW : ∀ i : ι, ∃ w : (overlapGraph domain).Walk i0 i, True := by
      intro i
      obtain ⟨w⟩ := hconnected.preconnected i0 i
      exact ⟨w, trivial⟩
    choose W _ using hW
    obtain ⟨B, hB⟩ : ∃ B : ι → ℤ, ∀ i, B i = walkSum offset (W i) :=
      ⟨fun i => walkSum offset (W i), fun i => rfl⟩
    have hpath : ∀ {u v : ι} (p : (overlapGraph domain).Walk u v),
        walkSum offset p = B v - B u := by
      intro u v p
      have h0 := hzero i0 (((W u).append p).append (W v).reverse)
      rw [walkSum_append, walkSum_append, walkSum_reverse_eq hanti] at h0
      rw [hB v, hB u]
      linarith
    choose idx hidx using hcover
    obtain ⟨f, hf⟩ : ∃ f : α → ℤ, ∀ x, f x = odometer (idx x) x + B (idx x) :=
      ⟨fun x => odometer (idx x) x + B (idx x), fun x => rfl⟩
    refine ⟨f, fun i => ?_⟩
    show ∃ c : ℤ, ∀ x ∈ domain i, f x - odometer i x = c
    refine ⟨B i, fun x hx => ?_⟩
    rw [hf x]
    by_cases hij : idx x = i
    · rw [hij]
      ring
    · have hadj : (overlapGraph domain).Adj (idx x) i := ⟨hij, x, hidx x, hx⟩
      have h1 := hoffset (idx x) i x ⟨hidx x, hx⟩
      have h2 := hpath (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      rw [walkSum_cons, walkSum_nil] at h2
      linarith

/-- `lemma:pairwise_compatibility`: uniqueness up to an additive constant. -/
theorem compatible_unique (domain : ι → Set α) (odometer : ι → α → ℤ)
    (hcover : ∀ x, ∃ i, x ∈ domain i) (hconnected : (overlapGraph domain).Connected)
    {f g : α → ℤ} (hf : ∀ i, CompatibleWith f (domain i) (odometer i))
    (hg : ∀ i, CompatibleWith g (domain i) (odometer i)) :
    ∃ c : ℤ, ∀ x, f x = g x + c := by
  have hf' : ∀ i, ∃ c : ℤ, ∀ x ∈ domain i, f x - odometer i x = c := hf
  have hg' : ∀ i, ∃ c : ℤ, ∀ x ∈ domain i, g x - odometer i x = c := hg
  have hlocal : ∀ i, ∀ x ∈ domain i, ∀ y ∈ domain i, f x - g x = f y - g y := by
    intro i x hx y hy
    obtain ⟨cf, hcf⟩ := hf' i
    obtain ⟨cg, hcg⟩ := hg' i
    linarith [hcf x hx, hcf y hy, hcg x hx, hcg y hy]
  have hwalk : ∀ {i j : ι} (p : (overlapGraph domain).Walk i j),
      ∀ x ∈ domain i, ∀ y ∈ domain j, f x - g x = f y - g y := by
    intro i j p
    induction p with
    | nil => exact fun x hx y hy => hlocal _ x hx y hy
    | @cons u v w h p ih =>
      intro x hx y hy
      obtain ⟨-, z, hzu, hzv⟩ := h
      rw [hlocal u x hx z hzu]
      exact ih z hzv y hy
  rcases isEmpty_or_nonempty α with hα | hne
  · exact ⟨0, fun x => (hα.false x).elim⟩
  · obtain ⟨x0⟩ := hne
    obtain ⟨i, hi⟩ := hcover x0
    refine ⟨f x0 - g x0, fun x => ?_⟩
    obtain ⟨j, hj⟩ := hcover x
    obtain ⟨p⟩ := hconnected.preconnected i j
    linarith [hwalk p x0 hi x hj]

end FLatticePaper.Tiles
