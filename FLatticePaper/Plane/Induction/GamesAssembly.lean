import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.FreeChain
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.StrongCore

/-! # The games with a deck rank from the Q1 rank (fixes/Q1.md)

Q1 builds the rank of the auxiliary game `permitsQ1` (black: both inputs; free white: the prescribed input; other white: either
input) by the Bellman construction, given that the game has no restricted fort. This file assembles the games of a word from it.

* `permitsQ1_rank_deck`: the Bellman rank `R = m K + r` (`K = P + J_η`, `r` deck-periodic) has the deck increments
  `(−m, m η)` on the kernel and the transverse vector.
* `freePolicy_strict_of_Q1`: the rank strictly decreases along every edge of the rank-independent policy `freePolicy`. At a black
  site both inputs decrease, at a free white the only permitted input is the prescribed one, and at a nonfree white the selection of a
  decreasing permitted input satisfies every square clause (`squares_gen_sel`), so unit propagation makes the W1-forced input the
  selected one (`forced_sound`): "Unit propagation is sound for all satisfying assignments, so every W1-forced white selects its forced
  edge."
* `gamesWithRank_of_free`: the canonical signed games of the free policy (`canonicalSigned_of_free`, `FreeChain.chain_free`, the deck
  equivariance `freePolicy_add_span`) with the ranks of the two signs give `GamesWithRank`. -/

namespace FLatticePaper.GamesAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.FreeClosure FLatticePaper.SquareClauses
  FLatticePaper.AuxRankQ1

/-- **The Q1 rank with its deck increments.** -/
theorem permitsQ1_rank_deck (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (hno : RestrictedNoFort F (fun z => frame.price F z + frame.roundedSlip F η z) (permitsQ1 frame F η)) :
    ∃ (R : Site → ℤ) (m : ℤ),
      (∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + m * -1) ∧
      (∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + m * η) ∧
      IsConstrainedBurningRank F R (permitsQ1 frame F η) := by
  have hpos : 0 < frame.child.modifiedDeck.det := by
    obtain ⟨hn1, hnd, -, -, -⟩ := frame.child_facts
    have e : frame.child.modifiedDeck.det = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
        - frame.child.num * frame.child.num := by
      unfold PeriodDeck.det
      rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
      simp only
      ring
    rw [e]
    nlinarith
  obtain ⟨scale, remainder, budget, -, -, hper, hR⟩ :=
    FLatticePaper.exists_constrainedBurningRank_of_restrictedNoFort (deck := frame.child.modifiedDeck)
      (sites := frame.child.modifiedDeck.residueSquare)
      ((PeriodDeck.covers_iff_square_codes_subset frame.child.modifiedDeck hpos _).mpr (subset_refl _))
      (fun step hstep => span_even frame hstep)
      (fun step hstep site => by
        obtain ⟨i, j, rfl⟩ := hstep
        exact frame.laplacian_add_lattice hP i j site)
      (grade_hgrade frame F η hPD hSD)
      (fun step hstep site input => permitsQ1_shift frame F η
        (fun c i j => frame.laplacian_add_lattice hP i j c) step hstep site input)
      (permitsQ1_permitLocal frame F hη) hP.binary hno
  have eU : frame.child.modifiedDeck.combine 1 0 = frame.child.modifiedDeck.kernel := by
    rw [FLatticePaper.DeckSelection.combine_eq frame 1 0]
    simp
  have eV : frame.child.modifiedDeck.combine 0 1 = frame.child.modifiedDeck.transverse := by
    rw [FLatticePaper.DeckSelection.combine_eq frame 0 1]
    simp
  refine ⟨fun site => scale * (frame.price F site + frame.roundedSlip F η site) + remainder site, scale, ?_, ?_, hR⟩
  · intro z
    have hk := grade_drift_combine frame F η hPD hSD 1 0 z
    have hr := hper (frame.child.modifiedDeck.combine 1 0) ⟨1, 0, rfl⟩ z
    rw [eU] at hk hr
    simp only
    rw [hk.1, hk.2, hr]
    ring
  · intro z
    have hk := grade_drift_combine frame F η hPD hSD 0 1 z
    have hr := hper (frame.child.modifiedDeck.combine 0 1) ⟨0, 1, rfl⟩ z
    rw [eV] at hk hr
    simp only
    rw [hk.1, hk.2, hr]
    ring

/-- **The Q1 rank is strict along the free policy.** -/
theorem freePolicy_strict_of_Q1 (frame : ChildFrame) {F : Field} {η : ℤ}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) (hex : ForcedExists frame F)
    {R : Site → ℤ} (hR : IsConstrainedBurningRank F R (permitsQ1 frame F η)) :
    ∀ c i, freePolicy frame F η c i → R i < R c := by
  classical
  have hR' : ∀ c, (laplacian F c = -1 ∧
        (permitsQ1 frame F η c (incomingNeg c) ∧ R (incomingNeg c) < R c) ∧
        (permitsQ1 frame F η c (incomingPos c) ∧ R (incomingPos c) < R c)) ∨
      (laplacian F c = 0 ∧
        ((permitsQ1 frame F η c (incomingNeg c) ∧ R (incomingNeg c) < R c) ∨
          (permitsQ1 frame F η c (incomingPos c) ∧ R (incomingPos c) < R c))) := fun c => hR c
  let sel : Site → Site := fun c =>
    if permitsQ1 frame F η c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c
  have hwh : ∀ c, laplacian F c = 0 → permitsQ1 frame F η c (sel c) ∧ R (sel c) < R c := by
    intro c hc
    by_cases hn : permitsQ1 frame F η c (incomingNeg c) ∧ R (incomingNeg c) < R c
    · simp only [sel, if_pos hn]
      exact hn
    · simp only [sel, if_neg hn]
      rcases hR' c with ⟨hb, -, -⟩ | ⟨-, hn' | hp⟩
      · rw [hc] at hb
        norm_num at hb
      · exact absurd hn' hn
      · exact hp
  have hbk : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → R i < R c := by
    intro c i hc hi
    rcases hR' c with ⟨-, hn, hp⟩ | ⟨hw, -⟩
    · rcases hi with rfl | rfl
      · exact hn.2
      · exact hp.2
    · rw [hc] at hw
      norm_num at hw
  have hsq := squares_gen_sel F sel R hbin hbk (fun c hc => (hwh c hc).2)
  have hsi : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c := by
    intro c _
    by_cases hn : permitsQ1 frame F η c (incomingNeg c) ∧ R (incomingNeg c) < R c
    · left
      simp only [sel, if_pos hn]
    · right
      simp only [sel, if_neg hn]
  intro c i hci
  unfold freePolicy at hci
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · exact hbk c i hl hE
  · obtain ⟨hpq, hlt⟩ := hwh c hl
    unfold permitsQ1 at hpq
    rcases hpq with ⟨hb, -⟩ | ⟨-, ⟨-, hps⟩ | ⟨hncl, -⟩⟩
    · rw [hl] at hb
      norm_num at hb
    · rw [freePresc_single frame η hp hps]
      exact hlt
    · exact absurd hcl hncl
  · have hf := forcedSel_spec (hex c hn hl)
    have he := forced_sound F (fun _ _ => False) sel hsi (fun _ _ h => False.elim h) hsq c _ hf
    rw [hs, ← he]
    exact (hwh c hl).2

/-- **`GamesWithRank` from the free policy**: the named inputs of the free policy of both signs, with ranks that have deck
increments, give the canonical signed games and their ranks. -/
theorem gamesWithRank_of_free {w : Word}
    (hpk : (frameAt w).Packet (standardField w))
    (hc : 3 ≤ (frameAt w).child.den - (frameAt w).child.num) (hU : HasUnitPrice (frameAt w) (standardField w))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt w).child.num (frameAt w).child.den (standardField w))
    (R : ℤ → Site → ℤ) (aU aV : ℤ → ℤ)
    (hRU : ∀ η, (η = 1 ∨ η = -1) → ∀ z, R η (z + (frameAt w).child.modifiedDeck.kernel) = R η z + aU η)
    (hRV : ∀ η, (η = 1 ∨ η = -1) → ∀ z, R η (z + (frameAt w).child.modifiedDeck.transverse) = R η z + aV η)
    (N : ∀ η, (η = 1 ∨ η = -1) → FreeNamedInputs (frameAt w) (standardField w) η (R η)) :
    GamesWithRank w := by
  have hex := forcedExists_of (frameAt w) hpk hW1
  let G : CanonicalSignedGames (frameAt w) (standardField w) :=
    { game := fun η hη => canonicalSigned_of_free (frameAt w) hpk hex hη (N η hη)
      chainNonincreasing := fun η hη =>
        FreeChain.chain_free (frameAt w) hpk.periods hpk hη hc hU hW1 (N η hη) (N (-η) (neg_unit hη))
      deckEquiv := fun η hη i j x u =>
        (freePolicy_add_span (frameAt w) hpk hex hη (squares_of_strict (frameAt w) hpk (N η hη).strictRank)
          ⟨i, j, rfl⟩ x u).symm }
  exact ⟨G, fun η hη => ⟨R η, aU η, aV η, hRU η hη, hRV η hη, fun x i h => (N η hη).strictRank x i h⟩⟩

/-- **The games of a word from the Q1 game.** At a proper word that is not a two-power, with the core of its strong estimates and its
W1 forcing: if the Q1 game of each sign has no restricted fort (`hno`), and every strict rank of the free policy that is a burning rank
of the Q1 game completes to the named inputs of the free policy (`hN`: the permits, the monotonicity of `P` and `J`, the exceptional
west input), then the word has games with a deck rank. -/
theorem gamesWithRank_of_Q1 {word : Word} (h2 : ∃ x ∈ word, x ≠ Digit.two)
    (hcore : StrongCore word)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hno : ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RestrictedNoFort (standardField word)
        (fun z => (frameAt word).price (standardField word) z + (frameAt word).roundedSlip (standardField word) η z)
        (permitsQ1 (frameAt word) (standardField word) η))
    (hN : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ R : Site → ℤ,
      IsConstrainedBurningRank (standardField word) R (permitsQ1 (frameAt word) (standardField word) η) →
      (∀ c i, freePolicy (frameAt word) (standardField word) η c i → R i < R c) →
      FreeNamedInputs (frameAt word) (standardField word) η R) :
    GamesWithRank word := by
  have hpk := hcore.packet
  have hex := forcedExists_of (frameAt word) hpk hW1
  have hc : 3 ≤ (frameAt word).child.den - (frameAt word).child.num := by
    have hd4 : 4 ≤ (frameAt word).child.den - (frameAt word).child.num :=
      FLatticePaper.Farey.current_even_diff_ge_four word h2
    omega
  have hPD : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
        (frameAt word).price (standardField word) z + -1 ∧
      (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
        (frameAt word).price (standardField word) z + 0 :=
    fun z => ⟨by linarith [(hcore.priceDrift z).1], by linarith [(hcore.priceDrift z).2]⟩
  have hSD : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z,
      (frameAt word).slip (standardField word) η (z + (frameAt word).child.modifiedDeck.kernel) =
          (frameAt word).slip (standardField word) η z + 0 ∧
        (frameAt word).slip (standardField word) η (z + (frameAt word).child.modifiedDeck.transverse) =
          (frameAt word).slip (standardField word) η z + 2 * η :=
    fun η hη z => ⟨by linarith [(hcore.slipDrift η hη z).1], by linarith [(hcore.slipDrift η hη z).2]⟩
  have hrank : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (R : Site → ℤ) (m : ℤ),
      (∀ z, R (z + (frameAt word).child.modifiedDeck.kernel) = R z + m * -1) ∧
      (∀ z, R (z + (frameAt word).child.modifiedDeck.transverse) = R z + m * η) ∧
      IsConstrainedBurningRank (standardField word) R (permitsQ1 (frameAt word) (standardField word) η) :=
    fun η hη => permitsQ1_rank_deck (frameAt word) (standardField word) hpk η hη hPD (hSD η hη) (hno η hη)
  classical
  let R : ℤ → Site → ℤ := fun η => if hη : η = 1 ∨ η = -1 then Classical.choose (hrank η hη) else fun _ => 0
  let m : ℤ → ℤ := fun η => if hη : η = 1 ∨ η = -1 then Classical.choose (Classical.choose_spec (hrank η hη)) else 0
  have hspec : ∀ η (hη : η = 1 ∨ η = -1),
      (∀ z, R η (z + (frameAt word).child.modifiedDeck.kernel) = R η z + m η * -1) ∧
      (∀ z, R η (z + (frameAt word).child.modifiedDeck.transverse) = R η z + m η * η) ∧
      IsConstrainedBurningRank (standardField word) (R η) (permitsQ1 (frameAt word) (standardField word) η) := by
    intro η hη
    simp only [R, m, dif_pos hη]
    exact Classical.choose_spec (Classical.choose_spec (hrank η hη))
  have hstrict : ∀ η (hη : η = 1 ∨ η = -1), ∀ c i,
      freePolicy (frameAt word) (standardField word) η c i → R η i < R η c :=
    fun η hη => freePolicy_strict_of_Q1 (frameAt word) hpk.binary hex (hspec η hη).2.2
  exact gamesWithRank_of_free hpk hc hcore.F1_unitPrice hW1 R (fun η => m η * -1) (fun η => m η * η)
    (fun η hη => (hspec η hη).1) (fun η hη => (hspec η hη).2.1)
    (fun η hη => hN η hη (R η) (hspec η hη).2.2 (hstrict η hη))

end FLatticePaper.GamesAssembly
