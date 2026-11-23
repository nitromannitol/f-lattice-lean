import FLatticePaper.Tiles.SiteStrings

/-! Task 52: the inductive proof of the four-string predicate (3005(b)) for the standard tiles, following the insertion of Q9
(`fixes/Q9.md` 3020-3032), with the cited covers as named hypotheses on the words.

The literal tile of a non-base word is the six-source union `oddChildB`/`evenChildB` of the two registers (`stateAt`), and each
register is the literal tile of a strictly shorter prefix (`regOdd_exists`, `regEven_exists`). The claim `P = H` is proved for
every word by induction on the length, with `H = HSet f` the set `H_X` of Part III section 2
(`ALL_WORD_NATIVE_UPPER_SUPPORT_BY_CHRONOLOGICAL_HAND_INDUCTION.md`), `f` the current fraction of the word. The root registers
`zeroTile`/`oneTile` are never read by a non-base word, so the base case is the literal base tile `oddTile w`/`evenTile w` of the
base words (`IsBase`), which the hypothesis `baseEq` identifies with `H`.

The cited covers enter only through `SourceHyps`, each field naming its source. -/

namespace FLatticePaper.Tiles.SiteInduction

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteStrings

/-! ### The set `H_X` (Part III section 2) -/

/-- The period multiplier `μ`: `2` for the odd type (`num + den` odd), `1` otherwise. -/
def muOf (f : Fraction) : ℤ := if (f.num + f.den) % 2 = 1 then 2 else 1

/-- `T_X = D² + 2 D N − N²`. -/
def tOf (f : Fraction) : ℤ := f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2

/-- The bound `a_X` on a physical site: `min(2N, D − N)` on even sites, `N` on odd sites. -/
def aOf (f : Fraction) (ev : Bool) : ℤ := if ev then min (2 * f.num) (f.den - f.num) else f.num

/-- The bound `l_X` on a physical site: `0` on even sites, `min(D − N, 3N − D)` on odd sites. -/
def lOf (f : Fraction) (ev : Bool) : ℤ := if ev then 0 else min (f.den - f.num) (3 * f.num - f.den)

/-- The coordinate `t_X(x, y) = N x − D y`. -/
def tCo (f : Fraction) (z : ℤ × ℤ) : ℤ := f.num * z.1 - f.den * z.2

/-- The coordinate `s_X(x, y) = (D + N) x + (D − N) y`. -/
def sCo (f : Fraction) (z : ℤ × ℤ) : ℤ := (f.den + f.num) * z.1 + (f.den - f.num) * z.2

/-- Membership in `H_X`: `a − T ≤ t ≤ D + N − a` and `l ≤ s ≤ μ T + 2 N − l`, with `a`, `l` taken at the physical parity of `z`. -/
abbrev InH (f : Fraction) (z : ℤ × ℤ) : Prop :=
  aOf f (decide ((z.1 + z.2) % 2 = 0)) - tOf f ≤ tCo f z ∧
    tCo f z ≤ f.den + f.num - aOf f (decide ((z.1 + z.2) % 2 = 0)) ∧
    lOf f (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo f z ∧
    sCo f z ≤ muOf f * tOf f + 2 * f.num - lOf f (decide ((z.1 + z.2) % 2 = 0))

/-- The set `H_X` of a fraction. -/
def HSet (f : Fraction) : Set (ℤ × ℤ) := {z | InH f z}

/-- The first period `U = μ (d, n)`. -/
def perU (f : Fraction) : ℤ × ℤ := (muOf f * f.den, muOf f * f.num)

/-- The second period `V = (N − D, D + N)`. -/
def perV (f : Fraction) : ℤ × ℤ := (f.num - f.den, f.den + f.num)

/-- Two sites are congruent modulo the lattice `ℤ U + ℤ V`. -/
abbrev PeriodCongr (U V z w : ℤ × ℤ) : Prop :=
  ∃ k l : ℤ, w.1 - z.1 = k * U.1 + l * V.1 ∧ w.2 - z.2 = k * U.2 + l * V.2

theorem PeriodCongr.symm' {U V z w : ℤ × ℤ} (h : PeriodCongr U V z w) : PeriodCongr U V w z := by
  obtain ⟨k, l, h1, h2⟩ := h
  refine ⟨-k, -l, ?_, ?_⟩
  · rw [neg_mul, neg_mul, ← neg_add, ← h1]; omega
  · rw [neg_mul, neg_mul, ← neg_add, ← h2]; omega

/-- A set covers every class modulo the periods `U, V` (the native quotient cover). -/
abbrev QuotientCover (S : Set (ℤ × ℤ)) (U V : ℤ × ℤ) : Prop :=
  ∀ z : ℤ × ℤ, ∃ s ∈ S, PeriodCongr U V s z

/-- The site `z` is the unique site of `H_f` in its class modulo the periods of `f`. -/
abbrev UniqueIn (f : Fraction) (z : ℤ × ℤ) : Prop :=
  InH f z ∧ ∀ w : ℤ × ℤ, InH f w → PeriodCongr (perU f) (perV f) z w → w = z

/-- **The reduction of the insertion**: `P = H` from the enclosure `P ⊆ H`, the quotient cover of `P`, the marked strings
`S ⊆ P`, and the hull band (a site of `H` that is not the unique representative of its class is marked). -/
theorem eq_of_covers {f : Fraction} {P S : Set (ℤ × ℤ)} (hSP : S ⊆ P) (hPH : P ⊆ HSet f)
    (hcov : QuotientCover P (perU f) (perV f))
    (hband : ∀ z ∈ HSet f, ¬ UniqueIn f z → z ∈ S) : P = HSet f := by
  refine Set.Subset.antisymm hPH ?_
  intro z hz
  by_cases hu : UniqueIn f z
  · obtain ⟨s, hsP, hc⟩ := hcov z
    have hsH : s ∈ HSet f := hPH hsP
    have hsz : s = z := hu.2 s hsH (PeriodCongr.symm' hc)
    rw [← hsz]
    exact hsP
  · exact hSP (hband z hz hu)

/-! ### The six-source operators on sets, mirroring `oddChildB` and `evenChildB` -/

/-- The image of a set under the translation by `v`. -/
def shiftS (S : Set (ℤ × ℤ)) (v : ℤ × ℤ) : Set (ℤ × ℤ) := (fun z => z + v) '' S

theorem coe_shift (T : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    ((shift T v : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = shiftS (T : Set (ℤ × ℤ)) v := by
  simp [shift, shiftS, Finset.coe_image]

/-- The odd child on sets, the set form of `oddChildB`. -/
def oddChildS : Bool → Set (ℤ × ℤ) → Set (ℤ × ℤ) → Fraction → Fraction → Set (ℤ × ℤ)
  | true, T1, T2, p, q =>
      shiftS T2 (texV1Odd p) ∪ shiftS T2 (texV1Odd p + texV1Even q) ∪ shiftS T2 (texV2 p) ∪
        shiftS T2 (texV2 p + texV1Even q) ∪ T1 ∪ shiftS T1 (texV1Even q + texV1Even q + texV2 q)
  | false, T1, T2, p, q =>
      T2 ∪ shiftS T2 (texV1Even q) ∪ shiftS T2 (texV1Odd p + texV2 p) ∪
        shiftS T2 (texV1Odd p + texV2 p + texV1Even q) ∪ shiftS T1 (texV1Even q + texV1Even q) ∪ shiftS T1 (texV2 q)

/-- The even child on sets, the set form of `evenChildB`. -/
def evenChildS : Bool → Set (ℤ × ℤ) → Set (ℤ × ℤ) → Fraction → Fraction → Set (ℤ × ℤ)
  | true, T1, T2, p, q =>
      shiftS T2 (texV1Odd p) ∪ shiftS T2 (texV2 p + texV2 p) ∪ T1 ∪ shiftS T1 (texV2 p) ∪
        shiftS T1 (texV1Even q + texV2 q) ∪ shiftS T1 (texV1Even q + texV2 q + texV2 p)
  | false, T1, T2, p, q =>
      T2 ∪ shiftS T2 (texV1Odd p + (texV2 p + texV2 p)) ∪ shiftS T1 (texV1Even q) ∪
        shiftS T1 (texV1Even q + texV2 p) ∪ shiftS T1 (texV2 q) ∪ shiftS T1 (texV2 q + texV2 p)

theorem coe_oddChildB (b : Bool) (T1 T2 : Finset (ℤ × ℤ)) (p q : Fraction) :
    ((oddChildB b T1 T2 p q : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      oddChildS b (T1 : Set (ℤ × ℤ)) (T2 : Set (ℤ × ℤ)) p q := by
  cases b <;> simp [oddChildB, oddChildS, coe_shift, Finset.coe_union] <;>
    (ext z; simp only [Set.mem_union]; tauto)

theorem coe_evenChildB (b : Bool) (T1 T2 : Finset (ℤ × ℤ)) (p q : Fraction) :
    ((evenChildB b T1 T2 p q : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      evenChildS b (T1 : Set (ℤ × ℤ)) (T2 : Set (ℤ × ℤ)) p q := by
  cases b <;> simp [evenChildB, evenChildS, coe_shift, Finset.coe_union] <;>
    (ext z; simp only [Set.mem_union]; tauto)

/-! ### The recursion at a non-base word -/

/-- A non-base word contains a letter other than `3` and a letter other than `2`. -/
theorem not_isBase_gives {w : Word} (h : ¬ IsBase w) :
    (∃ x ∈ w, x ≠ Digit.three) ∧ (∃ x ∈ w, x ≠ Digit.two) := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    apply h
    right; left
    intro d hd
    by_contra hne
    exact hc ⟨d, hd, hne⟩
  · by_contra hc
    apply h
    right; right
    intro d hd
    by_contra hne
    exact hc ⟨d, hd, hne⟩

/-- At a non-base word the child tiles are the six-source operators on the registers of the word. -/
theorem childTiles_nonbase (w : Word) (h : ¬ IsBase w) :
    childTiles w (stateAt w) =
      (oddChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (stateAt w).par.odd (stateAt w).par.even,
        evenChildB (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (stateAt w).par.odd (stateAt w).par.even) := by
  have h1 : ¬ w = [] := fun e => h (Or.inl e)
  have h2 : ¬ w = List.replicate w.length Digit.three := by
    intro e
    apply h
    right; left
    intro d hd
    rw [e] at hd
    exact List.eq_of_mem_replicate hd
  have h3 : ¬ w = List.replicate w.length Digit.two := by
    intro e
    apply h
    right; right
    intro d hd
    rw [e] at hd
    exact List.eq_of_mem_replicate hd
  unfold childTiles
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem oddTile_coe_nonbase (w : Word) (h : ¬ IsBase w) :
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      oddChildS (phase w == 1) ((stateAt w).tOdd : Set (ℤ × ℤ)) ((stateAt w).tEven : Set (ℤ × ℤ))
        (parentsAt w).odd (parentsAt w).even := by
  unfold oddTile
  rw [childTiles_nonbase w h, stateAt_par]
  exact coe_oddChildB _ _ _ _ _

theorem evenTile_coe_nonbase (w : Word) (h : ¬ IsBase w) :
    ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      evenChildS (phase w == 1) ((stateAt w).tOdd : Set (ℤ × ℤ)) ((stateAt w).tEven : Set (ℤ × ℤ))
        (parentsAt w).odd (parentsAt w).even := by
  unfold evenTile
  rw [childTiles_nonbase w h, stateAt_par]
  exact coe_evenChildB _ _ _ _ _

/-! ### The registers are literal tiles of shorter prefixes -/

/-- The odd register of a word containing a letter other than `3` is the odd tile of a shorter prefix `u`, whose odd fraction is
the odd parent of the word. -/
theorem regOdd_exists : ∀ w : Word, (∃ x ∈ w, x ≠ Digit.three) →
    ∃ u : Word, u.length < w.length ∧ (stateAt w).tOdd = oddTile u ∧
      (parentsAt w).odd = (parentsAt u).current .odd := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h; obtain ⟨x, hx, -⟩ := h; simp at hx
  | append_singleton v d ih =>
    intro hw
    cases d with
    | one =>
      exact ⟨v, by simp, tOdd_snoc_one v, by rw [parentsAt_append_singleton]; rfl⟩
    | two =>
      exact ⟨v, by simp, tOdd_snoc_two v, by rw [parentsAt_append_singleton]; rfl⟩
    | three =>
      have hv : ∃ x ∈ v, x ≠ Digit.three := by
        obtain ⟨x, hx, hne⟩ := hw
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, hne⟩
        · rw [List.mem_singleton] at hx
          exact absurd hx hne
      obtain ⟨u, hul, ht, hp⟩ := ih hv
      refine ⟨u, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · rw [tOdd_snoc_three]; exact ht
      · rw [parentsAt_append_singleton]; exact hp

/-- The even register of a word containing a letter other than `2` is the even tile of a shorter prefix `u`, whose even fraction
is the even parent of the word. -/
theorem regEven_exists : ∀ w : Word, (∃ x ∈ w, x ≠ Digit.two) →
    ∃ u : Word, u.length < w.length ∧ (stateAt w).tEven = evenTile u ∧
      (parentsAt w).even = (parentsAt u).current .even := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h; obtain ⟨x, hx, -⟩ := h; simp at hx
  | append_singleton v d ih =>
    intro hw
    cases d with
    | one =>
      exact ⟨v, by simp, tEven_snoc_one v, by rw [parentsAt_append_singleton]; rfl⟩
    | three =>
      exact ⟨v, by simp, tEven_snoc_three v, by rw [parentsAt_append_singleton]; rfl⟩
    | two =>
      have hv : ∃ x ∈ v, x ≠ Digit.two := by
        obtain ⟨x, hx, hne⟩ := hw
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨x, hx, hne⟩
        · rw [List.mem_singleton] at hx
          exact absurd hx hne
      obtain ⟨u, hul, ht, hp⟩ := ih hv
      refine ⟨u, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · rw [tEven_snoc_two]; exact ht
      · rw [parentsAt_append_singleton]; exact hp

/-! ### The marked strings and the cited covers as hypotheses -/

/-- The marked sites of the odd standard tile of `w` (the four strings of the Q9 reading). -/
def marksOdd (w : Word) : Set (ℤ × ℤ) :=
  {z | z ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false)}

/-- The marked sites of the even standard tile of `w`. -/
def marksEven (w : Word) : Set (ℤ × ℤ) :=
  {z | z ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true)}

/-- The current odd and even fractions of a word. -/
abbrev curO (w : Word) : Fraction := (parentsAt w).current .odd
abbrev curE (w : Word) : Fraction := (parentsAt w).current .even

/-- The inner boundary of a set of sites: members with a unit neighbour outside the set. -/
def innerBd (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {z | z ∈ S ∧ ∃ e ∈ unitNeighbours z, e ∉ S}

/-- **The cited covers and the Q9 facts, as named hypotheses.** The word-indexed fields quantify over the words that produce the
parents of the induction, which is the scope the sources state (the actual selected parents of section 3(B)).

* `baseEq`, `baseCov`: the literal base tiles (`IsBase`: the empty word, `3^k`, `2^k`) equal `H_X` of their current fractions, and
  cover every class. Source: `ALL_WORD_NATIVE_UPPER_SUPPORT_BY_CHRONOLOGICAL_HAND_INDUCTION.md` section 3(A) (the four literal
  pure standard initializer families satisfy `H`), and `F_LATTICE_LITERAL_INITIALIZERS_NATIVE_QUOTIENT_COVER_HAND_20261120.md`
  (the native quotient cover of the literal initializers).
* `encOdd`, `encEven`: the six natural standard-source `H` sets of the parents of a non-base word lie in `H` of its child.
  Source: section 3(B) of the same note.
* `propOdd`, `propEven`: an ordinary six-source child of covered parents covers every class of its own deck.
  Source: `ALL_ORDINARY_STANDARD_NATIVE_COVER_PROPAGATES_HAND_THEOREM.md`.
* `hull`, `hullE`: a site of `H` that is not the unique representative of its class is marked (Q9, the hull band).
* `marksIn`: the marked strings lie in the tile. `boundary`: the inner boundary of `H` is covered by the marks (Q9, the strings). -/
structure SourceHyps : Prop where
  baseEq : ∀ w : Word, IsBase w →
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) ∧
      ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w)
  baseCov : ∀ w : Word, IsBase w →
    QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) ∧
      QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w))
  encOdd : ∀ w : Word, ¬ IsBase w →
    oddChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even
      ⊆ HSet (curO w)
  encEven : ∀ w : Word, ¬ IsBase w →
    evenChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even
      ⊆ HSet (curE w)
  propOdd : ∀ w : Word, ¬ IsBase w →
    QuotientCover (HSet (parentsAt w).odd) (perU (parentsAt w).odd) (perV (parentsAt w).odd) →
    QuotientCover (HSet (parentsAt w).even) (perU (parentsAt w).even) (perV (parentsAt w).even) →
    QuotientCover
      (oddChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even)
      (perU (curO w)) (perV (curO w))
  propEven : ∀ w : Word, ¬ IsBase w →
    QuotientCover (HSet (parentsAt w).odd) (perU (parentsAt w).odd) (perV (parentsAt w).odd) →
    QuotientCover (HSet (parentsAt w).even) (perU (parentsAt w).even) (perV (parentsAt w).even) →
    QuotientCover
      (evenChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even)
      (perU (curE w)) (perV (curE w))
  hull : ∀ w : Word, ¬ IsBase w → ∀ z, InH (curO w) z → ¬ UniqueIn (curO w) z → z ∈ marksOdd w
  hullE : ∀ w : Word, ¬ IsBase w → ∀ z, InH (curE w) z → ¬ UniqueIn (curE w) z → z ∈ marksEven w
  marksIn : ∀ w : Word, marksOdd w ⊆ ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) ∧
    marksEven w ⊆ ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))
  boundary : ∀ w : Word, innerBd (HSet (curO w)) ⊆ marksOdd w ∧ innerBd (HSet (curE w)) ⊆ marksEven w

/-- The good statement at a word: both standard tiles equal `H`, and the `H` sets cover every class. -/
abbrev Good (w : Word) : Prop :=
  ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) ∧
    ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) ∧
    QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) ∧
    QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w))

theorem good_base (H : SourceHyps) (w : Word) (hb : IsBase w) : Good w := by
  obtain ⟨h1, h2⟩ := H.baseEq w hb
  obtain ⟨c1, c2⟩ := H.baseCov w hb
  exact ⟨h1, h2, c1, c2⟩

/-- The step at a non-base word, from the registers, which are the tiles of shorter prefixes. -/
theorem good_nonbase (H : SourceHyps) (w : Word) (hb : ¬ IsBase w)
    (IH : ∀ u : Word, u.length < w.length → Good u) : Good w := by
  obtain ⟨hno3, hno2⟩ := not_isBase_gives hb
  obtain ⟨u1, hu1l, hu1t, hu1p⟩ := regOdd_exists w hno3
  obtain ⟨u2, hu2l, hu2t, hu2p⟩ := regEven_exists w hno2
  obtain ⟨g1o, -, c1o, -⟩ := IH u1 hu1l
  obtain ⟨-, g2e, -, c2e⟩ := IH u2 hu2l
  have hTo : ((stateAt w).tOdd : Set (ℤ × ℤ)) = HSet (parentsAt w).odd := by
    rw [hu1t, hu1p]; exact g1o
  have hTe : ((stateAt w).tEven : Set (ℤ × ℤ)) = HSet (parentsAt w).even := by
    rw [hu2t, hu2p]; exact g2e
  have hcovP : QuotientCover (HSet (parentsAt w).odd) (perU (parentsAt w).odd) (perV (parentsAt w).odd) := by
    rw [hu1p]; exact c1o
  have hcovQ : QuotientCover (HSet (parentsAt w).even) (perU (parentsAt w).even) (perV (parentsAt w).even) := by
    rw [hu2p]; exact c2e
  -- the odd child
  have hPo : ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      oddChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even := by
    rw [oddTile_coe_nonbase w hb, hTo, hTe]
  have hcovO : QuotientCover ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) (perU (curO w)) (perV (curO w)) := by
    rw [hPo]; exact H.propOdd w hb hcovP hcovQ
  have hodd : ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) := by
    refine eq_of_covers (H.marksIn w).1 ?_ hcovO (fun z hz hu => H.hull w hb z hz hu)
    rw [hPo]; exact H.encOdd w hb
  -- the even child
  have hPe : ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) =
      evenChildS (phase w == 1) (HSet (parentsAt w).odd) (HSet (parentsAt w).even) (parentsAt w).odd (parentsAt w).even := by
    rw [evenTile_coe_nonbase w hb, hTo, hTe]
  have hcovE : QuotientCover ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) (perU (curE w)) (perV (curE w)) := by
    rw [hPe]; exact H.propEven w hb hcovP hcovQ
  have heven : ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) := by
    refine eq_of_covers (H.marksIn w).2 ?_ hcovE (fun z hz hu => H.hullE w hb z hz hu)
    rw [hPe]; exact H.encEven w hb
  have hcovOf : QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) := by
    rw [← hodd]; exact hcovO
  have hcovEf : QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w)) := by
    rw [← heven]; exact hcovE
  exact ⟨hodd, heven, hcovOf, hcovEf⟩

theorem good_le (H : SourceHyps) : ∀ n : ℕ, ∀ w : Word, w.length ≤ n → Good w := by
  intro n
  induction n with
  | zero =>
    intro w hw
    exact good_base H w (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ n ih =>
    intro w hw
    by_cases hb : IsBase w
    · exact good_base H w hb
    · exact good_nonbase H w hb (fun u hu => ih u (by omega))

/-- **The induction**: every standard tile equals `H` and the `H` sets cover every class. -/
theorem good_all (H : SourceHyps) (w : Word) : Good w :=
  good_le H w.length w le_rfl

/-! ### The four-string predicate for every standard tile -/

theorem fourStrings_odd (H : SourceHyps) (w : Word) :
    FourStrings (oddTile w) (hWordOf w false) (vWordOf w false) := by
  obtain ⟨hO, -, -, -⟩ := good_all H w
  refine ⟨fun z hz => ?_, fun z hz hb => ?_⟩
  · exact Finset.mem_coe.mp ((H.marksIn w).1 hz)
  · have hzS : z ∈ HSet (curO w) := by
      rw [← hO]; exact Finset.mem_coe.mpr hz
    have hnb : ∃ e ∈ unitNeighbours z, e ∉ HSet (curO w) := by
      obtain ⟨e, he, hne⟩ := hb.2
      exact ⟨e, he, by rw [← hO]; exact fun h => hne (Finset.mem_coe.mp h)⟩
    exact (H.boundary w).1 ⟨hzS, hnb⟩

theorem fourStrings_even (H : SourceHyps) (w : Word) :
    FourStrings (evenTile w) (hWordOf w true) (vWordOf w true) := by
  obtain ⟨-, hE, -, -⟩ := good_all H w
  refine ⟨fun z hz => ?_, fun z hz hb => ?_⟩
  · exact Finset.mem_coe.mp ((H.marksIn w).2 hz)
  · have hzS : z ∈ HSet (curE w) := by
      rw [← hE]; exact Finset.mem_coe.mpr hz
    have hnb : ∃ e ∈ unitNeighbours z, e ∉ HSet (curE w) := by
      obtain ⟨e, he, hne⟩ := hb.2
      exact ⟨e, he, by rw [← hE]; exact fun h => hne (Finset.mem_coe.mp h)⟩
    exact (H.boundary w).2 ⟨hzS, hnb⟩

/-- **Clause (b), the four-string predicate of every standard tile**, from the named hypotheses. -/
theorem standard_fourStrings (H : SourceHyps) (w : Word) (par : Bool) : StandardFourStrings w par := by
  cases par
  · exact fourStrings_odd H w
  · exact fourStrings_even H w

end FLatticePaper.Tiles.SiteInduction
