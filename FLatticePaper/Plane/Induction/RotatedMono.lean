import FLatticePaper.Plane.Induction.RotatedCap
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.SheetMonoChild

/-! # The rotated monotonicity (Q26, long V): proved from the frame's price, not named

With `h = G − h0` (the standard field minus the harmonic grid) and `f = quarterTurnField G = h ∘ Z` (`Z(x,y) = (−y, x−1)`):
* `h` is transverse-periodic (`h_transverse`), so `f` is periodic under the residual kernel `2(D,N)` (`quarterTurnField_kernel`).
* The price identity `h(w) − h(w − v) = P(w) − c0` (`harmonicGrid_shift_price`) and the price bound `P ≤ c0` for `s(w) ≥ L`
  (`price_le_cutPrice_of_sGrade`, from the closed polygon, the drifts and `closedPolygon_covers`) give `h(w) ≤ h(w − v)` for `s(w) ≥ L`.
* The reflection `z ↦ I − z` (`packet_reflection_I`, `harmonicGrid_I_sub`) turns this into `h(z) ≤ h(z + v)` for `s(z) ≤ −C`,
  i.e. `f(y) ≤ f(y + δ)` for `t'(y) ≤ 0`, with `δ = (v2, −v1)` of residual grade `1` (`sGrade_parentShift`).
* Same-level points of the same parity differ by a residual kernel multiple (`lattice_of_t_zero`), so the unit steps give
  `f(u) ≤ f(v)` for `t'(u) ≤ t'(v) ≤ 0` (`rotated_mono`). -/

namespace FLatticePaper.RotatedMono

open FLatticePaper FLatticePaper.Induction FLatticePaper.RotatedCap

variable {fr : ChildFrame} {G : Field}

/-- `h = G − h0` is invariant under the transverse vector: the packet's transverse law and the harmonic grid's increment have the same
affine correction `t(z) + coherentConstantV`. -/
theorem h_transverse (hP : fr.Packet G) (z : Site) :
    G (z + fr.child.modifiedDeck.transverse) - harmonicGrid (z + fr.child.modifiedDeck.transverse)
      = G z - harmonicGrid z := by
  have hV := hP.periods.2 z
  have h0V := fr.harmonicGrid_add_transverse z
  have htg : FLatticePaper.Farey.Fraction.transverseGrade fr.child z = -fr.tGrade z := by
    unfold FLatticePaper.Farey.Fraction.transverseGrade ChildFrame.tGrade
    ring
  rw [htg] at hV
  rw [hV, h0V]
  ring

/-- Integer multiples of the transverse vector leave `h` invariant. -/
theorem h_transverse_zsmul (hP : fr.Packet G) (k : ℤ) (z : Site) :
    G (z + k • fr.child.modifiedDeck.transverse) - harmonicGrid (z + k • fr.child.modifiedDeck.transverse)
      = G z - harmonicGrid z := by
  have hper : Function.Periodic (fun w => G w - harmonicGrid w) fr.child.modifiedDeck.transverse :=
    fun w => h_transverse hP w
  exact hper.zsmul k z

/-- The residual is the standard field minus the harmonic grid at `Z y`: `f = h ∘ Z`. -/
theorem quarterTurnField_eq_h (G : Field) (y : Site) :
    quarterTurnField G y = G (Zs y) - harmonicGrid (Zs y) := by
  have h := FLatticePaper.Induction.harmonicGrid_quarterTurn y
  rw [mapSite_eq_Zs] at h
  unfold quarterTurnField
  rw [mapSite_eq_Zs]
  linarith

/-- The residual is invariant under `2(D,N)` (the residual kernel, which `Z` sends to the transverse vector). -/
theorem quarterTurnField_kernel (hP : fr.Packet G) (N D : ℤ)
    (hN : fr.child.den - fr.child.num = 2 * N) (hD : fr.child.den + fr.child.num = 2 * D) (k : ℤ) (y : Site) :
    quarterTurnField G (y + (2 * D * k, 2 * N * k)) = quarterTurnField G y := by
  have hV : fr.child.modifiedDeck.transverse = (-(2 * N), 2 * D) := by
    rw [FLatticePaper.Induction.ChildFrame.modTransverse_eq]
    ext <;> simp <;> linarith
  rw [quarterTurnField_eq_h, quarterTurnField_eq_h]
  have e : Zs (y + (2 * D * k, 2 * N * k)) = Zs y + k • fr.child.modifiedDeck.transverse := by
    rw [hV]
    unfold Zs
    ext <;> simp <;> ring
  rw [e, h_transverse_zsmul hP k (Zs y)]

/-- Points of one level and parity of the residual differ by a multiple of `2(D,N)`. -/
theorem lattice_of_t_zero (N D : ℤ) (hcop : IsCoprime N D) (hDN : (D + N) % 2 = 1) (hD0 : D ≠ 0) (d : Site)
    (ht : N * d.1 - D * d.2 = 0) (he : (d.1 + d.2) % 2 = 0) : ∃ k : ℤ, d = (2 * D * k, 2 * N * k) := by
  have hdvd : D ∣ d.1 := by
    have h1 : D ∣ N * d.1 := ⟨d.2, by linarith⟩
    exact (hcop.symm).dvd_of_dvd_mul_left h1
  obtain ⟨m, hm⟩ := hdvd
  have hd2 : d.2 = N * m := by
    have h2 : D * d.2 = D * (N * m) := by
      have : N * (D * m) = D * d.2 := by rw [← hm]; linarith
      linarith [this, show N * (D * m) = D * (N * m) by ring]
    exact mul_left_cancel₀ hD0 h2
  have hsum : m * (D + N) = d.1 + d.2 := by rw [hm, hd2]; ring
  have hEven : Even (m * (D + N)) := by
    rw [Int.even_iff, hsum]
    exact he
  rcases Int.even_mul.mp hEven with hme | hdn
  · obtain ⟨k, hk⟩ := hme
    refine ⟨k, Prod.ext ?_ ?_⟩
    · simp only [hm, hk]; ring
    · simp only [hd2, hk]; ring
  · exfalso
    rw [Int.even_iff] at hdn
    omega

/-- The child's sGrade is at most `T + L − 2` on the closed polygon. -/
theorem sGrade_polygon_le (fr : ChildFrame) {y : Site} (hy : y ∈ fr.closedPolygon) :
    fr.sGrade y ≤ fr.child.periodDenominator + fr.child.den + fr.child.num - 2 := by
  obtain ⟨hn1, hnd, hdn, hd3, hT⟩ := fr.child_facts
  rcases (fr.mem_closedPolygon_iff y).mp hy with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
  · linarith
  · linarith

/-- The grade of the kernel is the period, and of the transverse vector is zero. -/
theorem sGrade_kernel (fr : ChildFrame) :
    fr.sGrade fr.child.modifiedDeck.kernel = fr.child.periodDenominator := by
  obtain ⟨-, -, -, -, hT⟩ := fr.child_facts
  have hk : fr.child.modifiedDeck.kernel = (fr.child.den, fr.child.num) := by
    unfold FLatticePaper.Farey.Fraction.modifiedDeck
    simp only [FLatticePaper.SheetMonoChild.periodMult_one fr, one_mul]
  rw [hk, hT]
  unfold ChildFrame.sGrade
  ring

theorem sGrade_transverse (fr : ChildFrame) : fr.sGrade fr.child.modifiedDeck.transverse = 0 := by
  rw [FLatticePaper.Induction.ChildFrame.modTransverse_eq]
  unfold ChildFrame.sGrade
  ring

/-- **The price is at most its cut value above the sGrade `L`.** The closed polygon covers the plane by its deck translates; the
price drops by one along the kernel and is invariant along the transverse vector (the drifts of the strong estimates), and
`s` increases along the kernel by the period, so a covering with a negative kernel index has `s < L`. -/
theorem price_le_cutPrice_of_sGrade (fr : ChildFrame) {G : Field}
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (z : Site) (hz : fr.child.den + fr.child.num ≤ fr.sGrade z) : fr.price G z ≤ fr.cutPrice := by
  obtain ⟨y, hy, i, j, hzy⟩ := fr.closedPolygon_covers z
  obtain ⟨hn1, hnd, hdn, hd3, hT⟩ := fr.child_facts
  set K := fr.child.modifiedDeck.kernel with hKdef
  set V := fr.child.modifiedDeck.transverse with hVdef
  have hU : ∀ (n : ℤ) (w : Site), fr.price G (w + n • K) = fr.price G w - n := by
    intro n
    induction n using Int.induction_on with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      have e : w + ((k : ℤ) + 1) • K = (w + (k : ℤ) • K) + K := by
        rw [add_smul, one_smul]; abel
      rw [e, hdrU, ih]
      ring
    | pred k ih =>
      intro w
      have e : w + (-(k : ℤ) - 1) • K + K = w + (-(k : ℤ)) • K := by
        rw [sub_smul, one_smul, neg_smul]; abel
      have h1 := hdrU (w + (-(k : ℤ) - 1) • K)
      rw [e, ih] at h1
      linarith
  have hVper : Function.Periodic (fun w => fr.price G w) V := fun w => hdrV w
  have hzeq : z = (y + j • V) + i • K := by
    rw [hzy]
    unfold FLatticePaper.Farey.PeriodDeck.combine
    ext <;> simp <;> ring
  have hpz : fr.price G z = fr.price G y - i := by
    have hpj : fr.price G (y + j • V) = fr.price G y := hVper.zsmul j y
    rw [hzeq, hU, hpj]
  have hsz : fr.sGrade z = fr.sGrade y + i * fr.child.periodDenominator := by
    have hsK := sGrade_kernel fr
    have hsV := sGrade_transverse fr
    have hadd : ∀ a b : Site, fr.sGrade (a + b) = fr.sGrade a + fr.sGrade b := by
      intro a b; unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring
    have hsmul : ∀ (n : ℤ) (a : Site), fr.sGrade (n • a) = n * fr.sGrade a := by
      intro n a; unfold ChildFrame.sGrade; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hzeq, hadd, hadd, hsmul, hsmul, hsK, hsV]
    ring
  have hyle := sGrade_polygon_le fr hy
  have hPT : 0 < fr.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hi : 0 ≤ i := by
    by_contra hneg
    have hi1 : i ≤ -1 := by omega
    have h2 : i * fr.child.periodDenominator ≤ -fr.child.periodDenominator := by
      nlinarith
    linarith
  have hprY := (hprice y hy).2
  rw [hpz]
  have : (0 : ℤ) ≤ i := hi
  linarith

/-- **The reflected price step.** For `s(z) ≤ −(d − n)`, the reflection `I − z` has `s ≥ L`, where the price is at most its cut value,
so `h(z) ≤ h(z + v)`. -/
theorem h_le_shift {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (z : Site) (hz : fr.sGrade z ≤ -(fr.child.den - fr.child.num)) :
    G z - harmonicGrid z ≤ G (z + fr.parentShift) - harmonicGrid (z + fr.parentShift) := by
  have hsw : fr.sGrade ((1, -1) - z) = 2 * fr.child.num - fr.sGrade z := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hw : fr.child.den + fr.child.num ≤ fr.sGrade ((1, -1) - z) := by
    rw [hsw]
    linarith
  have hpw := price_le_cutPrice_of_sGrade fr hprice hdrU hdrV ((1, -1) - z) hw
  have hsh := FLatticePaper.W1Lower.harmonicGrid_shift_price fr ((1, -1) - z)
  have hpdef : fr.price G ((1, -1) - z) = G ((1, -1) - z) - G (((1, -1) - z) - fr.parentShift)
      - fr.eps * (fr.parents.odd.num * ((1, -1) - z).1 - fr.parents.odd.den * ((1, -1) - z).2) := rfl
  have e : ((1, -1) - z) - fr.parentShift = (1, -1) - (z + fr.parentShift) := by
    ext <;> simp <;> ring
  have hR1 := FLatticePaper.Induction.packet_reflection_I fr hP z
  have hR2 := FLatticePaper.Induction.packet_reflection_I fr hP (z + fr.parentShift)
  have hH1 := FLatticePaper.Induction.harmonicGrid_I_sub z
  have hH2 := FLatticePaper.Induction.harmonicGrid_I_sub (z + fr.parentShift)
  rw [e] at hpdef hsh
  rw [hR1, hR2] at hpdef
  rw [hH1, hH2] at hsh
  linarith

/-- **The residual unit step.** For a residual site `y` with `t'(y) ≤ 0`, the residual increases along `δ = (v₂, −v₁)`. -/
theorem residual_step {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN : fr.child.den - fr.child.num = 2 * N) (hD : fr.child.den + fr.child.num = 2 * D)
    (y : Site) (hy : N * y.1 - D * y.2 ≤ 0) :
    quarterTurnField G y ≤ quarterTurnField G (y + (fr.parentShift.2, -fr.parentShift.1)) := by
  rw [quarterTurnField_eq_h, quarterTurnField_eq_h]
  have hZ : Zs (y + (fr.parentShift.2, -fr.parentShift.1)) = Zs y + fr.parentShift := by
    unfold Zs
    ext <;> simp <;> ring
  rw [hZ]
  apply h_le_shift hP hprice hdrU hdrV
  have hs : fr.sGrade (Zs y) = 2 * (N * y.1 - D * y.2) - 2 * N := by
    unfold ChildFrame.sGrade Zs
    simp only []
    rw [hD, hN]
    ring
  rw [hs, hN]
  linarith

/-- The residual pair `(N, D)` is coprime, since `D − N = n` and `D + N = d` are coprime. -/
theorem coprime_residual (fr : ChildFrame) (N D : ℤ) (hN : fr.child.den - fr.child.num = 2 * N)
    (hD : fr.child.den + fr.child.num = 2 * D) : IsCoprime N D := by
  obtain ⟨a, b, hab⟩ := fr.child_reduced
  have hnum : fr.child.num = D - N := by linarith
  have hden : fr.child.den = D + N := by linarith
  rw [hnum, hden] at hab
  exact ⟨b - a, a + b, by linear_combination hab⟩

/-- **The rotated monotonicity.** For residual sites of the same parity with `t'(u) ≤ t'(w) ≤ 0`, the residual satisfies
`f(u) ≤ f(w)`: the unit steps along `δ` (`residual_step`) and the kernel periodicity (`quarterTurnField_kernel`,
`lattice_of_t_zero`) reduce it to a single level. -/
theorem rotated_mono_core {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN : fr.child.den - fr.child.num = 2 * N) (hD : fr.child.den + fr.child.num = 2 * D)
    (hpos : 0 < N) (hND : N < D) (u w : Site) (hpar : (u.1 + u.2) % 2 = (w.1 + w.2) % 2)
    (hu : N * u.1 - D * u.2 ≤ N * w.1 - D * w.2) (hw : N * w.1 - D * w.2 ≤ 0) :
    quarterTurnField G u ≤ quarterTurnField G w := by
  have hcop := coprime_residual fr N D hN hD
  have hden : (fr.child.den) % 2 = 1 := by
    have hev : (fr.child.num + fr.child.den) % 2 = 0 := fr.child_even
    have hnum := FLatticePaper.FanInputs.num_odd fr
    omega
  have hDN : (D + N) % 2 = 1 := by
    have : fr.child.den = D + N := by linarith
    omega
  have hD0 : D ≠ 0 := by omega
  obtain ⟨δ, hδ⟩ : ∃ δ : Site, δ = (fr.parentShift.2, -fr.parentShift.1) := ⟨_, rfl⟩
  have hsh2 : (fr.parentShift.1 + fr.parentShift.2) % 2 = 0 := by
    have := FLatticePaper.W1Lower.evenSite_parentShift fr
    unfold EvenSite at this
    exact this
  have hsGr := FLatticePaper.PriceDeck.sGrade_parentShift fr
  have hsv : D * fr.parentShift.1 + N * fr.parentShift.2 = 1 := by
    unfold ChildFrame.sGrade at hsGr
    rw [hD, hN] at hsGr
    linarith
  have hδt : N * δ.1 - D * δ.2 = 1 := by
    rw [hδ]
    show N * fr.parentShift.2 - D * (-fr.parentShift.1) = 1
    linarith
  have hδpar : (δ.1 + δ.2) % 2 = 0 := by
    rw [hδ]
    show (fr.parentShift.2 + -fr.parentShift.1) % 2 = 0
    omega
  have step : ∀ y : Site, N * y.1 - D * y.2 ≤ 0 → quarterTurnField G y ≤ quarterTurnField G (y + δ) := by
    intro y hy
    rw [hδ]
    exact residual_step hP hprice hdrU hdrV N D hN hD y hy
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = (N * w.1 - D * w.2) - (N * u.1 - D * u.2) :=
    ⟨((N * w.1 - D * w.2) - (N * u.1 - D * u.2)).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have tlev : ∀ j : ℕ, N * (u + (j : ℤ) • δ).1 - D * (u + (j : ℤ) • δ).2 = (N * u.1 - D * u.2) + (j : ℤ) := by
    intro j
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (j : ℤ) * hδt
  have claim1 : ∀ j : ℕ, j ≤ n → quarterTurnField G u ≤ quarterTurnField G (u + (j : ℤ) • δ) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hj' : ((j : ℤ) + 1) ≤ (n : ℤ) := by exact_mod_cast hj
      have hlev : N * (u + (j : ℤ) • δ).1 - D * (u + (j : ℤ) • δ).2 ≤ 0 := by
        rw [tlev]
        linarith
      have hs := step (u + (j : ℤ) • δ) hlev
      have e : u + ((j + 1 : ℕ) : ℤ) • δ = (u + (j : ℤ) • δ) + δ := by
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [e]
      exact ih'.trans hs
  have hdlev : N * (u + (n : ℤ) • δ - w).1 - D * (u + (n : ℤ) • δ - w).2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (n : ℤ) * hδt + hn
  obtain ⟨c, hc⟩ : ∃ c : ℤ, δ.1 + δ.2 = 2 * c := ⟨(δ.1 + δ.2) / 2, by omega⟩
  have hdpar : ((u + (n : ℤ) • δ - w).1 + (u + (n : ℤ) • δ - w).2) % 2 = 0 := by
    have e : (u + (n : ℤ) • δ - w).1 + (u + (n : ℤ) • δ - w).2
        = (u.1 + u.2) - (w.1 + w.2) + 2 * ((n : ℤ) * c) := by
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination (n : ℤ) * hc
    rw [e]
    generalize (n : ℤ) * c = q
    omega
  obtain ⟨k, hk⟩ := lattice_of_t_zero N D hcop hDN hD0 (u + (n : ℤ) • δ - w) hdlev hdpar
  have hfw : quarterTurnField G (u + (n : ℤ) • δ) = quarterTurnField G w := by
    have e2 : u + (n : ℤ) • δ = w + (2 * D * k, 2 * N * k) := by
      rw [← hk]
      abel
    rw [e2]
    exact quarterTurnField_kernel hP N D hN hD k w
  calc quarterTurnField G u ≤ quarterTurnField G (u + (n : ℤ) • δ) := claim1 n le_rfl
    _ = quarterTurnField G w := hfw

/-- The rotated monotonicity for the parity-matched pairs (both odd or both even). -/
theorem rotated_mono {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D : ℤ) (hN : fr.child.den - fr.child.num = 2 * N) (hD : fr.child.den + fr.child.num = 2 * D)
    (hpos : 0 < N) (hND : N < D) (u w : Site) (hpar : (u.1 + u.2) % 2 = (w.1 + w.2) % 2)
    (hu : N * u.1 - D * u.2 ≤ N * w.1 - D * w.2) (hw : N * w.1 - D * w.2 ≤ 0) :
    quarterTurnField G u ≤ quarterTurnField G w :=
  rotated_mono_core hP hprice hdrU hdrV N D hN hD hpos hND u w hpar hu hw

/-- **The rotated cap with the monotonicity proved** (no named sheet monotonicity): the cap of the residual on the ray, from the
frame's price (the strong estimates' price range and drifts) and the packet. -/
theorem rotated_ray_cap_mono {fr : ChildFrame} {G : Field} (hP : fr.Packet G)
    (hprice : ∀ z ∈ fr.closedPolygon, fr.cutPrice - 1 ≤ fr.price G z ∧ fr.price G z ≤ fr.cutPrice)
    (hdrU : ∀ z, fr.price G (z + fr.child.modifiedDeck.kernel) = fr.price G z - 1)
    (hdrV : ∀ z, fr.price G (z + fr.child.modifiedDeck.transverse) = fr.price G z)
    (N D a : ℤ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hN2 : 2 * N = fr.child.den - fr.child.num) (hD2 : 2 * D = fr.child.den + fr.child.num)
    (hN0 : 0 < N) (hNDlt : N < D) {p q : ℤ} (hs : N * p - D * q = a - N) (hpq : (p + q) % 2 = 1)
    (J K : ℕ) (hJ1 : 2 * N * (J : ℤ) ≤ N + D - 2) (hJ2 : N + D - 2 < 2 * N * ((J : ℤ) + 1))
    (hK : 2 * N * (K : ℤ) ≤ 3 * D + 3 * N - 1) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ quarterTurnField G (p + (k : ℤ), q + (k : ℤ)) := by
  have hN : fr.child.den - fr.child.num = 2 * N := hN2.symm
  have hD : fr.child.den + fr.child.num = 2 * D := hD2.symm
  apply RotatedCap.rotated_ray_cap hP.strips hP.binary N D a ha1 ha2 hN2 hD2 hN0 hNDlt
  · intro u w hu hw h1 h2
    have hpar : (u.1 + u.2) % 2 = (w.1 + w.2) % 2 := by
      unfold EvenSite at hu hw
      omega
    exact rotated_mono hP hprice hdrU hdrV N D hN hD hN0 hNDlt u w hpar h1 h2
  · intro u w hu hw h1 h2
    have hpar : (u.1 + u.2) % 2 = (w.1 + w.2) % 2 := by
      unfold EvenSite at hu hw
      omega
    exact rotated_mono hP hprice hdrU hdrV N D hN hD hN0 hNDlt u w hpar h1 h2
  · exact hs
  · exact hpq
  · exact hJ1
  · exact hJ2
  · exact hK

end FLatticePaper.RotatedMono
