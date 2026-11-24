import FLatticePaper.Plane.Induction.ReflectedStrict
import FLatticePaper.Plane.Induction.EPolicyLap

/-!
# Strictness of the reflected rank on policy edges with native targets, for arbitrary centres (task 118, W1 base; bridge iv, part three)

`R0plus_edge_plus`: for a policy edge `c → i` of `ePolicy` with `η = +1` whose representative target `nativeRep c + (i - c)`
is native, `R0plus i < R0plus c`. The reduction shifts both sides by the same deck vector (`R0plus_add_combine`), and the
native case is `core_native` (white centres by `R0plus_edge_white_plus`, black centres by `R0plus_edge_black_plus`), with
the flag identity `lap_black_iff` (`laplacian = -1` iff `¬WhiteN` at native points).

Non-native targets are not covered here.
-/

namespace FLatticePaper.ReflectedEdges

open FLatticePaper FLatticePaper.Induction FLatticePaper.PureRank FLatticePaper.EPolicy FLatticePaper.ReflectedRank FLatticePaper.ReflectWitness FLatticePaper.ReflectedStrict FLatticePaper.Construction

set_option maxHeartbeats 400000 in
theorem Qdeck_add_combine (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (w : Pt) (a b : ℤ) :
    Qdeck d hd hden (w.1 + a * d + b * (1 - d), w.2 + a + b * (d + 1)) = Qdeck d hd hden w + 2 * d * a - 2 * (d + 1) * b := by
  obtain ⟨p, ⟨hn, h1, h2⟩, hQ⟩ := Qdeck_spec d hd hden w
  have hq' := Qdeck_eq d hd3 hd hden (w.1 + a * d + b * (1 - d), w.2 + a + b * (d + 1))
    (p.1, p.2.1 + a, p.2.2 + b) ⟨hn, by simp only; linear_combination h1, by simp only; linear_combination h2⟩
  rw [hq', hQ]
  ring

set_option maxHeartbeats 400000 in
theorem R0plus_add_combine (d : ℤ) (hd3 : 3 ≤ d) (hd : d % 2 = 1) (hden : BaseMask.stairEven.Valid d)
    (z : Pt) (a b : ℤ) :
    R0plus d hd hden (z.1 + a * d + b * (1 - d), z.2 + a + b * (d + 1)) = R0plus d hd hden z - 2 * d * a + 2 * (d + 1) * b := by
  unfold R0plus
  have h := Qdeck_add_combine d hd3 hd hden (2 - z.1, d + 1 - z.2) (-a) (-b)
  have e : (2 - (z.1 + a * d + b * (1 - d)), d + 1 - (z.2 + a + b * (d + 1))) =
      ((2 - z.1, d + 1 - z.2).1 + (-a) * d + (-b) * (1 - d), (2 - z.1, d + 1 - z.2).2 + (-a) + (-b) * (d + 1)) := by
    ext <;> simp only <;> ring
  rw [e, h]
  ring

theorem lap_black_iff (k : ℕ) (p : Pt) (hp : NativeP (2 * (k : ℤ) + 3) p) :
    laplacian (reciprocalField k) p = -1 ↔ ¬ WhiteN (2 * (k : ℤ) + 3) p := by
  rw [laplacian_reciprocal_native k hp]
  obtain ⟨x, y⟩ := p
  unfold WhiteN
  dsimp only
  by_cases hev : FLatticePaper.EvenSite (x, y)
  · rw [if_pos hev]
    by_cases h1 : x = 1
    · rw [if_pos h1]
      exact ⟨fun _ h => h.elim (fun h' => h'.2 h1) (fun h' => h'.1 hev), fun _ => rfl⟩
    · rw [if_neg h1]
      exact ⟨fun h => absurd h (by norm_num), fun h => (h (Or.inl ⟨hev, h1⟩)).elim⟩
  · rw [if_neg hev]
    by_cases hi : 0 < y ∧ y < 2 * (k : ℤ) + 3 + 1 ∧ 1 < x + y ∧ x + y < 2 * (k : ℤ) + 3 + 2
    · rw [if_pos hi]
      exact ⟨fun _ h => h.elim (fun h' => hev h'.1) (fun h' => h'.2 hi), fun _ => rfl⟩
    · rw [if_neg hi]
      exact ⟨fun h => absurd h (by norm_num), fun h => (h (Or.inr ⟨hev, hi⟩)).elim⟩

set_option maxHeartbeats 400000 in
theorem core_native (k : ℕ) (y1 y2 e1 e2 : ℤ) (hyN : NativeP (2 * (k : ℤ) + 3) (y1, y2))
    (hb : RetNat (2 * (k : ℤ) + 3) 1 (laplacian (reciprocalField k) (y1, y2) = -1) (y1, y2)
      ((y1, y2) + (e1, e2)))
    (hT : NativeP (2 * (k : ℤ) + 3) ((y1, y2) + (e1, e2))) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1 + e1, y2 + e2) <
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) (y1, y2) := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  have hT' : NativeP (2 * (k : ℤ) + 3) (2 - (y1 + e1), 2 * (k : ℤ) + 3 + 1 - (y2 + e2)) := by
    have := (nativeP_refl (2 * (k : ℤ) + 3) (y1 + e1) (y2 + e2)).mpr hT
    simpa using this
  by_cases hl : laplacian (reciprocalField k) (y1, y2) = -1
  · have hB := (lap_black_iff k (y1, y2) hyN).mp hl
    rw [eq_true hl] at hb
    exact R0plus_edge_black_plus (2 * (k : ℤ) + 3) y1 y2 e1 e2 hd3 hdodd hden hyN hB hb hT'
  · have hW : WhiteN (2 * (k : ℤ) + 3) (y1, y2) := by
      by_contra hw
      exact hl ((lap_black_iff k (y1, y2) hyN).mpr hw)
    rw [eq_false hl] at hb
    exact R0plus_edge_white_plus (2 * (k : ℤ) + 3) y1 y2 e1 e2 hd3 hdodd hden hyN hW hb hT'

set_option maxHeartbeats 400000 in
theorem R0plus_edge_plus (k : ℕ) (c i : Pt)
    (h : ePolicy (2 * (k : ℤ) + 3) 1 (laplacian (reciprocalField k)) c i)
    (hT : NativeP (2 * (k : ℤ) + 3) (nativeRep (2 * (k : ℤ) + 3) c + (i - c))) :
    R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) i <
      R0plus (2 * (k : ℤ) + 3) (by omega) (stairEven_valid_reciprocal k) c := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have hden := stairEven_valid_reciprocal k
  obtain ⟨hyN, a, b, hc⟩ := nativeRep_spec hden c
  rw [combine_mk_one hdodd] at hc
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  simp only [Prod.fst_add, Prod.snd_add] at hc1 hc2
  unfold ePolicy at h
  rw [laplacian_reciprocal_rep k c] at h
  generalize hy : nativeRep (2 * (k : ℤ) + 3) c = y at h hT hyN hc1 hc2
  obtain ⟨y1, y2⟩ := y
  simp only at hc1 hc2 hT
  obtain ⟨e1, he1⟩ : ∃ e1 : ℤ, e1 = i.1 - c.1 := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : ℤ, e2 = i.2 - c.2 := ⟨_, rfl⟩
  have hie : i - c = (e1, e2) := by
    ext <;> simp [he1, he2]
  rw [hie] at h hT
  have hcore := core_native k y1 y2 e1 e2 hyN h hT
  have hI : i = (y1 + e1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + e2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  have hcpair : c = (y1 + a * (2 * (k : ℤ) + 3) + b * (1 - (2 * (k : ℤ) + 3)),
      y2 + a + b * ((2 * (k : ℤ) + 3) + 1)) := by
    ext <;> simp only <;> linarith
  rw [hI, hcpair]
  have h1 := R0plus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1 + e1, y2 + e2) a b
  have h2 := R0plus_add_combine (2 * (k : ℤ) + 3) hd3 hdodd hden (y1, y2) a b
  simp only at h1 h2
  linarith

end FLatticePaper.ReflectedEdges
