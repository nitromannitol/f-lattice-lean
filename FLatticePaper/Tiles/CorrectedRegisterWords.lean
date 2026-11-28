import FLatticePaper.Tiles.CorrectedRegisterDiagram

/-! The register hypotheses from the Farey recursion at a non-base prefix. -/

namespace FLatticePaper.Tiles.CorrectedRegisterWords

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open CorrectedRegisterDiagram CorrectedDomainLattice Standard

/-- The register immediately after retaining or replacing the even parent. -/
def register (P : Parents) (one : Bool) (N : ℕ) (Z : Site) : Register :=
  let p := P.current .odd
  let q := if one then P.current .even else P.even
  ⟨scale p, (chart p (texV1Even q)).1, (N : ℤ)*scale p, p.den,p.num,q.den,q.num,Z.1,Z.2⟩

theorem old_periods (P : Parents) (one : Bool) (N : ℕ) (Z : Site) :
    oldOdd (register P one N Z) one = texV1Odd P.odd ∧
    oldEven (register P one N Z) one = texV1Even P.even := by
  cases one <;> constructor <;> apply Prod.ext <;>
    simp [oldOdd,oldEven,register,texV1Odd,texV1Even,Parents.current,Parents.combine] <;> ring

/-- The first digit determines a common closed sector for the two horizontal periods. -/
def firstSector : Digit → Fin 3
  | .one => 1
  | .two => 2
  | .three => 0

private abbrev sectorPair (s : Fin 3) (P : Parents) :=
  inSector s (texV1Odd P.odd) ∧ inSector s (texV1Even P.even)

private theorem sector_step {s : Fin 3} {P : Parents} (h : sectorPair s P) (d : Digit) :
    sectorPair s (P.step d) := by
  rcases h with ⟨a,b⟩
  fin_cases s <;> cases d <;>
    norm_num [sectorPair,inSector,Parents.step,Parents.current,Parents.combine,texV1Odd,texV1Even] at * <;> omega

theorem sectors (x : Digit) (xs : Word) : sectorPair (firstSector x) (parentsAt (x :: xs)) := by
  induction xs using List.reverseRecOn with
  | nil => cases x <;> norm_num [sectorPair,inSector,firstSector,parentsAt,Parents.walk,root,Parents.step,Parents.current,Parents.combine,texV1Odd,texV1Even] <;> decide
  | append_singleton v d ih =>
    change sectorPair (firstSector x) (parentsAt ((x::v)++[d]))
    rw [parentsAt_append_singleton]
    exact sector_step ih d

private theorem odd_scale (n d : ℤ) (h : (n+d)%2=1) : (d^2+2*d*n-n^2)%2=1 := by
  rcases (show (n%2=0 ∧ d%2=1) ∨ (n%2=1 ∧ d%2=0) by omega) with ⟨hn,hd⟩ | ⟨hn,hd⟩
  all_goals
    have a : n^2%2=n%2 := by rw [pow_two,Int.mul_emod,hn]; decide
    have b : d^2%2=d%2 := by rw [pow_two,Int.mul_emod,hd]; decide
    rw [show 2*d*n=2*(d*n) by ring]
    omega

private theorem even_components {q : Fraction} (he : q.Even) (hr : q.Reduced) :
    q.den%2=1 ∧ q.num%2=1 := by
  have h := Fraction.rotate_odd_of_even he hr
  rw [Fraction.rotate_of_even he] at h
  change (((q.den-q.num)/2)+((q.den+q.num)/2))%2=1 at h
  change (q.num+q.den)%2=0 at he
  omega

private theorem scale_ge {p : Fraction} (hp : 1 ≤ p.num) (hd : p.num < p.den) : 7 ≤ scale p := by
  have h₁ : 0 ≤ (p.num-1)*(2*p.den-p.num-1) := mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ (p.den-2)*(p.den+4) := mul_nonneg (by omega) (by omega)
  unfold scale
  nlinarith only [h₁,h₂]

private theorem old_sizes (r : Register) (one : Bool)
    (hm : r.M=r.d^2+2*r.d*r.n-r.n^2)
    (ht : 2*r.T=(r.d+r.n)*r.f+(r.d-r.n)*r.g) :
    2*(if one then 2*r.T-r.M else r.M-2*r.T) =
        (r.d+r.n)*(oldOdd r one).1+(r.d-r.n)*(oldOdd r one).2 ∧
    2*(if one then r.M-r.T else r.T) =
        (r.d+r.n)*(oldEven r one).1+(r.d-r.n)*(oldEven r one).2 := by
  cases one <;> simp only [Bool.false_eq_true,if_false,if_true,oldOdd,oldEven] <;>
    constructor <;> linarith only [hm,ht]

/-- The hypotheses of the general integer calculation hold at every proper preceding
quadruple, for either exit and every positive length. -/
theorem regular (x : Digit) (xs : Word) (hw : ¬ IsBase (x::xs)) (one : Bool)
    (N : ℕ) (hN : 0 < N) (Z : Site) :
    Regular (register (parentsAt (x::xs)) one N Z) one (firstSector x) := by
  let P := parentsAt (x::xs)
  let r := register P one N Z
  let p := P.current .odd
  let q := if one then P.current .even else P.even
  have valid := parentsAt_valid (x::xs)
  change P.ValidFrame at valid
  obtain ⟨a,b,c,d⟩ := SiteScope.proper_of_not_base (x::xs) hw
  change 0 < P.odd.num at a
  change P.odd.num < P.odd.den at b
  change 0 < P.even.num at c
  change P.even.num < P.even.den at d
  have ord : 1 ≤ p.num ∧ p.num < p.den := by
    dsimp [p,Parents.current,Parents.combine]
    omega
  have evenE : q.Even := by cases one <;> first | exact valid.even_parity | exact valid.current_even_parity
  have red : q.Reduced := by cases one <;> first | exact valid.even_reduced | exact valid.current_reduced .even
  obtain ⟨df,nf⟩ := even_components evenE red
  obtain ⟨df',nf'⟩ := even_components valid.even_parity valid.even_reduced
  have op := valid.current_odd_parity
  change (p.num+p.den)%2=1 at op
  have small : 7 ≤ r.M := scale_ge ord.1 ord.2
  have run : r.M ≤ r.S := by
    change r.M ≤ (N : ℤ)*r.M
    simpa using mul_le_mul_of_nonneg_right (by exact_mod_cast hN : (1:ℤ) ≤ N) (by omega : 0 ≤ r.M)
  have pairs := old_periods P one N Z
  change oldOdd r one = texV1Odd P.odd ∧ oldEven r one = texV1Even P.even at pairs
  have e₁ : 4 ≤ (oldOdd r one).1 ∧ 2 ≤ (oldOdd r one).2 ∧ 2 ≤ (oldOdd r one).1-(oldOdd r one).2 := by
    rw [pairs.1]; dsimp [texV1Odd]; omega
  have e₂ : 3 ≤ (oldEven r one).1 ∧ 1 ≤ (oldEven r one).2 ∧ 2 ≤ (oldEven r one).1-(oldEven r one).2 := by
    rw [pairs.2]; dsimp [texV1Even]; omega
  have hb : (q.den+q.num)%2=0 := by change (q.num+q.den)%2=0 at evenE; omega
  have ht := twice_first p (texV1Even q) hb
  have vals := old_sizes r one rfl ht
  have signs : 0 ≤ r.d+r.n ∧ 0 ≤ r.d-r.n := by change 0 ≤ p.den+p.num ∧ 0 ≤ p.den-p.num; omega
  have h₁ := add_le_add (mul_le_mul_of_nonneg_left e₁.1 signs.1) (mul_le_mul_of_nonneg_left e₁.2.1 signs.2)
  have h₂ := add_le_add (mul_le_mul_of_nonneg_left e₂.1 signs.1) (mul_le_mul_of_nonneg_left e₂.2.1 signs.2)
  have ss := sectors x xs
  change inSector (firstSector x) (texV1Odd P.odd) ∧ inSector (firstSector x) (texV1Even P.even) at ss
  change Regular r one (firstSector x)
  refine ⟨ord.1,?_,small,run,e₁.1,e₁.2.1,e₁.2.2,e₂.1,e₂.2.1,e₂.2.2,?_,?_,?_,?_,?_,df,nf,?_⟩
  · change 1 ≤ p.den-p.num; omega
  · rw [vals.1]; linarith only [h₁]
  · rw [vals.2]; linarith only [h₂]
  · rw [pairs.1]; exact ss.1
  · rw [pairs.2]; exact ss.2
  · change (p.den+p.num)%2=1; omega
  · exact odd_scale _ _ op

end FLatticePaper.Tiles.CorrectedRegisterWords
