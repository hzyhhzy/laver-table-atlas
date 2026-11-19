import ShiftedCrossing
import MixedDigits

/-! Dougherty II, 7.2(b), at any width for which the crossing triples
are known. In the equality case a higher nonzero background digit
forces one more degree. Both bounds are capped at the ambient degree. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem terminal_period {m s n a h : Nat} (width : 2≤n) (room : s+n≤m) (hm : h≤m)
    (hh : h≤s+n*n+1)
    (background : s+n*n<h → 2^(s+n)≤a%2^(s+n*n))
    (word : a%2^(s+n)=2^s*(2^n-2)+(2^s-1)) : h≤act tables m a n := by
  let f := act tables m a
  have pos := Nat.two_pow_pos s
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have eqAdd := congrArg (fun t : Nat => 2^s*t) (show 2^n-2+2=2^n by omega)
  change 2^s*(2^n-2+1+1)=2^s*2^n at eqAdd
  rw [Nat.mul_succ,Nat.mul_succ] at eqAdd
  have converted : a%2^(s+n)=2^(s+n)-2^s-1 := by rw [word,Nat.pow_add]; omega
  obtain ⟨first,second⟩ := run_after_zero tables (by omega : s<s+n) room converted
  apply Nat.le_of_not_gt
  intro small
  have visible := Nat.lt_of_lt_of_le small hm
  have line := linear_growth tables m a n visible
  rw [first] at line
  have gap : n≤f 1-s := by change _≤act tables m a 1-s; omega
  have prod := Nat.mul_le_mul_right n gap
  change s+(f 1-s)*n≤f n at line
  change f n<h at small
  have target : f n=s+n*n := by omega
  have over : s+n*n<h := by omega
  have tight : f n=s+(f 1-s)*n := by omega
  have same : f 1-s=n := Nat.eq_of_mul_eq_mul_right (by omega : 0<n) (by omega : (f 1-s)*n=n*n)
  have read := linear_equality_residue tables n (by omega) visible (by rw [first]; exact tight)
  change a%2^(f n+1)<2^(f 1) at read
  have h1 : f 1=s+n := by change s+n≤f 1 at second; omega
  rw [target,h1] at read
  have compare := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (Nat.le_succ (s+n*n)))
  have lower := Nat.mod_le (a%2^(s+n*n+1)) (2^(s+n*n))
  rw [compare] at lower
  exact (Nat.not_lt_of_ge (background over)) (Nat.lt_of_le_of_lt lower read)

theorem shifted_period_bound (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {m s n h : Nat} (width : 2≤n) (dyadic : IsDyadic n) (multiple : n ∣ s)
    (room : s+n≤m) (positiveRoom : n<m) (hm : h≤m) (hh : h≤s+n*n+1)
    (bridges : UpperBridges tables m n) (a x : Nat) (lo : 0<x) (hi : x≤2^n-2)
    (word : a%2^(s+n)=2^s*x+(2^s-1))
    (background : s+n*n<h → 2^(s+n)≤a%2^(s+n*n)) : h≤act tables m a n := by
  by_cases finalWord : x=2^n-2
  · rw [finalWord] at word
    exact terminal_period width room hm hh background word
  obtain ⟨z,y,β,inc,zmax,rep,aligned,passed,link,row⟩ :=
    shifted_crossing_with_row tables width room positiveRoom bridges lo (by omega : x<2^n-2) word
  have ps := Nat.two_pow_pos s
  have psFit : 2^s-1<2^s := by omega
  have pack : z+2^s-1=z+(2^s-1) := by omega
  have fits := Nat.mul_lt_mul_of_pos_left (show y+1<2^n by omega) ps
  rw [Nat.mul_succ] at fits
  have short : 2^s-1<2^(s+n) := Nat.lt_of_lt_of_le psFit (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  have word' : (z+2^s-1)%2^(s+n)=2^s*y+(2^s-1) := by
    rw [pack,Nat.add_mod,rep,Nat.mod_eq_of_lt short,Nat.mod_eq_of_lt (by rw [Nat.pow_add]; omega)]
  have more (need : s+n*n<h) : 2^(s+n)≤(z+2^s-1)%2^(s+n*n) := by
    have old := background need
    have upto : s+n*n≤m := by omega
    have widen := Nat.mul_le_mul_left n (show 1≤n by omega)
    rw [Nat.mul_one] at widen
    have dd := Nat.pow_dvd_pow 2 (show s+n≤s+n*n by omega)
    have notzero : z%2^(s+n*n)≠0 := by
      intro zero
      have proj := Nat.mod_mod_of_dvd z dd
      rw [zero,Nat.zero_mod,rep] at proj
      exact (Nat.ne_of_gt (Nat.mul_pos ps (by omega : 0<y))) proj.symm
    -- Recover z as the product a*c. Every nonzero projected product
    -- strictly exceeds the representative of its left factor.
    have smaller : a%2^(s+n*n)<z%2^(s+n*n) := by
      obtain ⟨c,zc⟩ := row
      rw [zc] at notzero ⊢
      exact left_residue_lt tables upto notzero
    rw [pack,(aligned_add_residue (Nat.le_add_right s (n*n)) aligned psFit).1]
    omega
  have prior := shifted_period_bound H law width dyadic multiple room positiveRoom hm hh bridges
    (z+2^s-1) y (by omega) zmax word' more
  have advance := shifted_action_bound H law dyadic multiple aligned m
  exact Nat.le_trans prior (Nat.le_trans advance (Nat.le_trans (act_mono tables m z passed) (Nat.le_of_eq link)))
termination_by 2^n-1-x
decreasing_by omega

#print axioms shifted_period_bound
end Gamma11
