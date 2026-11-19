import BackwardLocal

/-! Reduction modulo the highest bit, the cost of lifting a period,
and the value of a short left power of a full digit. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem generated_mod (M X i : Nat) :
    mul (X+1) i%2^M=mul (X%2^M+1) i := by
  have below := Nat.mod_lt X (Nat.two_pow_pos M)
  have range := mul_lt_left (Nat.zero_lt_succ (X%2^M)) i
  change mul (X%2^M+1) i<X%2^M+1 at range
  calc
    _ = mul ((X+1)%2^M) (i%2^M) := project_native ..
    _ = mul (((X%2^M)+1)%2^M) (i%2^M) := by rw [Nat.mod_add_mod]
    _ = mul (X%2^M+1) i%2^M := (project_native ..).symm
    _ = _ := Nat.mod_eq_of_lt (by omega)

theorem powers_project (M a i : Nat) : powers a i%2^M=powers (a%2^M) i := by
  induction i with
  | zero => simp [powers]
  | succ i ih => rw [powers,powers,project_native,ih]

theorem period_lifts_once {M x k : Nat} (pos : 0<x) (fits : x≤2^(M+1))
    (low : mul x (2^k)%2^M=0) : mul x (2^(k+1))=0 := by
  let a := neg (M+1) x
  have zero := (finite_zero_iff M x (2^k)).mp ((mul_projects M x (2^k)).symm.trans low)
  have reduceA : a%2^M=neg M x := neg_project (Nat.le_succ _) _
  rw [← reduceA,(tables M).mul_mod_left] at zero
  have bound := (le_act_iff tables (M+1) a k M (Nat.le_succ M)).mpr zero
  have lim := act_le tables (M+1) a (k+1)
  have hit : act tables (M+1) a (k+1)=M+1 := by
    apply Nat.le_antisymm lim
    apply Nat.le_of_not_gt
    intro h
    have strict := act_strict_below_cap tables (M+1) a k (k+1) (Nat.lt_succ_self _) (show _<M+1 by omega)
    omega
  have ff := (finite_zero_iff (M+1) x (2^(k+1))).mpr
    ((le_act_iff tables (M+1) a (k+1) (M+1) (Nat.le_refl _)).mp (Nat.le_of_eq hit.symm))
  have pr := mul_projects (M+1) x (2^(k+1))
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_left pos _) fits), ff] at pr

theorem short_powers_of_digit {X z b l : Nat} (row : DigitRow X z b) (per : PeriodExp (X+1) l)
    {r : Nat} (rf : r<2^b) : powers (X+2^z*(2^b-1)) (2^b-r)=X+2^z*r := by
  let p := 2^b
  let K := p*2^l
  have pp : 0<p := Nat.two_pow_pos b
  have lp := Nat.two_pow_pos l
  have zero := row (2^l) 0 pp
  rw [Nat.add_zero,(per l).mpr (Nat.le_refl _),Nat.mul_zero,Nat.add_zero] at zero
  have room : p≤K := Nat.le_mul_of_pos_right _ lp
  have algebra : p*(2^l-1)+p=K := by
    rw [← Nat.mul_succ,show Nat.succ (2^l-1)=2^l from Nat.sub_add_cancel lp]
  have index : K-(p-r)=p*(2^l-1)+r := by change r<p at rf; omega
  have pow := power_from_column (K:=K) zero (p-r) (by omega)
  rw [index,row _ _ rf,period_last X l per] at pow
  exact pow

#print axioms period_lifts_once
#print axioms short_powers_of_digit
end Gamma11.Backward
