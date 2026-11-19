import BackwardTables

/-! Periodic row operations in the direct union of the backward finite
tables. These lemmas work with the ordinary, untruncated product. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem at_native_arguments {d x y : Nat} (xf : x<2^d) (yf : y<2^d) : mul x y=finite d x y := by
  by_cases zero : x=0
  · subst x; rw [mul_zero_left,finite_zero_left,Nat.mod_eq_of_lt yf]
  · exact at_degree (Nat.pos_of_ne_zero zero) xf y

theorem project_native (d x y : Nat) : mul x y%2^d=mul (x%2^d) (y%2^d) := by
  rw [mul_projects,at_native_arguments (Nat.mod_lt x (Nat.two_pow_pos d)) (Nat.mod_lt y (Nat.two_pow_pos d))]
  have residue (a : Nat) : neg d (a%2^d)=neg d a := by simp only [neg,Nat.mod_mod]
  unfold finite
  rw [residue x,residue y]

theorem power_row (k y : Nat) : mul (2^k) y=y%2^k := by
  have pr := project_native k (2^k) y
  rw [Nat.mod_self,mul_zero_left,Nat.mod_eq_of_lt (mul_lt_left (Nat.two_pow_pos k) y)] at pr
  exact pr

theorem row_congr {x l : Nat} (pos : 0<x) (per : PeriodExp x l) {u v : Nat}
    (same : u%2^l=v%2^l) : mul x u=mul x v := by
  let d := max (x.log2+1) l
  have dl : l≤d := Nat.le_max_right ..
  have fit : x<2^d := Nat.lt_of_lt_of_le (Nat.lt_log2_self (n:=x))
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))
  have kills := (per l).mpr (Nat.le_refl _)
  rw [at_degree pos fit,finite_zero_iff] at kills
  have args : neg d u%2^l=neg d v%2^l := by rw [neg_project dl,neg_project dl]; simp only [neg,same]
  rw [at_degree pos fit,at_degree pos fit,finite,finite,(tables d).reduce_period kills,
    args,← (tables d).reduce_period kills]

theorem previous_column (a i : Nat) : mul (a+1) i=mul (mul (a+1) (i+1)) a := by
  apply eq_of_neg_all
  intro d
  let e := neg d (a+1)
  let b := neg d (i+1)
  rw [neg_mul,neg_mul,neg_mul]
  calc
    (tables d).mul e (neg d i) = (tables d).mul e ((b+1)%2^d) :=
      congrArg ((tables d).mul e) (negate_succ d i).symm
    _ = (tables d).mul ((tables d).mul e b) (e+1) := by
      rw [(tables d).mul_mod_right,(tables d).row_recurrence]
    _ = (tables d).mul ((tables d).mul e b) (neg d a) := by
      rw [← (tables d).mul_mod_right _ (e+1),negate_succ]

def powers (a : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => mul (powers a i) a

theorem power_from_column {a K : Nat} (zero : mul (a+1) K=0) (i : Nat) (le : i≤K) :
    powers a i=mul (a+1) (K-i) := by
  induction i with
  | zero => simpa [powers] using zero.symm
  | succ i ih =>
    rw [powers,ih (by omega),previous_column a (K-(i+1)),show K-(i+1)+1=K-i by omega]

theorem map_powers (x a i : Nat) : mul x (powers a i)=powers (mul x a) i := by
  induction i with
  | zero => simp [powers,mul_zero_right]
  | succ i ih => rw [powers,powers,mul_distrib,ih]

theorem positive_half {x k : Nat} (pos : 0<x) (fit : x<2^(k+1)) : mul x (2^k)=0 := by
  rw [at_degree pos fit,finite_zero_iff]
  apply positive_half_zero tables k (neg (k+1) x) _ (neg_lt ..)
  rw [neg_small pos fit]; omega

theorem smaller_generated_period {x u l : Nat} (per : PeriodExp (x+1) l) (small : mul (x+1) u<x) :
    0<l ∧ mul (mul (x+1) u+1) (2^(l-1))=0 := by
  let r := u%2^l
  have mid : mul (x+1) u=mul (x+1) r := row_congr (Nat.zero_lt_succ _) per (Nat.mod_mod ..).symm
  have fit : r<2^l := Nat.mod_lt _ (Nat.two_pow_pos l)
  have shorter : r+1<2^l := by
    apply Nat.lt_of_not_ge
    intro big
    have e : r=2^l-1 := by omega
    rw [mid,e,period_last x l per] at small
    exact Nat.lt_irrefl _ small
  have lp : 0<l := by
    apply Nat.pos_of_ne_zero
    intro z; rw [z,Nat.pow_zero] at shorter; omega
  have inDegree : r+1<2^((l-1)+1) := by rwa [Nat.sub_add_cancel lp]
  exact ⟨lp,by rw [mid,compose_rows,positive_half (Nat.zero_lt_succ _) inDegree,mul_zero_right]⟩

theorem generated_divisible {x d : Nat} (dv : 2^d∣x) (y : Nat) : 2^d∣mul (x+1) y := by
  apply Nat.dvd_of_mod_eq_zero
  rw [project_native,Nat.add_mod,Nat.mod_eq_zero_of_dvd dv,Nat.zero_add,Nat.mod_mod]
  rw [← project_native]
  have zero : mul 1 y=0 := by have := mul_lt_left (by decide : 0<1) y; omega
  rw [zero,Nat.zero_mod]

#print axioms power_from_column
#print axioms smaller_generated_period
end Gamma11.Backward
