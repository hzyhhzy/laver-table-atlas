import CanonicalTables
import EndpointMidpoint

/-! In the ordinary table of size 4a, a = 2^k, the row a starts with
a+1, ..., 2a. Indeed, the rows strictly between a and 2a come from upper
copies in the table of size 2a and return to zero by column a in size 4a. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem between_quarters_zero (k y : Nat) (hy : 0 < y) (fit : y < 2^k) :
    (tables (k+2)).mul (2^k+y) (2^k) = 0 := by
  cases k with
  | zero => simp at fit; omega
  | succ k =>
    have old := positive_half_zero tables k y hy fit
    have copy := upper_copy (tables (k+2)) (tables (k+1)) fit (2^k)
    rw [if_pos old] at copy
    have new := double_zero tables (k+2) _ _ copy
    rw [show 2 * 2^k = 2^(k+1) by rw [Nat.pow_succ,Nat.mul_comm]] at new
    exact new

theorem quarter_prefix (k b : Nat) (lo : 0 < b) (hi : b ≤ 2^k) :
    (tables (k+2)).mul (2^k) b = 2^k+b := by
  have size : 2^(k+2) = 2^k*4 := by rw [Nat.pow_add]
  have pos := Nat.two_pow_pos k
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases z : b=0
    · subst b
      rw [(tables _).mul_one,Nat.mod_eq_of_lt (by rw [size]; omega)]
    · have old := ih (by omega) (by omega)
      have zero := between_quarters_zero k b (by omega) (by omega)
      have period := (tables (k+2)).periodic_multiple zero 1 1
      simp only [Nat.mul_one] at period
      rw [(tables _).row_recurrence,old,period,(tables _).mul_one,
        Nat.mod_eq_of_lt (by rw [size]; omega)]
      omega

theorem quarter_square (k : Nat) : (tables (k+2)).mul (2^k) (2^k) = 2^(k+1) := by
  rw [quarter_prefix k _ (Nat.two_pow_pos _) (Nat.le_refl _),Nat.pow_succ]
  omega

#print axioms quarter_square
end Gamma11
