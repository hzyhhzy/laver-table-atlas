import ManuscriptEndpoint
import DenseDigits

/-! Dougherty II, Corollary 6.4 and the protected multiplication of
Lemma 6.7. The right endpoint of 6.3 suffices for both statements. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

theorem shifted_action_bound (H : FirstRowUnbounded) (law : FiniteBlockLaw) {a s w : Nat}
    (dyadic : IsDyadic w) (multiple : w ∣ s) (aligned : 2^s ∣ a) (m : Nat) :
    act tables m (a+2^s-1) w ≤ act tables m a (s+w) := by
  let r := a+2^s-1
  let n := image H r w
  have bound : BlockBoundary H := (finite_block_iff_boundary H).mp law
  have here := (bound (d:=n) dyadic multiple aligned (Nat.le_refl n)).2
  have hA := numeral_total H a
  have hS := numeral_total H (2^s-1)
  have hR := numeral_total H r
  have read := finite_read _ _ (total_comp hA hS) hR n w here
  rw [index_comp] at read
  change min n (image H a (image H (2^s-1) w))=min n n at read
  rw [ones_shift_of_boundary H bound dyadic multiple,Nat.min_self] at read
  have upper : n≤image H a (s+w) := Nat.le_trans (Nat.le_of_eq read.symm) (Nat.min_le_right ..)
  rw [numeral_cap_eq_min H,numeral_cap_eq_min H]
  change min m n≤min m (image H a (s+w))
  omega

theorem guarded_shift_multiplication (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {m a s w : Nat} (dyadic : IsDyadic w) (multiple : w ∣ s) (aligned : 2^(s+w) ∣ a)
    (i : Nat) (guard : ∀ j, 2≤j → j≤i+1 → act tables m (a+2^s*j-1) w=m) :
    (tables m).mul (a+2^s-1) (i+1)=(a+2^s*(i+1))%2^m := by
  have pos := Nat.two_pow_pos s
  have next : a+2^s-1+1=a+2^s := by omega
  induction i with
  | zero => rw [(tables m).mul_one,next,Nat.mul_one]
  | succ i ih =>
    let B := a+2^s*(i+1)
    have aDiv : 2^s ∣ a := Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_add_right s w)) aligned
    have div : 2^s ∣ B := Nat.dvd_add aDiv (Nat.dvd_mul_right (2^s) (i+1))
    have plus : B+2^s=a+2^s*(i+1+1) := by rw [Nat.mul_succ,Nat.add_assoc]
    have protect := guard (i+1+1) (by omega) (Nat.le_refl _)
    rw [← plus] at protect
    have high := shifted_action_bound H law dyadic multiple div m
    rw [protect] at high
    have zeroB := (le_act_iff tables m B (s+w) m (Nat.le_refl _)).mp high
    have zeroP := (le_act_iff tables m (B+2^s-1) w m (Nat.le_refl _)).mp (Nat.le_of_eq protect.symm)
    have block := law dyadic multiple div ((canonical_mul m _ _).symm.trans zeroP)
    have prev := ih (fun j lo hi => guard j lo (by omega))
    rw [(tables m).row_recurrence (a+2^s-1) (i+1),prev,(tables m).mul_mod_left,next]
    exact (add_period_background (y:=2^s) aligned zeroB).trans (block.trans (congrArg (fun z => z%2^m) plus))

#print axioms shifted_action_bound
#print axioms guarded_shift_multiplication
end Gamma11
