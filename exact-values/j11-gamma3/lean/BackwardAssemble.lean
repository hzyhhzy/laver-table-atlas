import BackwardBoundary

/-! A mixed digit needs only a single zero at column 2^b. From this
bound the whole two-parameter full-digit row follows by induction on
the generator. Zero backgrounds and the end digits cost no premise. -/
set_option autoImplicit false
namespace Gamma11.Backward

def MixedInteriorCap : Prop := ∀ {X z b l r : Nat}, 0<X → 2≤b → IsDyadic b → b∣z →
  2^(z+b)∣X → PeriodExp (X+1) l → l≤b → 0<r → r+1<2^b →
  mul (X+2^z*r+1) (2^b)=0

theorem caps_at_zero {b z r : Nat} (dy : IsDyadic b) (dz : b∣z) (small : r<2^b) :
    mul (2^z*r+1) (2^b)=0 := by
  let F := 2^z*(2^b-1)+1
  have image : mul F r=2^z*r := (full_block_at_zero dy dz r).trans (by rw [Nat.mod_eq_of_lt small])
  have original := zero_at_width (Nat.zero_lt_succ r) (show r+1≤2^b by omega)
  rw [← image,compose_rows,original,mul_zero_right]

theorem caps_of_interior (interior : MixedInteriorCap) (L : Nat) : MixedCapsBelow L := by
  intro X z b l r dy dz dX per lb gap _
  by_cases noDigit : r=0
  · rw [noDigit,Nat.mul_zero,Nat.add_zero]; exact (per b).mpr lb
  by_cases base : X=0
  · rw [base,Nat.zero_add]; exact caps_at_zero dy dz (by omega)
  have large : 2≤b := by
    apply Nat.le_of_not_gt
    intro h
    have le := Nat.pow_le_pow_right (by decide : 0<2) (show b≤1 by omega)
    change 2^b≤2 at le
    omega
  exact interior (Nat.pos_of_ne_zero base) large dy dz dX per lb (Nat.pos_of_ne_zero noDigit) gap

theorem generated_period_le {X l : Nat} (per : PeriodExp (X+1) l) (i : Nat) :
    ∃ h, PeriodExp (mul (X+1) i+1) h ∧ h≤l := by
  let r := i%2^l
  have small : r<2^l := Nat.mod_lt i (Nat.two_pow_pos l)
  have read : mul (X+1) i=mul (X+1) r := row_congr (Nat.zero_lt_succ _) per (Nat.mod_mod ..).symm
  obtain ⟨h,ph⟩ := has_period_exp (Nat.zero_lt_succ (mul (X+1) i))
  refine ⟨h,ph,(ph l).mp ?_⟩
  rw [read,compose_rows,zero_at_width (Nat.zero_lt_succ r) (Nat.succ_le_of_lt small),mul_zero_right]

private theorem next_full {L X z b l : Nat} (previous : FullDigitsBelow L) (caps : MixedCapsBelow L)
    (dy : IsDyadic b) (dz : b∣z) (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l)
    (lb : l≤b) (endAt : X+2^z*(2^b-1)=L) : DigitRow X z b := by
  have bp : 0<b := by obtain ⟨e,rfl⟩ := dy; exact Nat.two_pow_pos _
  have pgt : 1<2^b := Nat.one_lt_two_pow (Nat.ne_of_gt bp)
  have pos := Nat.mul_pos (Nat.two_pow_pos z) (Nat.sub_pos_of_lt pgt)
  apply (digit_row_iff_predecessors ..).mpr
  constructor
  · intro i r fit
    obtain ⟨h,ph,lh⟩ := generated_period_le per i
    have small : mul (X+1) i≤X := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ X) i)
    have digit := Nat.mul_le_mul_left (2^z) (show r+1≤2^b-1 by omega)
    exact inner_step_of_caps previous caps dy dz (generated_divisible dX i) dX ph (Nat.le_trans lh lb)
      fit (by omega)
  · intro i
    have small : mul (X+1) (i+1)≤X := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ X) _)
    exact boundary_step_below previous dy dz X dX per lb (by omega) i (by omega)

theorem full_from_mixed_interior (caps : MixedInteriorCap) : FullDigitRow := by
  have allAt (L : Nat) : ∀ {X z b l : Nat}, IsDyadic b → b∣z → 2^(z+b)∣X →
      PeriodExp (X+1) l → l≤b → X+2^z*(2^b-1)=L → DigitRow X z b := by
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro X z b l dy dz dX per lb exactGen
      apply next_full (L:=L) _ (caps_of_interior caps L) dy dz dX per lb exactGen
      intro A t n h dy' dt dA ph hn smaller
      exact ih _ smaller dy' dt dA ph hn rfl
  intro b z X l dy dz dX per lb
  exact allAt _ dy dz dX per lb rfl

#print axioms full_from_mixed_interior
end Gamma11.Backward
