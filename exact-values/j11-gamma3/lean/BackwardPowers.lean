import BackwardCoding

/-! For two generators already below the induction bound, compression
compares every left power using a common zero column. -/
set_option autoImplicit false
namespace Gamma11.Backward

theorem powers_of_compressed {X z b l Y : Nat} (row : CompressedRow X z b l Y) (n : Nat) :
    powers (X+2^z*Y) n=encodeDigit X z b (powers (modelGenerator b l Y) n) := by
  let a := X+2^z*Y
  let m := modelGenerator b l Y
  let d := a+m+n+2
  have width : d<2^d := Nat.lt_two_pow_self
  have bigger : a+1≤d ∧ m+1≤d ∧ n≤d := by dsimp [d]; omega
  have za := zero_at_width (Nat.zero_lt_succ a) (Nat.le_trans bigger.1 (Nat.le_of_lt width))
  have zm := zero_at_width (Nat.zero_lt_succ m) (Nat.le_trans bigger.2.1 (Nat.le_of_lt width))
  have fits := Nat.le_trans bigger.2.2 (Nat.le_of_lt width)
  exact (power_from_column za n fits).trans ((row (2^d-n)).trans
    (congrArg (encodeDigit X z b) (power_from_column zm n fits).symm))

theorem encode_nested {X z b w : Nat} (dy : IsDyadic b) (fit : w<2^b) (t : Nat) :
    encodeDigit (mul (X+1) w) z b t=encodeDigit X z b (encodeDigit (2^b*w) 0 b t) := by
  have scaled : encodeDigit (2^b*w) 0 b t=2^b*mul (w+1) (t/2^b)+t%2^b := by
    rw [encodeDigit,scaled_generator dy (Nat.dvd_refl _) fit,Nat.pow_zero,Nat.one_mul]
  rw [scaled,encoding_parts (Nat.mod_lt _ (Nat.two_pow_pos _)),encodeDigit,compose_rows]

theorem powers_at_smaller_digit {L X z b l w r : Nat} (ih : RowsBelow L)
    (dy : IsDyadic b) (dz : b∣z) (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (wFit : w<2^l) (rFit : r<2^b) (cutX : mul (X+1) w+2^z*r<L)
    (cutCode : 2^b*w+r<L) (n : Nat) :
    powers (mul (X+1) w+2^z*r) n=encodeDigit X z b (powers (2^b*w+r) n) := by
  have fits := Nat.lt_of_lt_of_le wFit (Nat.pow_le_pow_right (by decide : 0<2) lb)
  obtain ⟨h,ph⟩ := has_period_exp (Nat.zero_lt_succ w)
  have cap := Nat.le_trans ((ph l).mp (zero_at_width (Nat.zero_lt_succ w) (Nat.succ_le_of_lt wFit))) lb
  have rowX := ih dy dz (generated_divisible dX w) (induced_period per wFit ph) cap rFit cutX
  have lowFit : 2^(0+b)∣2^b*w := by rw [Nat.zero_add]; exact Nat.dvd_mul_right ..
  have codeCut : 2^b*w+2^0*r<L := by simpa only [Nat.pow_zero,Nat.one_mul] using cutCode
  have rowC := ih (z:=0) dy (Nat.dvd_zero _) lowFit (scaled_period dy (Nat.dvd_refl _) fits ph) cap rFit codeCut
  have k := powers_of_compressed rowC n
  rw [Nat.pow_zero,Nat.one_mul] at k
  exact (powers_of_compressed rowX n).trans ((encode_nested dy fits _).trans (congrArg (encodeDigit X z b) k.symm))

#print axioms powers_at_smaller_digit
end Gamma11.Backward
