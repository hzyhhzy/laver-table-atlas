import DigitBorrows

/-! The local full-digit law at width one, including every allowed
positive background. With at most a two-element period a positive
background must itself be a single power of two. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem square_zero_iff_power {x : Nat} (pos : 0<x) : mul x x=0 ↔ ∃ k, x=2^k := by
  constructor
  · intro zero
    let d := x.log2+1
    have fit : x<2^d := Nat.lt_log2_self
    rw [at_degree pos fit,finite,neg_eq_zero_iff,Nat.mod_eq_of_lt ((tables d).mul_lt ..)] at zero
    rcases (square_zero_iff tables d (neg d x) (neg_lt ..)).mp zero with impossible|⟨k,kd,hk⟩
    · rw [neg_small pos fit] at impossible; omega
    · have up := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_lt kd)
      rw [neg_small pos fit] at hk
      exact ⟨k,by omega⟩
  · rintro ⟨k,rfl⟩; rw [power_row,Nat.mod_self]

theorem single_bit_output (m i : Nat) : mul (2^m+1) i=2^m*(i%2) := by
  have result := full_block_at_zero (z:=m) (b:=1) (show IsDyadic 1 from ⟨0,rfl⟩) (Nat.one_dvd _) i
  simpa only [Nat.pow_one,show 2-1=1 by decide,Nat.mul_one] using result

private theorem two_bit_products {m z : Nat} (low : z<m) :
    let v := 2^m; let u := 2^z; let a := v+u
    mul u a=0 ∧ mul v a=u ∧ mul a a=v := by
  let v := 2^m
  let u := 2^z
  let a := v+u
  have uPos : 0<u := Nat.two_pow_pos _
  have vPos : 0<v := Nat.two_pow_pos _
  have uv : u<v := Nat.pow_lt_pow_right (by decide) low
  have apos : 0<a := by dsimp only [a]; omega
  have aMod : a%v=u := by dsimp only [a]; rw [Nat.add_mod_left,Nat.mod_eq_of_lt uv]
  have multiple : u ∣ v := Nat.pow_dvd_pow 2 (Nat.le_of_lt low)
  have uu : mul u a=0 := (power_row ..).trans (Nat.mod_eq_zero_of_dvd (Nat.dvd_add multiple (Nat.dvd_refl u)))
  have vu : mul v a=u := (power_row ..).trans aMod
  have rem := project_native m a a
  change mul a a%v=mul (a%v) (a%v) at rem
  rw [aMod,power_row,Nat.mod_self] at rem
  have nz : mul a a≠0 := by
    rintro h
    obtain ⟨k,hk⟩ := (square_zero_iff_power apos).mp h
    by_cases km : k≤m
    · have le : 2^k≤v := Nat.pow_le_pow_right (by decide) km
      dsimp only [a] at hk; omega
    · have le := Nat.pow_le_pow_right (by decide : 0<2) (show m+1≤k by omega)
      rw [Nat.pow_succ] at le
      change v*2≤2^k at le; dsimp only [a] at hk; omega
  have bounded := mul_lt_left apos a
  change mul a a<v+u at bounded
  have mid : v≤mul a a := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) (Nat.dvd_of_mod_eq_zero rem)
  rw [Nat.mod_eq_sub_mod mid,Nat.mod_eq_of_lt (show mul a a-v<v by omega)] at rem
  exact ⟨uu,vu,(show mul a a=v by omega)⟩

theorem two_bit_row {m z : Nat} (below : z<m) : DigitRow (2^m) z 1 := by
  let v := 2^m
  let u := 2^z
  obtain ⟨low,high,square⟩ := two_bit_products below
  change mul u (v+u)=0 at low
  change mul v (v+u)=u at high
  change mul (v+u) (v+u)=v at square
  apply (digit_row_iff_predecessors _ _ _).mpr
  constructor
  · intro i r fit
    change r+1<2 at fit
    have eqv : r=0 := by omega
    subst r
    change mul (mul (2^m+1) i+u*1) (v+u*1)=mul (2^m+1) i+u*0
    rw [single_bit_output,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    change mul (v*(i%2)+u) (v+u)=v*(i%2)
    rcases Nat.mod_two_eq_zero_or_one i with even|odd
    · rw [even,Nat.mul_zero,Nat.zero_add]; exact low
    · rw [odd,Nat.mul_one]; exact square
  · intro i
    change mul (mul (2^m+1) (i+1)) (v+u*1)=mul (2^m+1) i+u*1
    rw [single_bit_output,single_bit_output,Nat.mul_one]
    change mul (v*((i+1)%2)) (v+u)=v*(i%2)+u
    rcases Nat.mod_two_eq_zero_or_one i with even|odd
    · rw [even,show (i+1)%2=1 by omega,Nat.mul_one,Nat.mul_zero,Nat.zero_add]; exact high
    · rw [odd,show (i+1)%2=0 by omega,Nat.mul_zero,Nat.mul_one,mul_zero_left]

theorem width_one {X z l : Nat} (aligned : 2^(z+1) ∣ X) (per : PeriodExp (X+1) l) (bound : l≤1) :
    DigitRow X z 1 := by
  by_cases zero : X=0
  · subst X; exact zero_background_row (show IsDyadic 1 from ⟨0,rfl⟩) (Nat.one_dvd _)
  · have two : mul (X+1) 2=0 := (per 1).mpr bound
    have p := power_from_column (K:=2) two 2 (Nat.le_refl _)
    change mul (mul 0 X) X=mul (X+1) 0 at p
    rw [mul_zero_left,mul_zero_right] at p
    obtain ⟨m,h⟩ := (square_zero_iff_power (Nat.pos_of_ne_zero zero)).mp p
    subst X
    have lim := Nat.le_of_dvd (Nat.two_pow_pos m) aligned
    apply two_bit_row
    apply Nat.lt_of_not_ge
    intro no
    exact (Nat.not_lt_of_ge lim) (Nat.pow_lt_pow_right (by decide) (show m<z+1 by omega))

#print axioms width_one

/-- After the zero-background and one-bit calculations, only positive
backgrounds and widths of at least two remain. -/
def WidePositiveDigits : Prop := ∀ {X z b l : Nat}, 0<X → 2≤b → IsDyadic b → b ∣ z →
  2^(z+b) ∣ X → PeriodExp (X+1) l → l≤b → DigitRow X z b

theorem full_of_wide_digits (wide : WidePositiveDigits) : FullDigitRow := by
  apply full_of_positive_digits
  intro b z X l positive dy aligned divX per lb
  by_cases large : 2≤b
  · exact wide positive large dy aligned divX per lb
  · have bp : 0<b := by obtain ⟨f,rfl⟩ := dy; exact Nat.two_pow_pos _
    have one : b=1 := by omega
    subst b
    exact width_one divX per lb

#print axioms full_of_wide_digits
end Gamma11.Backward
