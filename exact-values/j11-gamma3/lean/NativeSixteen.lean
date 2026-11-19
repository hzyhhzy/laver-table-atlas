import MixedNormal

/-! The initial degree 256 of the mixed-block induction. The concrete
source points for rows 13 and 14 give an independent proof of the
width-16 instance of Dougherty II, 7.2(b), shift zero. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem linear16 {a : Nat} (start : act tables 256 a 0=0) (one : 16≤act tables 256 a 1) :
    act tables 256 a 16=256 := by
  apply Nat.le_antisymm (act_le ..)
  apply Nat.le_of_not_gt; intro vis
  have grow := linear_growth tables 256 a 16 vis
  rw [start,Nat.sub_zero,Nat.zero_add] at grow
  have min := Nat.mul_le_mul_right 16 one
  omega

private theorem exponential_two {a : Nat} (start : act tables 256 a 0=1) (one : 16≤act tables 256 a 1) :
    act tables 256 a 2=256 := by
  apply Nat.le_antisymm (act_le ..)
  apply Nat.le_of_not_gt; intro vis
  have grow := exponential_growth tables 256 a 2 start vis
  have min := Nat.pow_le_pow_left one 2
  omega

private theorem at_four {a : Nat} (four : act tables 256 14 4=16) (sig : signature 256 a=4)
    (jump : 16≤act tables 256 a 4) : act tables 256 a 16=256 := by
  let p := (tables 256).mul a 14
  have fix1 := fixes_below_signature tables 256 a 1 (by omega)
  have s14 : signature 256 14=1 := signature_lift (by decide : 2≤256) (by decide : signature 2 14<2)
  have sigp : signature 256 p=1 :=
    (signature_mul tables 256 a 14).trans ((congrArg (act tables 256 a) s14).trans fix1)
  have zero := fixes_below_signature tables 256 p 0 (by omega)
  have t1 := act_from_low tables 256 14 1 _ 4 (by decide) (LowProducts.v14_2 _) (by decide) (by decide)
  have p1 := act_application tables 256 a 14 1
  have p4 := act_application tables 256 a 14 4
  rw [fix1,t1] at p1
  rw [four] at p4
  have sat := linear16 zero (p1.symm ▸ jump)
  have up := act_mono tables 256 p jump
  rw [sat,p4] at up
  exact Nat.le_antisymm (act_le ..) up

private theorem at_two_or_three {a r : Nat} (f13 : act tables 256 13 2=16)
    (sig : signature 256 a=r) (lo : 2≤r) (hi : r≤3) (jump : 16≤act tables 256 a r) :
    act tables 256 a 16=256 := by
  let p := (tables 256).mul a 13
  have fix0 := fixes_below_signature tables 256 a 0 (by omega)
  have fix1 := fixes_below_signature tables 256 a 1 (by omega)
  have c0 := act_from_low tables 256 13 0 _ 1 (by decide) (LowProducts.v13_1 _) (by decide) (by decide)
  have c1 := act_from_low tables 256 13 1 _ 4 (by decide) (LowProducts.v13_2 _) (by decide) (by decide)
  have p0 := act_application tables 256 a 13 0
  have p1 := act_application tables 256 a 13 1
  have p2 := act_application tables 256 a 13 2
  rw [fix0,c0,fix1] at p0
  rw [fix1,c1] at p1
  rw [f13] at p2
  have h4 := Nat.le_trans jump (act_mono tables 256 a (by omega : r≤4))
  have sat := exponential_two p0 (p1.symm ▸ h4)
  have up := act_mono tables 256 p (le_act tables 256 a 2 (by decide))
  change act tables 256 p 2=256 at sat
  rw [sat,p2] at up
  exact Nat.le_antisymm (act_le ..) up

def NativePeriods16 : Prop := ∀ a, 0<a%65536 → a%65536≤65534 → act tables 256 a 16=256

theorem native_periods_16 (four : act tables 256 14 4=16) (f13 : act tables 256 13 2=16) :
    NativePeriods16 := by
  intro a positive upper
  by_cases final : a%65536=65534
  · obtain ⟨sig,reaches⟩ := first_move_from_run tables (by decide : 1<16) (by decide : 16≤256) final
    exact linear16 (fixes_below_signature tables 256 a 0 (by omega)) reaches
  by_cases prior : a%65536=65533
  · obtain ⟨s1,s2⟩ := run_after_zero tables (by decide : 1<16) (by decide : 16≤256) prior
    have cap := exponential_two s1 s2
    have up := act_mono tables 256 a (by decide : 2≤16)
    rw [cap] at up
    exact Nat.le_antisymm (act_le ..) up
  obtain ⟨α,β,c,tr,_,_,lo,small,high,_,_⟩ := cross_sixteen (m:=256) (by decide) positive
    (by change a%65536≤65533; omega) four
  let z := (tables 256).mul a c
  let r := act tables 256 a α
  have sig : signature 256 z=r := (signature_mul tables 256 a c).trans (congrArg (act tables 256 a) tr.1)
  have z1 := act_application tables 256 a c α
  have z2 := act_application tables 256 a c β
  rw [tr.2.1] at z1
  rw [tr.2.2] at z2
  change act tables 256 z r=act tables 256 a β at z1
  have jump : 16≤act tables 256 z r := z1.symm ▸ high
  have cap : act tables 256 z 16=256 := by
    change 0<r at lo
    change r<16 at small
    by_cases large : 4≤r
    · exact critical_four_to_fifteen (by decide) (Nat.le_refl 16) four (fun _ => at_four four)
        r z large small sig jump
    by_cases two : 2≤r
    · exact at_two_or_three f13 sig two (by omega) jump
    have one : r=1 := by omega
    rw [one] at sig jump
    exact linear16 (fixes_below_signature tables 256 z 0 (by omega)) jump
  have up := act_mono tables 256 z high
  rw [cap,z2] at up
  exact Nat.le_antisymm (act_le ..) up

#print axioms native_periods_16
end Gamma11
