import BackwardTail

/-! Local consequences of the induction on the generator in
Dougherty II §4. The mixed digit and full digit may come from the
same background. It is the whole generator which must decrease. -/
set_option autoImplicit false
namespace Gamma11.Backward

def modelGenerator (b l Y : Nat) := 2^(l+b)-2^b+Y

def encodeDigit (X z b t : Nat) := mul (X+1) (t/2^b)+2^z*(t%2^b)

def CompressedRow (X z b l Y : Nat) : Prop := ∀ i,
  mul (X+2^z*Y+1) i=encodeDigit X z b (mul (modelGenerator b l Y+1) i)

def RowsBelow (L : Nat) : Prop := ∀ {X z b l Y}, IsDyadic b → b ∣ z → 2^(z+b) ∣ X →
  PeriodExp (X+1) l → l≤b → Y<2^b → X+2^z*Y<L → CompressedRow X z b l Y

theorem model_full {b l : Nat} : modelGenerator b l (2^b-1)+1=2^(l+b) := by
  have room := Nat.pow_le_pow_right (by decide : 0<2) (show b≤l+b by omega)
  have pos := Nat.two_pow_pos b
  unfold modelGenerator; omega

theorem local_full {L : Nat} (earlier : RowsBelow L) : FullDigitsBelow L := by
  intro X z b l dy dz dX per lb cut i r low
  let p := 2^b
  have pos : 0<p := Nat.two_pow_pos b
  have large : 0<2^l := Nat.two_pow_pos _
  have parts := earlier dy dz dX per lb (show p-1<2^b by change p-1<p; omega) cut (p*i+r)
  rw [model_full,power_row] at parts
  have modEq : (p*i+r)%2^(l+b)=p*(i%2^l)+r := by
    rw [Nat.add_comm l b,Nat.pow_add,Nat.mod_mul,Nat.mul_add_mod,Nat.mod_eq_of_lt low,
      Nat.mul_add_div pos,Nat.div_eq_of_lt low,Nat.add_zero]
    exact Nat.add_comm .. 
  rw [encodeDigit,modEq,Nat.mul_add_div pos,Nat.div_eq_of_lt low,Nat.add_zero,Nat.mul_add_mod,
    Nat.mod_eq_of_lt low] at parts
  exact parts.trans (congrArg (fun v => v+2^z*r) (row_congr (Nat.zero_lt_succ _) per (Nat.mod_mod ..)))

theorem local_mixed {L X z b l Y : Nat} (earlier : RowsBelow L) (dy : IsDyadic b)
    (dz : b∣z) (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (gap : Y+1<2^b) (cut : X+2^z*Y<L) : mul (X+2^z*Y+1) (2^b)=0 := by
  have row := earlier dy dz dX per lb (show Y<2^b by omega) cut (2^b)
  have model := mixed_model dy lb gap
  change mul (modelGenerator b l Y+1) (2^b)=0 at model
  simpa only [model,encodeDigit,Nat.zero_div,Nat.zero_mod,mul_zero_right,Nat.mul_zero,Nat.add_zero] using row

def MixedCapsBelow (L : Nat) : Prop := ∀ {A z b l r}, IsDyadic b → b∣z → 2^(z+b)∣A →
  PeriodExp (A+1) l → l≤b → r+1<2^b → A+2^z*r<L → mul (A+2^z*r+1) (2^b)=0

theorem inner_step_of_caps {L A X z b l r : Nat} (full : FullDigitsBelow L) (caps : MixedCapsBelow L) (dy : IsDyadic b)
    (dz : b∣z) (dA : 2^(z+b)∣A) (dX : 2^(z+b)∣X) (per : PeriodExp (A+1) l) (lb : l≤b)
    (small : r+1<2^b) (cut : A+2^z*(r+1)≤L) :
    mul (A+2^z*(r+1)) (X+2^z*(2^b-1))=A+2^z*r := by
  let a := A+2^z*r
  let p := 2^b
  have pos : 0<p := Nat.two_pow_pos b
  have zp := Nat.two_pow_pos z
  have next : a+2^z=A+2^z*(r+1) := by rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_assoc ..
  have kill := caps dy dz dA per lb small (show a<L by omega)
  obtain ⟨h,period⟩ := has_period_exp (Nat.zero_lt_succ a)
  have hb := (period b).mp kill
  have fits : 2^z∣a := Nat.dvd_add (Nat.dvd_trans
    (Nat.pow_dvd_pow 2 (Nat.le_add_right z b)) dA) (Nat.dvd_mul_right ..)
  have tail := lower_tail_row full z (X:=a) (l:=h) (by omega) fits period ⟨b,dy,hb,dz⟩
  obtain ⟨t,Xt⟩ := dX
  have splitInput : X+2^z*(p-1)=2^z*(p*t+(p-1))+0 := by
    rw [Xt,Nat.pow_add,Nat.mul_assoc,Nat.mul_add,Nat.add_zero]
  let y := p*t+(p-1)
  have followed : y+1=p*(t+1) := by dsimp only [y]; rw [Nat.mul_succ]; omega
  have divisor : 2^h ∣ y+1 := followed ▸ Nat.dvd_trans (Nat.pow_dvd_pow 2 hb) (Nat.dvd_mul_right ..)
  have zero := (zero_iff_period (Nat.zero_lt_succ a) period _).mpr (Nat.mod_eq_zero_of_dvd divisor)
  have prev := previous_column a y
  rw [zero,mul_zero_left] at prev
  rw [← next,splitInput,tail _ _ zp,Nat.add_zero]
  exact prev

theorem inner_step_below {L A X z b l r : Nat} (earlier : RowsBelow L) (dy : IsDyadic b)
    (dz : b∣z) (dA : 2^(z+b)∣A) (dX : 2^(z+b)∣X) (per : PeriodExp (A+1) l) (lb : l≤b)
    (small : r+1<2^b) (cut : A+2^z*(r+1)≤L) :
    mul (A+2^z*(r+1)) (X+2^z*(2^b-1))=A+2^z*r :=
  inner_step_of_caps (local_full earlier) (fun dy dz dA per lb rFit cut => local_mixed earlier dy dz dA per lb rFit cut)
    dy dz dA dX per lb small cut

#print axioms local_full
#print axioms inner_step_below
end Gamma11.Backward
