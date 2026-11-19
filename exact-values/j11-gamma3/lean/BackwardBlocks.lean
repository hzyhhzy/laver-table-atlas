import BackwardTables
import TailRestore

/-! Translate the period part of Dougherty II, Theorem 4.1, to the
local forward period update. The source row has its genuine least
period, while the forward update is given only an upper bound. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- Equality of the period lengths asserted by Dougherty's subalgebra
isomorphism. The actual reverse operation here is defined by finite
canonical Laver tables. -/
def PeriodCompression : Prop := ∀ {b z X Y l : Nat}, IsDyadic b → b ∣ z →
  2^(z+b) ∣ X → Y<2^b → PeriodExp (X+1) l → l≤b → ∀ k,
  mul (X+2^z*Y+1) (2^k)=0 ↔ mul (2^(l+b)-2^b+Y+1) (2^k)=0

/-- The full-digit formula of Dougherty II, Corollary 4.2. It specifies
one row per aligned background and width. -/
def FullDigitRow : Prop := ∀ {b z X l : Nat}, IsDyadic b → b ∣ z → 2^(z+b) ∣ X →
  PeriodExp (X+1) l → l≤b → ∀ i r, r<2^b →
    mul (X+2^z*(2^b-1)+1) (2^b*i+r)=mul (X+1) i+2^z*r

theorem compression_from_full_digit (full : FullDigitRow) : PeriodCompression := by
  intro b z X Y l dy aligned divX small per lb k
  let p := 2^b
  let F := X+2^z*(p-1)+1
  let M := 2^(l+b)-p+Y
  have pp : 0<p := Nat.two_pow_pos _
  have zeroDigit := full dy aligned divX per lb
  have factor : p*(2^l-1)+Y=M := by
    dsimp [p,M]; rw [Nat.mul_sub,Nat.mul_one,Nat.pow_add,Nat.mul_comm (2^b) (2^l)]
  have rowAt : mul F M=X+2^z*Y := by
    rw [← factor]
    exact (zeroDigit (2^l-1) Y small).trans (by rw [period_last X l per])
  have read := compose_rows F M (2^k)
  rw [rowAt] at read
  rw [read]
  let v := mul (M+1) (2^k)
  have baseEnough := Nat.pow_le_pow_right (by decide : 0<2) (show b≤l+b by omega)
  have vSmall : v<2^(l+b) := by
    have old := mul_lt_left (Nat.zero_lt_succ M) (2^k)
    change v<M+1 at old
    dsimp [M,p] at old
    omega
  have digit : v%p<p := Nat.mod_lt _ pp
  have high : v/p<2^l := (Nat.div_lt_iff_lt_mul pp).mpr (by rwa [Nat.pow_add] at vSmall)
  change mul F v=0 ↔ v=0
  constructor
  · intro h
    have parts := zeroDigit (v/p) (v%p) digit
    change mul F (p*(v/p)+v%p)=mul (X+1) (v/p)+2^z*(v%p) at parts
    rw [Nat.div_add_mod,h] at parts
    have van : mul (X+1) (v/p)=0 := by omega
    have hh := (zero_iff_period (Nat.zero_lt_succ _) per _).mp van
    rw [Nat.mod_eq_of_lt high] at hh
    have bottom : v%p=0 := by
      apply Nat.eq_zero_of_not_pos
      intro nonzero
      have lower := Nat.mul_pos (Nat.two_pow_pos z) nonzero
      omega
    have split := Nat.div_add_mod v p
    rw [hh,bottom,Nat.mul_zero,Nat.zero_add] at split
    exact split.symm
  · intro h; rw [h,mul_zero_right]

theorem mixed_model {b l Y : Nat} (dy : IsDyadic b) (fits : l≤b) (gap : Y+1<2^b) :
    mul (2^(l+b)-2^b+Y+1) (2^b)=0 := by
  obtain ⟨e,rfl⟩ := dy
  let b := 2^e
  have small := Nat.pow_le_pow_right (by decide : 0<2) (show b≤l+b by omega)
  have upper := Nat.pow_le_pow_right (by decide : 0<2) (show l+b≤2*b by omega)
  have multiple := Nat.dvd_sub (Nat.pow_dvd_pow 2 (show b≤l+b by omega)) (Nat.dvd_refl (2^b))
  apply two_block_period (e:=e)
  · change 2^(l+b)-2^b+Y+1<2^(2*b)
    change Y+1<2^b at gap
    omega
  · rw [Nat.add_assoc,Nat.add_mod,Nat.mod_eq_zero_of_dvd multiple,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt gap]
    omega

private theorem shift_normalized (d A u k : Nat) :
    act tables d (A%2^d+u) k=act tables d (A+u) k := by
  unfold act
  apply congrArg (signature d)
  calc
    _ = (tables d).mul ((A%2^d+u)%2^d) (2^k) := ((tables d).mul_mod_left _ _).symm
    _ = _ := by rw [Nat.mod_add_mod,(tables d).mul_mod_left]

theorem restore_of_period_compression (zip : PeriodCompression) : RestoreBlockLaw := by
  intro d z b q A y dy aligned fits divides qb low old
  let U := 2^d
  let Q := 2^(z+b)
  let a := A%U
  let X := U-(a+Q)
  let Y := 2^b-1-y
  have bPos : 0<b := by obtain ⟨e,rfl⟩ := dy; exact Nat.two_pow_pos _
  have block : Q∣U := Nat.pow_dvd_pow 2 fits
  have alignedA : Q∣a := (Nat.dvd_mod_iff block).mpr divides
  have aSmall : a<U := Nat.mod_lt _ (Nat.two_pow_pos d)
  have room := Nat.le_of_dvd (Nat.sub_pos_of_lt aSmall) (Nat.dvd_sub block alignedA)
  have sum : X+(a+Q)=U := by dsimp [X]; omega
  have ample : 1<Q := Nat.one_lt_two_pow (by omega : z+b≠0)
  have alignX : Q∣X := Nat.dvd_sub block (Nat.dvd_add alignedA (Nat.dvd_refl Q))
  have oldAt : act tables d (a+(Q-1)) q=d := (shift_normalized d A (Q-1) q).trans old
  have oldOpp : X+1+(a+(Q-1))=U := by omega
  have initial : mul (X+1) (2^q)=0 := of_forward_zero (Nat.zero_lt_succ _)
    (show X+1<U by omega) (oldOpp ▸ Nat.mod_self U) oldAt
  obtain ⟨l,expo⟩ := has_period_exp (Nat.zero_lt_succ X)
  have lq := (expo q).mp initial
  have yFit : Y<2^b := by dsimp [Y]; omega
  have sumY : Y+y+1=2^b := by dsimp [Y]; omega
  have lowSum := congrArg (fun v => 2^z*v) sumY
  change 2^z*(Y+y+1)=2^z*2^b at lowSum
  rw [Nat.mul_succ,Nat.mul_add,← Nat.pow_add] at lowSum
  change 2^z*Y+2^z*y+2^z=Q at lowSum
  have posZ := Nat.two_pow_pos z
  have newOpp : X+2^z*Y+1+(a+(2^z*y+(2^z-1)))=U := by omega
  have mapped := zip dy aligned alignX yFit expo (Nat.le_trans lq qb)
  have model : mul (2^(l+b)-2^b+Y+1) (2^(if y=0 then q+b else b))=0 := by
    by_cases zero : y=0
    · have ge := Nat.pow_le_pow_right (by decide : 0<2) (show b≤l+b by omega)
      have same : 2^(l+b)-2^b+Y+1=2^(l+b) := by omega
      rw [if_pos zero,same]
      exact zero_at_width (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [if_neg zero]
      exact mixed_model dy (Nat.le_trans lq qb) (by omega)
  have divNew : (X+2^z*Y+1+(a+(2^z*y+(2^z-1))))%2^d=0 := by rw [newOpp,Nat.mod_self]
  have newAt := to_forward_zero divNew ((mapped _).mpr model)
  rw [Nat.add_assoc A,← shift_normalized d A]
  exact newAt

#print axioms restore_of_period_compression

theorem restore_of_full_digit (full : FullDigitRow) : RestoreBlockLaw :=
  restore_of_period_compression (compression_from_full_digit full)

#print axioms restore_of_full_digit
end Gamma11.Backward
