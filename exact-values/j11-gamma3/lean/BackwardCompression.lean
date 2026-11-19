import BackwardTransfer

/-! The full induction of Dougherty II, Theorem 4.1 for ordinary
finite Laver tables, expressed in the stable backward numbering. -/
set_option autoImplicit false
namespace Gamma11.Backward

theorem model_right_from_power {b l Y m : Nat} (mp : 0<m) (yFit : Y<2^b) (fits : m≤modelGenerator b l Y) :
    mul m (modelGenerator b l Y)=powers (m-1) (2^b-Y) := by
  let K := 2^(l+b)
  let p := 2^b
  have kp : 0<K := Nat.two_pow_pos _
  have pk : p≤K := Nat.pow_le_pow_right (by decide) (Nat.le_add_left b l)
  have mf : m<K := Nat.lt_of_le_of_lt fits (model_fits yFit)
  have head : K-1+1=K := Nat.sub_add_cancel kp
  have row (i : Nat) : mul (K-1+1) i=i%K := by rw [head,power_row]
  have zero : mul (K-1+1) K=0 := (row K).trans (Nat.mod_self _)
  have pow := power_from_column zero (p-Y) (show p-Y≤K by omega)
  rw [row,Nat.mod_eq_of_lt (Nat.sub_lt kp (Nat.sub_pos_of_lt yFit))] at pow
  have value : powers (K-1) (p-Y)=modelGenerator b l Y := by
    rw [pow]; change K-(p-Y)=K-p+Y; change Y<p at yFit; omega
  have last := previous_column (m-1) (K-1)
  rw [Nat.sub_add_cancel mp,head,zero_at_width mp (Nat.le_of_lt mf),mul_zero_left] at last
  rw [←value,map_powers,last]

private theorem next_compressed {L X z b l Y : Nat} (ih : RowsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (yFit : Y<2^b) (eqv : X+2^z*Y=L) (xp : 0<X) (yp : 0<Y) (i : Nat)
    (prev : mul (L+1) (i+1)=encodeDigit X z b (mul (modelGenerator b l Y+1) (i+1))) :
    mul (L+1) i=encodeDigit X z b (mul (modelGenerator b l Y+1) i) := by
  let P := modelGenerator b l Y
  let m := mul (P+1) (i+1)
  let E := encodeDigit X z b
  let F := X+2^z*(2^b-1)
  let d := 2^b-Y
  have smallM : m≤P := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ P) _)
  have pFit : P<2^(l+b) := model_fits yFit
  have mFit := Nat.lt_of_le_of_lt smallM pFit
  have pVal : E P=L := (encoded_model per yFit).trans eqv
  have mL := Nat.le_trans smallM (Nat.le_trans (encode_dominates dX per pFit) (Nat.le_of_eq pVal))
  have outRoom : E m≤L := Nat.le_trans (Nat.le_of_eq prev.symm) (Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ L) _))
  have eZero : E 0=0 := by simp [E,encodeDigit,mul_zero_right]
  have step : mul (E m) L=E (mul m P) := by
    by_cases empty : m=0
    · rw [empty,eZero,mul_zero_left,mul_zero_left,pVal]
    have mp := Nat.pos_of_ne_zero empty
    have ap := Nat.lt_of_lt_of_le mp (encode_dominates dX per mFit)
    have positive := Nat.mul_pos (Nat.two_pow_pos z) yp
    have below : X<L := by omega
    have old := predecessor_on_code ih dy dz dX per lb below mp outRoom
    change mul (E m) F=E (m-1) at old
    have reduced : E (m-1)<L := Nat.lt_of_lt_of_le (old ▸ mul_lt_left ap F) outRoom
    have move := mixed_right_from_power (local_full ih) dy dz dX per lb xp (Nat.le_of_lt below) yFit ap
      (eqv ▸ outRoom)
    calc
      mul (E m) L=powers (mul (E m) F) d := eqv ▸ move
      _=powers (E (m-1)) d := by rw [old]
      _=E (powers (m-1) d) := smaller_encoded_power ih dy dz dX per lb (by omega) reduced (by omega) d
      _=E (mul m P) := congrArg E (model_right_from_power mp yFit smallM).symm
  calc
    mul (L+1) i=mul (mul (L+1) (i+1)) L := previous_column L i
    _=mul (E m) L := by rw [prev]
    _=E (mul m P) := step
    _=E (mul (P+1) i) := congrArg E (previous_column P i).symm

private theorem compressed_at {L X z b l Y : Nat} (ih : RowsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (yFit : Y<2^b) (eqv : X+2^z*Y=L) : CompressedRow X z b l Y := by
  by_cases base : X=0
  · subst X; exact zero_base_compressed dy dz per yFit
  by_cases zero : Y=0
  · subst Y; exact zero_digit_compressed dy per lb
  intro i
  let P := modelGenerator b l Y
  let s := L+P+i+2
  let K := 2^s
  have room : s<K := Nat.lt_two_pow_self
  have large : L+1≤s ∧ P+1≤s ∧ i≤s := by dsimp [s]; omega
  have before : i≤K := Nat.le_trans large.2.2 (Nat.le_of_lt room)
  have first := zero_at_width (Nat.zero_lt_succ L) (Nat.le_trans large.1 (Nat.le_of_lt room))
  have other := zero_at_width (Nat.zero_lt_succ P) (Nat.le_trans large.2.1 (Nat.le_of_lt room))
  have descend (j : Nat) (fit : j≤K) :
      mul (L+1) (K-j)=encodeDigit X z b (mul (P+1) (K-j)) := by
    induction j with
    | zero =>
      change mul (L+1) (2^s)=encodeDigit X z b (mul (P+1) (2^s))
      rw [first,other]; simp [encodeDigit,mul_zero_right]
    | succ j prev =>
      apply next_compressed ih dy dz dX per lb yFit eqv (Nat.pos_of_ne_zero base) (Nat.pos_of_ne_zero zero)
      rw [show K-(j+1)+1=K-j by omega]
      exact prev (by omega)
  have finalEq := descend (K-i) (Nat.sub_le _ _)
  rwa [show K-(K-i)=i by omega,←eqv] at finalEq

theorem compression_at_every_generator {X z b l Y : Nat} (dy : IsDyadic b) (dz : b∣z) (dX : 2^(z+b)∣X)
    (per : PeriodExp (X+1) l) (lb : l≤b) (yFit : Y<2^b) : CompressedRow X z b l Y := by
  have allAt (L : Nat) : ∀ {X z b l Y : Nat}, IsDyadic b → b∣z → 2^(z+b)∣X →
      PeriodExp (X+1) l → l≤b → Y<2^b → X+2^z*Y=L → CompressedRow X z b l Y := by
    induction L using Nat.strongRecOn with
    | ind L ih =>
      intro X z b l Y dy dz dX per lb fit atL
      apply compressed_at _ dy dz dX per lb fit atL
      intro A t n q r nd nt divA pa cap rf before
      exact ih _ before nd nt divA pa cap rf rfl
  exact allAt _ dy dz dX per lb yFit rfl

theorem finite_full_digit : FullDigitRow := by
  intro b z X l dy dz dX per lb
  apply local_full (L:=X+2^z*(2^b-1)+1) _ dy dz dX per lb (Nat.lt_succ_self _)
  intro _ _ _ _ _ dy' dz' dX' per' lb' fit _
  exact compression_at_every_generator dy' dz' dX' per' lb' fit

theorem finite_restoration : RestoreBlockLaw := restore_of_full_digit finite_full_digit

#print axioms compression_at_every_generator
#print axioms finite_restoration
end Gamma11.Backward
