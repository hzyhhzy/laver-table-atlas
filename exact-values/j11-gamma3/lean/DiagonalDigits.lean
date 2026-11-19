import GeometricHalf
import BackwardTables

/-! Bits and truncations of the interval word used for the geometric
row at changing finite degrees. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem intervalWord_padding {f : Nat → Nat} (s k n x : Nat) (kn : k≤n) (small : x<2^k) :
    intervalWord f s n x=intervalWord f s k x := by
  induction k generalizing s n x with
  | zero =>
    have empty : x=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)
    rw [empty,intervalWord_zero,intervalWord_zero]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have half : x/2<2^k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rwa [←Nat.pow_succ])
      rw [intervalWord,intervalWord,ih (s+1) n (x/2) (by omega) half]

theorem intervalWord_bound {f : Nat → Nat} (mono : ∀ i j, i≤j → f i≤f j) (s n x : Nat) :
    intervalWord f s n x+2^(f s)≤2^(f (s+n)) := by
  induction n generalizing s x with
  | zero => simp [intervalWord]
  | succ n ih =>
    have base := ih (s+1) (x/2)
    have up := Nat.pow_le_pow_right (by decide : 0<2) (mono s (s+1) (Nat.le_succ _))
    rw [show s+(n+1)=s+1+n by omega,intervalWord]
    split <;> omega

theorem interval_digit_bit {a b t : Nat} (lo : a≤t) (hi : t<b) :
    (2^b-2^a).testBit t=true := by
  have ab : a≤b := by omega
  have eqv : 2^a*(2^(b-a)-1)=2^b-2^a := by
    rw [Nat.mul_sub,Nat.mul_one,←Nat.pow_add,Nat.add_sub_of_le ab]
  rw [←eqv,Nat.testBit_two_pow_mul,Nat.testBit_two_pow_sub_one]
  simp [lo,show t-a<b-a by omega]

theorem intervalWord_bit {f : Nat → Nat} (mono : ∀ i j, i≤j → f i≤f j)
    (s n x i t : Nat) (inside : i<n) (lo : f (s+i)≤t) (hi : t<f (s+i+1)) :
    (intervalWord f s n x).testBit t=x.testBit i := by
  induction n generalizing s x i with
  | zero => omega
  | succ n ih =>
    let h := f (s+1)
    let a := f s
    let tail := intervalWord f (s+1) n (x/2)
    let digit := if x%2=0 then 0 else 2^h-2^a
    have pos := Nat.two_pow_pos h
    have ap := Nat.two_pow_pos a
    have fits : digit<2^h := by dsimp [digit]; split <;> omega
    obtain ⟨q,decomp⟩ := intervalWord_dvd f mono (s+1) n (x/2)
    change tail=2^h*q at decomp
    change (digit+tail).testBit t=x.testBit i
    cases i with
    | zero =>
      change a≤t at lo
      change t<h at hi
      rw [decomp,Nat.add_comm,Nat.testBit_two_pow_mul_add _ fits,if_pos hi,Nat.testBit_zero]
      by_cases e : x%2=0
      · simp [digit,e]
      · have odd : x%2=1 := by omega
        simp [digit,odd,interval_digit_bit lo hi]
    | succ i =>
      have ht : h≤t := Nat.le_trans (mono (s+1) (s+(i+1)) (by omega)) lo
      have same : s+1+i=s+(i+1) := by omega
      have recursive := ih (s+1) (x/2) i (by omega) (by rwa [same]) (by rwa [same])
      rw [Nat.testBit_div_two] at recursive
      calc
        (digit+tail).testBit t=(2^h*q+digit).testBit t := by rw [decomp,Nat.add_comm]
        _=q.testBit (t-h) := by rw [Nat.testBit_two_pow_mul_add _ fits,if_neg (Nat.not_lt_of_ge ht)]
        _=tail.testBit t := by rw [decomp,Nat.testBit_two_pow_mul]; simp [ht]
        _=x.testBit (i+1) := recursive

theorem next_bit_residue (x t : Nat) : x%2^(t+1)=x%2^t+(if x.testBit t then 2^t else 0) := by
  let a := x%2^(t+1)
  have fit : a<2^(t+1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have size : 2^(t+1)=2^t*2 := Nat.pow_succ ..
  have low : a%2^t=x%2^t := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ _))
  have bit : a.testBit t=x.testBit t := by simp [a,Nat.testBit_mod_two_pow]
  by_cases before : a<2^t
  · rw [←bit,Nat.testBit_lt_two_pow before]
    rw [Nat.mod_eq_of_lt before] at low
    exact low
  · rw [←bit,Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_gt before) fit]
    rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt before),Nat.mod_eq_of_lt (show a-2^t<2^t by omega)] at low
    change a=x%2^t+2^t; omega

def GeometricAt (t : Nat) : Prop := ∀ y, (tables t).mul geometricRow y=diagonalWord 256 (y%2^256)%2^t

theorem geometric_step_from_bit {t k : Nat} (old : GeometricAt t) (lift : RowLiftsAtBit tables t geometricRow k)
    (fits : k<256) (lower : 256^k≤t) (upper : t<256^(k+1)) : GeometricAt (t+1) := by
  intro y
  have bit := intervalWord_bit (f:=fun i : Nat => 256^i) (fun _ _ => Nat.pow_le_pow_right (by decide))
    0 256 (y%2^256) k t fits (by simpa only [Nat.zero_add] using lower) (by simpa only [Nat.zero_add] using upper)
  rw [Nat.testBit_mod_two_pow] at bit
  simp only [decide_eq_true fits,Bool.true_and] at bit
  change (diagonalWord 256 (y%2^256)).testBit t=y.testBit k at bit
  rw [lift,old,next_bit_residue (diagonalWord 256 (y%2^256)) t,bit]

theorem geometric_untruncated {t k y : Nat} (old : GeometricAt t) (degree : 256^k≤t)
    (kn : k≤256) (fit : y<2^k) :
    oldEntry t geometricRow y=intervalWord (fun i : Nat => 256^i) 0 k y := by
  have long := Nat.lt_of_lt_of_le fit (Nat.pow_le_pow_right (by decide : 0<2) kn)
  have high := intervalWord_bound (f:=fun i : Nat => 256^i) (fun _ _ => Nat.pow_le_pow_right (by decide)) 0 k y
  simp only [Nat.zero_add,Nat.pow_zero,Nat.pow_one] at high
  have big := Nat.pow_le_pow_right (by decide : 0<2) degree
  change (tables t).mul geometricRow y=_
  rw [old,Nat.mod_eq_of_lt long,diagonalWord,intervalWord_padding 0 k 256 y kn fit,
    Nat.mod_eq_of_lt (show intervalWord (fun i : Nat => 256^i) 0 k y<2^t by omega)]

#print axioms geometric_step_from_bit
end Gamma11
