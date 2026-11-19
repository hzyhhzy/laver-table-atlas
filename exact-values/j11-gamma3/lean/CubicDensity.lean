import DiagonalDigits
import DenseDigits
import MixedNormal

/-! A nonconstant even input to binary digit repetition gives a
positive aligned background with at least a full digit of ones above
the low block, and with at least one missing high bit. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem count_step (x k : Nat) :
    zeroDigits x (k+1)=zeroDigits x k+(if x.testBit k then 0 else 1) := by
  rw [zeroDigits,next_bit_residue]
  have below := Nat.mod_lt x (Nat.two_pow_pos k)
  cases h : x.testBit k <;> simp [below]

private theorem count_mod {a b n : Nat} (same : a%2^n=b%2^n) : zeroDigits a n=zeroDigits b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zeroDigits,zeroDigits,ih (residue_agree_lower same (Nat.le_succ _)),same]

private theorem count_split (w k x r : Nat) (rf : r<2^w) :
    zeroDigits (2^w*x+r) (w+k)=zeroDigits r w+zeroDigits x k := by
  induction k with
  | zero =>
    change zeroDigits (2^w*x+r) w=zeroDigits r w+0
    exact count_mod (Nat.mul_add_mod _ _ _)
  | succ k ih =>
    rw [show w+(k+1)=w+k+1 by omega,count_step,count_step x k,ih,
      Nat.testBit_two_pow_mul_add x rf,if_neg (Nat.not_lt_of_ge (Nat.le_add_right w k)),Nat.add_sub_cancel_left,
      Nat.add_assoc]

private theorem count_at_most (x k : Nat) : zeroDigits x k≤k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => rw [count_step]; split <;> omega

private theorem count_full (w k : Nat) (small : k≤w) : zeroDigits (2^w-1) k=0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [count_step,ih (by omega),Nat.testBit_two_pow_sub_one]
    simp [show k<w by omega]

private theorem one_full_digit (w k : Nat) {x : Nat} (pos : 0<x) (fit : x<2^k) :
    zeroDigits (repeatBits w k x) (k*w)+w≤k*w := by
  induction k generalizing x with
  | zero => simp at fit; omega
  | succ k ih =>
    have half := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (show x<2^k*2 by rwa [←Nat.pow_succ])
    have power := Nat.two_pow_pos w
    rw [Nat.succ_mul,show k*w+w=w+k*w by omega,repeatBits]
    by_cases even : x%2=0
    · rw [if_pos even,Nat.add_comm 0,count_split _ _ _ 0 power]
      have prior := ih (x:=x/2) (by omega) half
      have cnt := count_at_most 0 w
      omega
    · rw [if_neg even,Nat.add_comm (2^w-1),count_split _ _ _ _ (by omega),count_full _ _ (Nat.le_refl _)]
      have cnt := count_at_most (repeatBits w k (x/2)) (k*w)
      omega

theorem repeated_background {n y : Nat} (width : 2≤n) (pos : 0<y) (even : y%2=0) (fit : y<2^n-2) :
    let A := repeatBits n n y
    let a := 2^n-2
    2^n∣A ∧ 0<A ∧ A+a<2^(n*n)-2 ∧
    zeroDigits (A+a) (n*n)≤zeroDigits (A+a) n+(n-2)*n := by
  let p := 2^n
  let k := n-1
  let z := y/2
  let Z := repeatBits n k z
  let a := p-2
  have base : 4≤p := Nat.pow_le_pow_right (by decide : 0<2) width
  have ks : k+1=n := Nat.sub_add_cancel (by omega : 1≤n)
  have pk : p=2^k*2 := (congrArg (fun i : Nat => 2^i) ks.symm).trans (Nat.pow_succ 2 k)
  have zFit : z+1<2^k := by change y<p-2 at fit; dsimp only [z]; omega
  have word : repeatBits n n y=p*Z := by
    conv => lhs; arg 2; rw [←ks]
    rw [repeatBits,if_pos even,Nat.zero_add]
  have sq : n*n=k*n+n := (congrArg (fun i : Nat => i*n) ks.symm).trans (Nat.succ_mul k n)
  have power : 2^(n*n)=p*2^(k*n) := by rw [sq,Nat.add_comm,Nat.pow_add]
  obtain ⟨B,e,_,_,_,old,next⟩ := repeatBits_carry n k z zFit
  have zRoom := repeatBits_lt n k (z+1)
  rw [next] at zRoom
  change Z=B+2^e-1 at old
  have ep := Nat.two_pow_pos e
  have xp : 1≤p-1 := by omega
  have upto := Nat.mul_le_mul_left (2^e) xp
  rw [Nat.mul_one] at upto
  change B+2^e*(p-1)<2^(k*n) at zRoom
  have high : Z+1<2^(k*n) := by omega
  have widened := Nat.mul_lt_mul_of_pos_left high (Nat.two_pow_pos n)
  rw [Nat.mul_succ] at widened
  have count := one_full_digit n k (x:=z) (by dsimp [z]; omega) (by omega)
  change zeroDigits Z (k*n)+n≤k*n at count
  have factor : (n-2)*n+n=k*n := by rw [←Nat.succ_mul,show (n-2).succ=k by dsimp [k]; omega]
  have zero : 2^n∣repeatBits n n y := word ▸ Nat.dvd_mul_right ..
  have pA := repeatBits_pos (by omega : 0<n) pos (show y<2^n by omega)
  refine ⟨zero,pA,?_,?_⟩
  · rw [word,power]
    change p*Z+(p-2)<p*2^(k*n)-2
    change p*Z+p<p*2^(k*n) at widened
    omega
  · change zeroDigits (repeatBits n n y+a) (n*n)≤zeroDigits (repeatBits n n y+a) n+(n-2)*n
    rw [word,show n*n=n+k*n by omega,count_split n (k*n) Z a (by dsimp [a]; omega)]
    have low := count_mod (Nat.mul_add_mod (2^n) Z a)
    change zeroDigits (p*Z+a) n=zeroDigits a n at low
    rw [low]; omega

#print axioms repeated_background
end Gamma11
