import MixedInduction
import MixedNormal

/-! A nonconstant fifteen-bit word has both a full and an empty block
after sixteenfold digit repetition.  This supplies the mixed-block
hypothesis for every odd carry in the target square. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem zeros_at_residue {a b n : Nat} (same : a%2^n=b%2^n) :
    zeroDigits a n=zeroDigits b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zeroDigits,zeroDigits,ih (residue_agree_lower same (Nat.le_succ _)),same]

private theorem zeros_le_width (a n : Nat) : zeroDigits a n≤n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [zeroDigits]; split <;> omega

private theorem zeros_above_block (x low k : Nat) (fit : low<65536) :
    zeroDigits (65536*x+low) (16+k)=zeroDigits low 16+zeroDigits x k := by
  induction k with
  | zero =>
    change zeroDigits (65536*x+low) 16=zeroDigits low 16+0
    rw [Nat.add_zero]
    exact zeros_at_residue (Nat.mul_add_mod 65536 x low)
  | succ k ih =>
    have rem := (aligned_add_residue (a:=65536*x) (show 16≤16+(k+1) by omega)
      (show 2^16 ∣ 65536*x from Nat.dvd_mul_right ..) fit).1
    rw [Nat.pow_add,show 2^16=65536 by decide,Nat.mul_mod_mul_left] at rem
    have bit : (65536*x+low)%2^(16+k+1)<2^(16+k) ↔ x%2^(k+1)<2^k := by
      rw [show 16+k+1=16+(k+1) by omega,Nat.pow_add 2 16 (k+1),Nat.pow_add 2 16 k,
        show 2^16=65536 by decide,rem]
      omega
    change zeroDigits (65536*x+low) (16+k)+(if (65536*x+low)%2^(16+k+1)<2^(16+k) then 1 else 0)=
      zeroDigits low 16+(zeroDigits x k+(if x%2^(k+1)<2^k then 1 else 0))
    by_cases lastZero : x%2^(k+1)<2^k
    · rw [ih,if_pos (bit.mpr lastZero),if_pos lastZero,Nat.add_assoc]
    · rw [ih,if_neg (fun h => lastZero (bit.mp h)),if_neg lastZero,Nat.add_assoc]

private theorem zeros_in_repeat {k x : Nat} (pos : 0<x) (fit : x<2^k) :
    zeroDigits (repeatBits 16 k x) (k*16)+16≤k*16 := by
  induction k generalizing x with
  | zero => simp at fit; omega
  | succ k ih =>
    have small := fit
    rw [Nat.pow_succ] at small
    rw [Nat.succ_mul,show k*16+16=16+k*16 by omega,repeatBits]
    by_cases e : x%2=0
    · rw [if_pos e, Nat.add_comm 0, zeros_above_block _ 0 _ (by decide)]
      have prev := ih (x:=x/2) (by omega) (by omega)
      have num : zeroDigits 0 16=16 := by decide
      omega
    · rw [if_neg e, Nat.add_comm (2^16-1), zeros_above_block _ 65535 _ (by decide)]
      have prev := zeros_le_width (repeatBits 16 k (x/2)) (k*16)
      have num : zeroDigits 65535 16=0 := by decide
      omega

theorem mixed_repeat_word {y : Nat} (pos : 0<y) (even : y%2=0) (fit : y<65534) :
    Incomplete16 (repeatBits 16 16 y) := by
  let z := y/2
  have zp : 0<z := by dsimp [z]; omega
  have zr : z+1<2^15 := by change z+1<32768; dsimp [z]; omega
  let Z := repeatBits 16 15 z
  have word : repeatBits 16 16 y=65536*Z := by
    change (if y%2=0 then 0 else 2^16-1)+2^16*Z=65536*Z
    rw [if_pos even,Nat.zero_add]
  have count : zeroDigits Z 240+16≤240 := zeros_in_repeat zp (by omega : z<2^15)
  obtain ⟨B,p,_,_,_,old,next⟩ := repeatBits_carry 16 15 z zr
  have nextFit := repeatBits_lt 16 15 (z+1)
  rw [next] at nextFit
  change Z=B+2^p-1 at old
  have power := Nat.two_pow_pos p
  change B+2^p*65535<2^240 at nextFit
  have high : Z+1<2^240 := by omega
  rw [word]
  constructor
  · have fullCount := zeros_above_block Z 0 240 (by decide)
    rw [Nat.add_zero] at fullCount
    change zeroDigits (65536*Z) 256=zeroDigits 0 16+zeroDigits Z 240 at fullCount
    have lowCount : zeroDigits (65536*Z) 16=zeroDigits 0 16 := by
      apply zeros_at_residue
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right ..)
    unfold Dense16; omega
  · have limit : 65536*Z<2^256-2^16 := by omega
    unfold FullBitBlock
    rw [Nat.mod_eq_of_lt (by omega : 65536*Z<2^256)]
    omega

theorem mixed_width_of_cap {m : Nat} (cap : MixedAt m m) : MixedWidth16 m := by
  intro y pos even fit i lo hi
  have aligned : 2^16 ∣ repeatBits 16 16 y := by
    change 2^16 ∣ ((if y%2=0 then 0 else 2^16-1)+2^16*repeatBits 16 15 (y/2))
    rw [if_pos even,Nat.zero_add]; exact Nat.dvd_mul_right ..
  have rem := (aligned_add_residue (Nat.le_refl 16) aligned (by omega : i<65536)).1
  rw [Nat.mod_eq_zero_of_dvd aligned,Nat.zero_add] at rem
  have mixed := (mixed_aligned_add aligned (by omega : i<65536)).mpr (mixed_repeat_word pos even fit)
  exact Nat.le_antisymm (act_le ..) (cap _ mixed (rem.symm ▸ lo) (rem.symm ▸ hi))

#print axioms mixed_width_of_cap
end Gamma11
