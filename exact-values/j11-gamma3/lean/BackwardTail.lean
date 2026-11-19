import DigitBorrows

/-! The local form of the low-tail induction in Dougherty II, Lemma
4.4. Each full digit used here has generator strictly below L. -/
set_option autoImplicit false
namespace Gamma11.Backward

def FullDigitsBelow (L : Nat) : Prop := ∀ {X z b l}, IsDyadic b → b ∣ z →
  2^(z+b) ∣ X → PeriodExp (X+1) l → l≤b → X+2^z*(2^b-1)<L → DigitRow X z b

theorem period_of_digit_row {X z b l : Nat} (row : DigitRow X z b)
    (per : PeriodExp (X+1) l) : PeriodExp (X+2^z*(2^b-1)+1) (l+b) := by
  intro k
  by_cases fits : b≤k
  · have split : k=b+(k-b) := by omega
    have read := row (2^(k-b)) 0 (Nat.two_pow_pos b)
    simp only [Nat.add_zero,Nat.mul_zero] at read
    rw [← Nat.pow_add,← split] at read
    rw [read,per]; omega
  · have small := Nat.pow_lt_pow_right (by decide : 1<2) (show k<b by omega)
    have read := row 0 (2^k) small
    rw [Nat.mul_zero,Nat.zero_add,mul_zero_right,Nat.zero_add] at read
    have positive := Nat.mul_pos (Nat.two_pow_pos z) (Nat.two_pow_pos k)
    rw [read]; omega

def TailRow (X s : Nat) : Prop := ∀ i r, r<2^s →
  mul (X+2^s) (2^s*i+r)=mul (X+1) i+r

theorem lower_tail_row {L : Nat} (full : FullDigitsBelow L) (s : Nat) {X l : Nat}
    (cut : X+2^s-1<L) (aligned : 2^s ∣ X) (per : PeriodExp (X+1) l)
    (license : ∃ u, IsDyadic u ∧ l≤u ∧ u ∣ s) : TailRow X s := by
  by_cases empty : s=0
  · subst s
    intro i r small
    have zero : r=0 := by simpa only [Nat.pow_zero,Nat.lt_one_iff] using small
    simp [zero]
  obtain ⟨u,⟨e,ue⟩,lu,k,sk⟩ := license
  have up : 0<u := ue ▸ Nat.two_pow_pos e
  have kp : 0<k := by
    apply Nat.pos_of_ne_zero; intro kz; rw [kz,Nat.mul_zero] at sk; exact empty sk
  obtain ⟨f,t,kt⟩ := odd_factor kp
  let b := u*2^f
  let z := (2*b)*t
  have bp : 0<b := Nat.mul_pos up (Nat.two_pow_pos f)
  have dy : IsDyadic b := ⟨e+f,by dsimp [b]; rw [ue,Nat.pow_add]⟩
  have size : s=z+b := by
    rw [sk,kt,← Nat.mul_assoc,Nat.mul_succ,← Nat.mul_assoc,Nat.mul_comm _ 2]
  have smaller : z<s := by omega
  have bz : b∣z := Nat.dvd_trans (Nat.dvd_mul_left b 2) (Nat.dvd_mul_right ..)
  have cap : l≤b := Nat.le_trans lu (Nat.le_of_dvd bp (Nat.dvd_mul_right ..))
  have dual : IsDyadic (2*b) := by
    obtain ⟨g,eqv⟩ := dy
    exact ⟨g+1,by rw [Nat.pow_succ,← eqv,Nat.mul_comm]⟩
  let X' := X+2^z*(2^b-1)
  have zp := Nat.two_pow_pos z
  have pp := Nat.two_pow_pos b
  have product : 2^s=2^z*2^b := by rw [size,Nat.pow_add]
  have whole : X'+2^z=X+2^s := by
    calc
      X'+2^z = X + 2^z*((2^b-1)+1) := by rw [Nat.mul_add,Nat.mul_one]; exact Nat.add_assoc .. 
      _ = X+2^s := by rw [Nat.sub_add_cancel pp,← product]
  have piece := full dy bz (size ▸ aligned) per cap (show X'<L by omega)
  have aligned' : 2^z ∣ X' := Nat.dvd_add
    (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_of_lt smaller)) aligned) (Nat.dvd_mul_right ..)
  have tail := lower_tail_row full z (X:=X') (l:=l+b) (by omega) aligned'
    (period_of_digit_row piece per) ⟨2*b,dual,by omega,Nat.dvd_mul_right ..⟩
  intro i r small
  have hi : r/2^z<2^b := (Nat.div_lt_iff_lt_mul zp).mpr (by rwa [product,Nat.mul_comm] at small)
  have lo := Nat.mod_lt r zp
  have inputs : 2^z*(2^b*i+r/2^z)+r%2^z=2^s*i+r := by
    rw [Nat.mul_add,← Nat.mul_assoc,← product,Nat.add_assoc,Nat.div_add_mod]
  have read := tail (2^b*i+r/2^z) (r%2^z) lo
  rw [whole,inputs,piece _ _ hi,Nat.add_assoc,Nat.div_add_mod] at read
  exact read
termination_by s
decreasing_by exact smaller

#print axioms lower_tail_row
end Gamma11.Backward
