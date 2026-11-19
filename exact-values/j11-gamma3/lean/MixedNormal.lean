import ShiftedCrossing
import LastNormalProduct

/-! The exact remaining odd-carry guards for the square of 65534. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def MixedWidth16 (m : Nat) : Prop := ∀ y, 0<y → y%2=0 → y<65534 →
  ∀ i, 1≤i → i≤65534 → act tables m (repeatBits 16 16 y+i) 16=m

private theorem add_aligned {m a : Nat} (room : 16≤m) (fit : a<2^m) (aligned : 2^16 ∣ a)
    (per : ∀ i, 1≤i → i≤65534 → act tables m (a+i) 16=m) :
    (tables m).mul a 65535=a+65535 := by
  have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt fit) (Nat.dvd_sub (Nat.pow_dvd_pow 2 room) aligned)
  have first : (a+1)%2^16=1 := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd aligned,Nat.zero_add,Nat.mod_mod]
  have calcRow (i : Nat) (bound : i≤65534) : (tables m).mul a (i+1)=a+(i+1) := by
    induction i with
    | zero => exact ((tables m).mul_one a).trans (Nat.mod_eq_of_lt (by omega))
    | succ i ih =>
      have z := (le_act_iff tables m (a+(i+1)) 16 m (Nat.le_refl _)).mp
        (Nat.le_of_eq (per (i+1) (by omega) bound).symm)
      rw [(tables m).row_recurrence a (i+1),ih (by omega),(tables m).reduce_period z (a+1),
        first,(tables m).mul_one,Nat.mod_eq_of_lt (by omega : a+(i+1)+1<2^m),Nat.add_assoc]
  exact calcRow 65534 (Nat.le_refl _)

private theorem odd_form {y : Nat} (even : y%2=0) :
    2^16 ∣ repeatBits 16 16 y ∧ repeatBits 16 16 (y+1)=repeatBits 16 16 y+65535 := by
  have o : (y+1)%2≠0 := by omega
  have same : (y+1)/2=y/2 := by omega
  change (2^16 ∣ ((if y%2=0 then 0 else 2^16-1)+2^16*repeatBits 16 15 (y/2))) ∧
    (if (y+1)%2=0 then 0 else 2^16-1)+2^16*repeatBits 16 15 ((y+1)/2)=
    ((if y%2=0 then 0 else 2^16-1)+2^16*repeatBits 16 15 (y/2))+65535
  rw [if_pos even,if_neg o,same,Nat.zero_add]
  exact ⟨Nat.dvd_mul_right ..,Nat.add_comm ..⟩

theorem square_of_mixed_16 {m : Nat} (room : 256≤m) (mixed : MixedWidth16 m)
    (even : ∀ y, y%2≠0 → y+1<65536 →
      (tables m).mul (repeatBits 16 16 y) 65535=repeatBits 16 16 (y+1)) :
    entry m 65534 65534=2^256-2^16 := by
  have fits (y : Nat) : repeatBits 16 16 y<2^m := Nat.lt_of_lt_of_le (repeatBits_lt 16 16 y)
    (Nat.pow_le_pow_right (by decide : 0<2) room)
  have all (i : Nat) (bound : i+1≤65534) : (tables m).mul 65534 (i+1)=repeatBits 16 16 (i+1) := by
    induction i with
    | zero => rw [(tables m).mul_one,repeatBits_one 16 16 (by decide),Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (by decide : 65534+1<2^256) (Nat.pow_le_pow_right (by decide) room))]
    | succ i ih =>
      rw [(tables m).row_recurrence 65534 (i+1),ih (by omega)]
      by_cases e : (i+1)%2=0
      · obtain ⟨div,step⟩ := odd_form e
        exact (add_aligned (by omega : 16≤m) (fits _) div (mixed (i+1) (by omega) e bound)).trans step.symm
      · exact even (i+1) e (by omega)
  exact (canonical_mul m _ _).symm.trans ((all 65533 (Nat.le_refl _)).trans (by decide))

#print axioms square_of_mixed_16
end Gamma11
