import DiagonalHom

/-! One ordinary table lift, with either constant or doubled period.
The new high output bit is specified for all columns. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

def RowLiftsAtBit (F : BinaryFamily) (t a k : Nat) : Prop := ∀ y,
  (F (t+1)).mul a y=(F t).mul a y + (if y.testBit k then 2^t else 0)

theorem first_zero_from_half (F : BinaryFamily) {t a k : Nat}
    (endAt : (F t).mul a (2^(k+1))=0) (middle : (F t).mul a (2^k)≠0) :
    (F t).FirstZero a (2^(k+1)) := by
  obtain ⟨p,per⟩ := (F t).exists_firstZero a
  obtain ⟨e,_,rfl⟩ := period_is_power_two F t a p per
  have upper := (pow_mod_zero_iff _ _).mp (((F t).firstZero_iff_mod per _).mp endAt)
  have lower : k<e := by
    apply Nat.lt_of_not_ge; intro le
    exact middle (((F t).firstZero_iff_mod per _).mpr ((pow_mod_zero_iff _ _).mpr le))
  rwa [show k+1=e by omega]

theorem row_lifts_at_bit (F : BinaryFamily) {t a k : Nat}
    (per : (F (t+1)).FirstZero a (2^(k+1)))
    (below : ∀ j, j<2^k → (F (t+1)).mul a j<2^t)
    (atHalf : 2^t≤(F (t+1)).mul a (2^k)) : RowLiftsAtBit F t a k := by
  intro y
  let r := y%2^(k+1)
  have rf : r<2^(k+1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have rep : (F (t+1)).mul a y=(F (t+1)).mul a r := (F (t+1)).reduce_period per.2.1 y
  have bit : r.testBit k=y.testBit k := by simp [r,Nat.testBit_mod_two_pow]
  have pr := (F (t+1)).projection (F t) (Nat.pow_dvd_pow 2 (Nat.le_succ t)) a y
  have room := (F (t+1)).mul_lt a y
  have size : 2^(t+1)=2^t*2 := Nat.pow_succ ..
  by_cases low : r<2^k
  · have atY : y.testBit k=false := bit.symm.trans (Nat.testBit_lt_two_pow low)
    have old := below r low
    rw [←rep] at old
    rw [Nat.mod_eq_of_lt old] at pr
    simpa only [atY,Bool.false_eq_true,if_false,Nat.add_zero] using pr
  · have large : 2^k≤r := by omega
    have atY := bit.symm.trans (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt large rf)
    have raised : 2^t≤(F (t+1)).mul a r := by
      rcases Nat.eq_or_lt_of_le large with same|lt
      · exact same ▸ atHalf
      · exact Nat.le_trans atHalf (Nat.le_of_lt ((F _).firstZero_strict per (Nat.two_pow_pos k) lt rf))
    rw [←rep] at raised
    rw [Nat.mod_eq_sub_mod raised,Nat.mod_eq_of_lt (show (F (t+1)).mul a y-2^t<2^t by omega)] at pr
    rw [atY]; simp only [if_true]; omega

theorem stable_period_lift (F : BinaryFamily) {t a k : Nat} (kt : k≤t)
    (old : (F t).FirstZero a (2^(k+1))) (stays : (F (t+1)).mul a (2^(k+1))=0)
    (early : ∀ j, j<2^k → (F (t+1)).mul a j<2^t) : RowLiftsAtBit F t a k := by
  have src := old.2.2 _ (Nat.two_pow_pos k) (Nat.pow_lt_pow_succ (by decide))
  have proj := (F (t+1)).projection (F t) (Nat.pow_dvd_pow 2 (Nat.le_succ t)) a (2^k)
  have nz : (F (t+1)).mul a (2^k)≠0 := by
    intro h; rw [h,Nat.zero_mod] at proj; exact src proj.symm
  have sharp := first_zero_from_half F stays nz
  apply row_lifts_at_bit F sharp early
  apply Nat.le_of_not_gt; intro small
  have hit := (lift_iff_lower_midpoint F t a k kt old.2.1).mpr ⟨Nat.pos_of_ne_zero nz,small⟩
  rw [stays] at hit; exact Nat.ne_of_gt (Nat.two_pow_pos t) hit.symm

theorem doubled_period_lift (F : BinaryFamily) {t a k : Nat} (kt : k≤t)
    (old : (F t).FirstZero a (2^(k+1)))
    (mid : 0<(F (t+1)).mul a (2^k) ∧ (F (t+1)).mul a (2^k)<2^t) :
    RowLiftsAtBit F t a (k+1) := by
  have hit := (lift_iff_lower_midpoint F t a k kt old.2.1).mpr mid
  have endAt := double_zero F t a (2^(k+1)) old.2.1
  rw [Nat.mul_comm,←Nat.pow_succ] at endAt
  have whole := first_zero_from_half F endAt (show (F (t+1)).mul a (2^(k+1))≠0 by
    rw [hit]; exact Nat.ne_of_gt (Nat.two_pow_pos t))
  apply row_lifts_at_bit F whole _ (Nat.le_of_eq hit.symm)
  intro j jp
  rcases Nat.eq_zero_or_pos j with rfl|pos
  · rw [(F _).mul_zero]; exact Nat.two_pow_pos _
  · rw [←hit]
    exact (F _).firstZero_strict whole pos jp (Nat.pow_lt_pow_succ (by decide))

/-- The whole diagonal homomorphism follows from the one geometric
row at the old degree, by left distributivity and projection. -/
theorem diagonal_hom_of_row {N t : Nat} (within : N≤t)
    (row : ∀ y, (tables t).mul (2^N-3) y=diagonalWord N (y%2^N)) : DiagonalHomAt N t := by
  intro a b af bf
  let g := 2^N-3
  have proj := (tables t).projection (tables N) (Nat.pow_dvd_pow 2 within) a b
  calc
    diagonalWord N ((tables N).mul a b)=(tables t).mul g ((tables t).mul a b) := by rw [row,proj]
    _=(tables t).mul ((tables t).mul g a) ((tables t).mul g b) := (tables t).mul_distrib ..
    _=_ := by rw [row,row,Nat.mod_eq_of_lt af,Nat.mod_eq_of_lt bf]

#print axioms doubled_period_lift
#print axioms diagonal_hom_of_row
end Gamma11
