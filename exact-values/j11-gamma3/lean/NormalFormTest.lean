import SpectrumBits

/-! The contradiction in §1 of the normal-form paper. In fact only the
nonzero sixteenth entry is needed. The first entry cannot be revisited after
2^N-16 positions unless the least period divides 16. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem zero_before_first {size a b : Nat} (S : FiniteTable size) (small : a+1 < size)
    (again : S.mul a (b+1) = a+1) : S.mul a b = 0 := by
  rcases S.row_grows a b (by omega) with hz | before
  · exact hz
  · have after := S.row_grows (S.mul a b) (a+1) (S.mul_lt _ _)
    rw [← S.row_recurrence, again] at after
    rcases after with h | h <;> omega

theorem exclude_repeated_first (F : BinaryFamily) {N d q u : Nat}
    (five : 5 ≤ N) (form : u = 2 ^ N - 16) (small : q+1 < 2 ^ d)
    (prefix12 : (F d).mul u 12 = q) (visible : (F d).mul q 16 ≠ 0) :
    (F d).mul u 13 ≠ q+1 := by
  intro same
  have recurrence := (F d).row_recurrence u 12
  rw [prefix12] at recurrence
  have hz := zero_before_first (F d) small (recurrence.symm.trans same)
  obtain ⟨p, hp⟩ := (F d).exists_firstZero q
  obtain ⟨b, _, he⟩ := period_is_power_two F d q p hp
  have pu : p ∣ u := Nat.dvd_of_mod_eq_zero (((F d).firstZero_iff_mod hp u).mp hz)
  have upper : b ≤ 4 := by
    apply Nat.le_of_not_gt; intro high
    have hd32 : 32 ∣ u := Nat.dvd_trans (he ▸ Nat.pow_dvd_pow 2 high) pu
    have m32 : u % 32 = 0 := Nat.mod_eq_zero_of_dvd hd32
    have z32 : 2 ^ N % 32 = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 five)
    have big : 32 ≤ 2 ^ N := Nat.pow_le_pow_right (by decide : 0 < 2) five
    omega
  exact visible (((F d).firstZero_iff_mod hp 16).mpr (Nat.mod_eq_zero_of_dvd (he ▸ Nat.pow_dvd_pow 2 upper)))

/-- If the geometric row takes N to t, the row just before it takes 4 to
t as well. This is proved in the finite table itself, at cap t+1. -/
theorem previous_row_four (F : BinaryFamily) {N d : Nat} (hN : 5 ≤ N) (h9 : 9 ≤ d)
    (cap : N+1 ≤ d) :
    act F d (2 ^ N-4) 4 = act F d (2 ^ N-3) N := by
  let q := 2^N-4
  let g := 2^N-3
  have two : 2 ≤ N := by omega
  have big : 4 ≤ 2 ^ N := Nat.pow_le_pow_right (by decide : 0 < 2) two
  have next : q+1 = g := by dsimp [q,g]; omega
  have below : q+1 < 2^d := Nat.lt_of_lt_of_le
    (show q+1 < 2^N by dsimp [q]; omega) (Nat.pow_le_pow_right (by decide) (by omega))
  have step : (F d).mul q 1 = g := ((F d).mul_one q).trans ((Nat.mod_eq_of_lt below).trans next)
  have div4 : 2^N % 4 = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 two)
  have qlow : q % 4 = 0 := by dsimp [q]; omega
  have q1 : act F d q 1 = 1 := by
    apply act_of_lower_entry F (k := 1) (by omega)
    change (F 2).mul q 2 = 2
    rw [← (F 2).mul_mod_left q, show q % 2^2 = 0 from qlow, (F 2).zero_mul]
  have g1 : act F d g 1 = N := act_of_lower_entry F cap (row_minus_three_at_two F N two)
  have j1 := act_from_low F d 1 1 12 2 h9 (LowProducts.v1_2 (F 9)) (by decide) (by decide)
  have j2 := act_from_low F d 1 2 240 4 h9 (LowProducts.v1_4 (F 9)) (by decide) (by decide)
  have a := act_application F d q 1 1
  rw [q1, step, g1, j1] at a
  have b := act_application F d q 1 2
  rw [step, ← a, j2] at b
  exact b.symm

/-- The finite contradiction used under the equality assumption in the
normal-form proof. `prefix12` is a strictly shorter computation. -/
theorem critical_four_contradiction (F : BinaryFamily) {N t : Nat}
    (hN : 5 ≤ N) (h9 : 9 ≤ t+1) (ht : N ≤ t)
    (prefix12 : (F (t+1)).mul (2^N-16) 12 = 2^N-4)
    (geometric : act F (t+1) (2^N-3) N = t) :
    (F (t+1)).mul (2^N-16) 13 ≠ 2^N-3 := by
  have hfour := (previous_row_four F hN h9 (by omega)).trans geometric
  have visible : (F (t+1)).mul (2^N-4) 16 ≠ 0 := by
    intro zero
    have high := (le_act_iff F (t+1) (2^N-4) 4 (t+1) (Nat.le_refl _)).mpr zero
    omega
  have pos : 4 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ N by omega)
  have sm : 2^N-4+1 < 2^(t+1) := Nat.lt_of_lt_of_le (show 2^N-4+1 < 2^N by omega)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have e : 2^N-3 = 2^N-4+1 := by omega
  rw [e]
  exact exclude_repeated_first F hN rfl sm prefix12 visible

#print axioms critical_four_contradiction
end Gamma11
