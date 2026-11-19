import EndpointMidpoint

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem below_cap_input (F : BinaryFamily) {m a x : Nat} (hx : act F m a x < m) :
    x < m := by
  apply Nat.lt_of_not_ge
  intro h
  have h1 := le_act F m a m (Nat.le_refl _)
  have h2 := act_mono F m a h
  omega

private theorem distance (F : BinaryFamily) (m a u v : Nat) (huv : u ≤ v)
    (hv : act F m a v < m) : act F m a u + (v - u) ≤ act F m a v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono := act_mono F m a (Nat.le_succ (u + k))
    have hp : act F m a (u + k) < m := Nat.lt_of_le_of_lt hmono hv
    exact Nat.le_trans (Nat.succ_le_succ (ih (by omega) hp)) (act_next F m a (u + k) hp)

/-- The row 2^r-1 sends the first two indices to r and r+1, provided both
    are visible. In column 2 this is exactly the gap-prefix computation. -/
theorem adjacent_pair (F : BinaryFamily) (m r : Nat) (hr : r + 2 ≤ m) :
    act F m (2 ^ r - 1) 0 = r ∧ act F m (2 ^ r - 1) 1 = r + 1 := by
  have hpos := Nat.two_pow_pos r
  have hsmall : 2 ^ r < 2 ^ (r + 1) := by rw [Nat.pow_succ]; omega
  have hsub : 2 ^ r - 1 + 1 = 2 ^ r := by omega
  constructor
  · apply act_of_lower_entry F (by omega)
    change (F (r + 1)).mul (2 ^ r - 1) 1 = 2 ^ r
    rw [(F _).mul_one, hsub, Nat.mod_eq_of_lt hsmall]
  · apply act_of_lower_entry F hr
    change (F (r + 2)).mul (2 ^ r - 1) 2 = 2 ^ (r + 1)
    rw [(F _).row_recurrence _ 1, (F _).mul_one, hsub,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega : r < r + 2))]
    have h := gap_prefix F (s := r) (m := r + 1) (Nat.lt_succ_self r) (2 ^ r)
      hpos (Nat.le_refl _)
    have he : 2 ^ (r + 1) - 2 ^ r = 2 ^ r := by rw [Nat.pow_succ]; omega
    rw [he] at h
    exact h.trans (by rw [Nat.pow_succ]; omega)

/-- Finite, unsaturated form of the inequality in Dougherty II, Lemma 7.1. -/
theorem linear_growth (F : BinaryFamily) (m a x : Nat) (hx : act F m a x < m) :
    act F m a 0 + (act F m a 1 - act F m a 0) * x ≤ act F m a x := by
  induction x with
  | zero => simp
  | succ x ih =>
    have hsm := below_cap_input F hx
    obtain ⟨h0, h1⟩ := adjacent_pair F m x (by omega)
    let w := (F m).mul a (2 ^ x - 1)
    have left : act F m w (act F m a 0) = act F m a x := by
      rw [act_application, h0]
    have right : act F m w (act F m a 1) = act F m a (x + 1) := by
      rw [act_application, h1]
    have gap := distance F m w (act F m a 0) (act F m a 1)
      (act_mono F m a (by decide)) (right.symm ▸ hx)
    rw [left, right] at gap
    have before := ih (Nat.lt_of_le_of_lt (act_mono F m a (Nat.le_succ x)) hx)
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_right before _) gap

private theorem even_output_of_first_one (F : BinaryFamily) {m a : Nat} (hm : 0 < m)
    (h0 : act F m a 0 = 1) (y : Nat) : act F m ((F m).mul a y) 0 = 0 := by
  have hbase := (le_act_iff F m a 0 1 hm).mp (Nat.le_of_eq h0.symm)
  obtain ⟨p, hp⟩ := (F 1).exists_firstZero a
  have hret : (F 1).mul a y = 0 := by
    have hp1 := (F 1).firstZero_le_of_zero hp (by decide : 0 < 1) hbase
    have pe : p = 1 := by have := hp.1; omega
    apply ((F 1).firstZero_iff_mod hp y).mpr
    rw [pe, Nat.mod_one]
  have hbit := ((F m).projection (F 1) (Nat.pow_dvd_pow 2 hm) a y).trans hret
  apply act_of_lower_entry F (k := 0) hm
  change (F 1).mul ((F m).mul a y) 1 = 1
  rw [← (F 1).mul_mod_left, hbit, (F 1).zero_mul]

/-- Every row with first index 1 has at least exponential unsaturated
    growth, with its second index as the base. -/
theorem exponential_growth (F : BinaryFamily) (m a x : Nat)
    (h0 : act F m a 0 = 1) (hx : act F m a x < m) :
    (act F m a 1) ^ x ≤ act F m a x := by
  induction x with
  | zero => simp [h0]
  | succ x ih =>
    have hs := below_cap_input F hx
    obtain ⟨e0, e1⟩ := adjacent_pair F m x (by omega)
    let w := (F m).mul a (2 ^ x - 1)
    have w0 : act F m w 0 = 0 := even_output_of_first_one F (by omega) h0 _
    have w1 := act_application F m a (2 ^ x - 1) 0
    rw [h0, e0] at w1
    have wx := act_application F m a (2 ^ x - 1) 1
    rw [e1] at wx
    have lin := linear_growth F m w (act F m a 1) (wx.symm ▸ hx)
    rw [w0, Nat.sub_zero, Nat.zero_add, w1, wx] at lin
    have before := ih (Nat.lt_of_le_of_lt (act_mono F m a (Nat.le_succ x)) hx)
    rw [Nat.pow_succ]
    exact Nat.le_trans (Nat.mul_le_mul_right _ before) lin

theorem first_of_minus_three (F : BinaryFamily) (m N : Nat) (hN : 2 ≤ N) (hm : 2 ≤ m) :
    act F m (2 ^ N - 3) 0 = 1 := by
  have h4 : 4 ∣ 2 ^ N := Nat.pow_dvd_pow 2 hN
  have hz := Nat.mod_eq_zero_of_dvd h4
  have hge : 4 ≤ 2 ^ N := Nat.pow_le_pow_right (by decide : 0 < 2) hN
  apply act_of_lower_entry F hm
  change (F 2).mul (2 ^ N - 3) 1 = 2
  rw [(F 2).mul_one]
  change (2 ^ N - 3 + 1) % 4 = 2
  omega

/-- The old-table zero required for the candidate row, uniform in N and m.
    In particular m=256^256 is permitted and no normal form for 11 is used. -/
theorem geometric_row_zero (F : BinaryFamily) (m N x : Nat)
    (hN : 2 ≤ N) (hm : N + 1 ≤ m) (hpow : m ≤ N ^ x) :
    (F m).mul (2 ^ N - 3) (2 ^ x) = 0 := by
  apply (le_act_iff F m _ x m (Nat.le_refl _)).mp
  apply Nat.le_of_not_gt
  intro hlow
  have h0 := first_of_minus_three F m N hN (by omega)
  have h1 : act F m (2 ^ N - 3) 1 = N := act_of_lower_entry F hm (row_minus_three_at_two F N hN)
  have h := exponential_growth F m _ x h0 hlow
  rw [h1] at h
  omega

end Gamma11
