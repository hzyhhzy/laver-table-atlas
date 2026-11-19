import EndpointArithmetic
import LaverLowerBounds.LowConstants

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- A row in the upper half of a doubled table is the upper copy of the old
    positive outputs; zeros stay zero. -/
theorem upper_copy {n : Nat} (A : FiniteTable (n * 2)) (B : FiniteTable n)
    {x : Nat} (hx : x < n) (y : Nat) :
    A.mul (n + x) y = if B.mul x y = 0 then 0 else n + B.mul x y := by
  have hmod := A.projection B (show n ∣ n * 2 from ⟨2, rfl⟩) (n + x) y
  have hrow : B.mul (n + x) y = B.mul x y := by
    rw [← B.mul_mod_left (n + x), Nat.add_mod_left, Nat.mod_eq_of_lt hx]
  rw [hrow] at hmod
  rcases A.row_grows (n + x) y (by omega) with hz | hg
  · rw [hz, Nat.zero_mod] at hmod
    simp [hz, ← hmod]
  · have hlt := A.mul_lt (n + x) y
    rw [Nat.mod_eq_sub_mod (by omega : n ≤ A.mul (n + x) y),
      Nat.mod_eq_of_lt (by omega : A.mul (n + x) y - n < n)] at hmod
    rw [if_neg (by omega : B.mul x y ≠ 0)]
    omega

/-- A local computation just one degree above N. Its cost in the proof does
    not depend on the size of the table. -/
theorem row_minus_three_at_two (F : BinaryFamily) (N : Nat) (hN : 2 ≤ N) :
    (F (N + 1)).mul (2 ^ N - 3) 2 = 2 ^ N := by
  let n := 2 ^ N
  have hn : 4 ≤ n := Nat.pow_le_pow_right (by decide : 0 < 2) hN
  have hd : 4 ∣ n := Nat.pow_dvd_pow 2 hN
  have hn4 : n % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
  let A : FiniteTable (n * 2) := F (N + 1)
  let B := F N
  have mid (y : Nat) :
      A.mul n y = if y % n = 0 then 0 else n + y % n := by
    have h := upper_copy A B (x := 0) (by omega) y
    simpa only [Nat.add_zero, B.zero_mul] using h
  have hOne (x : Nat) (hx : x + 1 < n * 2) : A.mul x 1 = x + 1 := by
    rw [A.mul_one, Nat.mod_eq_of_lt hx]
  have lastOne : A.mul (n - 1) 1 = n := by rw [hOne _ (by omega)]; omega
  have lastTwo : A.mul (n - 1) 2 = 0 := by
    rw [A.row_recurrence (n - 1) 1, lastOne, show n - 1 + 1 = n by omega, mid]
    simp
  have beforeOne : A.mul (n - 2) 1 = n - 1 := by rw [hOne _ (by omega)]; omega
  have beforeTwo : A.mul (n - 2) 2 = n := by
    rw [A.row_recurrence (n - 2) 1, beforeOne, show n - 2 + 1 = n - 1 by omega,
      A.reduce_period lastTwo, show (n - 1) % 2 = 1 by omega, lastOne]
  have beforeThree : A.mul (n - 2) 3 = n * 2 - 1 := by
    rw [A.row_recurrence (n - 2) 2, beforeTwo, mid, Nat.mod_eq_of_lt (by omega),
      if_neg (by omega)]
    omega
  have beforeFour : A.mul (n - 2) 4 = 0 := by
    rw [A.row_recurrence (n - 2) 3, beforeThree]
    rcases A.row_grows (n * 2 - 1) (n - 2 + 1) (by omega) with hz | hg
    · exact hz
    · have := A.mul_lt (n * 2 - 1) (n - 2 + 1)
      omega
  change A.mul (n - 3) 2 = n
  rw [A.row_recurrence (n - 3) 1, hOne _ (by omega),
    show n - 3 + 1 = n - 2 by omega, A.reduce_period beforeFour,
    show (n - 2) % 4 = 2 by omega, beforeTwo]

theorem act_of_lower_entry (F : BinaryFamily) {m a x k : Nat} (hm : k + 1 ≤ m)
    (he : (F (k + 1)).mul a (2 ^ x) = 2 ^ k) : act F m a x = k := by
  have hz : (F k).mul a (2 ^ x) = 0 := by
    rw [← (F (k + 1)).projection (F k) (Nat.pow_dvd_pow 2 (Nat.le_succ k)), he,
      Nat.mod_self]
  have hlow := (le_act_iff F m a x k (by omega)).mpr hz
  have hhi : ¬ k + 1 ≤ act F m a x := by
    intro h
    have := (le_act_iff F m a x (k + 1) hm).mp h
    rw [he] at this
    exact (Nat.ne_of_gt (Nat.two_pow_pos k)) this
  omega

private theorem low_Q_fixes_one (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m) :
    act F m ((F m).mul 11 3) 1 = 1 := by
  let q := (F m).mul 11 3
  have h9 : q % 512 = 508 :=
    ((F m).projection (F 9) (Nat.pow_dvd_pow 2 hm) 11 3).trans (LowProducts.v11_3 (F 9))
  have h4 : q % 4 = 0 := by omega
  apply act_of_lower_entry F (k := 1) (by omega)
  change (F 2).mul q 2 = 2
  rw [← (F 2).mul_mod_left q, show q % 2 ^ 2 = 0 from h4, (F 2).zero_mul]

/-- The action identities of G=(11*3)*1 hold whether or not its integer
    representative is known. -/
theorem eleven_actions (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m) :
    let G := (F m).mul ((F m).mul 11 3) 1
    act F m G 0 = 1 ∧ act F m G 1 = act F m 11 2 ∧
      act F m G (act F m 11 2) = act F m 11 3 := by
  let q := (F m).mul 11 3
  have h11zero : act F m 11 0 = 2 := act_from_low F _ _ _ 12 _ hm
    ((F 9).mul_one 11) (by decide) (by decide)
  have h3zero : act F m 3 0 = 2 := act_from_low F _ _ _ 4 _ hm
    ((F 9).mul_one 3) (by decide) (by decide)
  have h11one : act F m 11 1 = 4 := act_from_low F _ _ _ 496 _ hm
    (LowProducts.v11_2 (F 9)) (by decide) (by decide)
  have h3one : act F m 3 1 = 3 := act_from_low F _ _ _ 8 _ hm
    (LowProducts.v3_2 (F 9)) (by decide) (by decide)
  have hjone : act F m 1 1 = 2 := act_from_low F _ _ _ 12 _ hm
    (LowProducts.v1_2 (F 9)) (by decide) (by decide)
  have hjtwo : act F m 1 2 = 4 := act_from_low F _ _ _ 240 _ hm
    (LowProducts.v1_4 (F 9)) (by decide) (by decide)
  have hjzero : act F m 1 0 = 1 := act_from_low F _ _ _ 2 _ hm
    ((F 9).mul_one 1) (by decide) (by decide)
  have hq1 : act F m q 1 = 1 := low_Q_fixes_one F m hm
  have hq0 : act F m q 0 = 0 := by
    have hn := act_strict_below_cap F m q 0 1 (by decide) (by omega)
    omega
  have eq2 := act_application F m 11 3 0
  rw [h11zero, h3zero] at eq2
  have eq4 := act_application F m 11 3 1
  rw [h11one, h3one] at eq4
  have g0 := act_application F m q 1 0
  rw [hq0, hjzero, hq1] at g0
  have g1 := act_application F m q 1 1
  rw [hq1, hjone, eq2] at g1
  have last := act_application F m q 1 2
  rw [eq2, hjtwo, eq4] at last
  exact ⟨g0, g1, last⟩

/-- Under the finite normal form, the traditionally separate value
    f_11(2)=N is a consequence of a local two-entry computation. -/
theorem normal_form_reduction (F : BinaryFamily) (m N : Nat)
    (hm : 9 ≤ m) (hN : 2 ≤ N) (hNm : N + 1 ≤ m)
    (hnf : (F m).mul ((F m).mul 11 3) 1 = 2 ^ N - 3) :
    act F m 11 2 = N ∧ act F m 11 3 = act F m (2 ^ N - 3) N := by
  obtain ⟨_, h1, h3⟩ := eleven_actions F m hm
  rw [hnf] at h1 h3
  have hg1 : act F m (2 ^ N - 3) 1 = N :=
    act_of_lower_entry F hNm (row_minus_three_at_two F N hN)
  have hx := h1.symm.trans hg1
  exact ⟨hx, by rw [hx] at h3; exact h3.symm⟩

end Gamma11
