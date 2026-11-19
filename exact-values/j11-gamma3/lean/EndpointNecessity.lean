import CriticalFour

/-! Equality forces the native row in the boundary normal form. This
    implication does not presuppose that the candidate is the real row. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem normal_form_necessary (hT : Target) :
    let d := targetIndex+1
    let G := entry d (entry d 11 3) 1
    G = 2^256-3 ∧ ∀ k, k ≤ 256 → act tables d G k = 256^k := by
  let d := targetIndex+1
  let G := (tables d).mul ((tables d).mul 11 3) 1
  have atEndpoint := (target_iff_act tables).mp hT
  change act tables d 11 3 = targetIndex at atEndpoint
  have targetLarge : 2^4 ≤ targetIndex :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 4 ≤ 2048)
  have large : 9 ≤ d := Nat.le_trans (by decide : 9 ≤ 2^4)
    (Nat.le_trans targetLarge (Nat.le_succ targetIndex))
  have before := second_at_equality tables d large (Nat.lt_succ_self _) atEndpoint
  obtain ⟨start,base,final⟩ := eleven_actions tables d large
  change act tables d G 0 = 1 at start
  change act tables d G 1 = act tables d 11 2 at base
  change act tables d G (act tables d 11 2) = act tables d 11 3 at final
  rw [before] at base final
  rw [atEndpoint, targetIndex_eq] at final
  have visible : 256^256 < d := targetIndex_eq ▸ Nat.lt_succ_self targetIndex
  obtain ⟨native, earlier⟩ := exponential_equality tables start base (by decide : 0 < 256) visible final
  rw [← targetIndex_eq, Nat.mod_eq_of_lt ((tables d).mul_lt _ _)] at native
  simpa only [← canonical_mul, d, G] using And.intro native earlier

/-- Without assuming the normal form, the conjunction of two ordinary
    finite-row tests is necessary and sufficient for the endpoint. -/
theorem target_iff_normal_form_and_midpoint :
    Target ↔
      entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = 2^256-3 ∧
      (0 < entry (targetIndex+1) (2^256-3) (2^255) ∧
        entry (targetIndex+1) (2^256-3) (2^255) < 2^targetIndex) := by
  constructor
  · intro h
    have nf := (normal_form_necessary h).1
    exact ⟨nf, (target_iff_geometric_midpoint nf).mp h⟩
  · rintro ⟨nf,mid⟩
    exact (target_iff_geometric_midpoint nf).mpr mid

/-- Adding a positive multiple of 2^N to the geometric row forces its
    N-th index above N^N whenever that extra part survives in the table. -/
theorem geometric_background_saturates (F : BinaryFamily) {A N t : Nat}
    (two : 2 ≤ N) (within : N ≤ t) (scale : t = N^N)
    (pos : 0 < A) (small : A < 2^t) (aligned : 2^N ∣ A) :
    act F (t+1) (A+(2^N-3)) N = t+1 := by
  let g := 2^N-3
  let a := A+g
  let d := t+1
  have nd : N ≤ d := Nat.le_trans within (Nat.le_succ t)
  have alignment : a % 2^N = g % 2^N := by
    dsimp [a]; rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd aligned, Nat.zero_add, Nat.mod_mod]
  have same (x : Nat) : act F N a x = act F N g x := by
    unfold act
    rw [← (F N).mul_mod_left a, alignment, (F N).mul_mod_left]
  have start : act F d a 0 = 1 := by
    have low := (act_at_smaller_degree F nd a 0).symm.trans
      ((same 0).trans (first_of_minus_three F N N two two))
    omega
  have base : N ≤ act F d a 1 := by
    have g1 : act F d g 1 = N := act_of_lower_entry F (Nat.succ_le_succ within) (row_minus_three_at_two F N two)
    have low := (act_at_smaller_degree F nd a 1).symm.trans ((same 1).trans (act_at_smaller_degree F nd g 1))
    rw [g1, Nat.min_self] at low
    omega
  change act F d a N = d
  apply Nat.le_antisymm (act_le ..)
  apply Nat.le_of_not_gt
  intro visible
  obtain ⟨force,_⟩ := exponential_at_threshold F scale (by omega : 0 < N) start base visible
  have gp : g < 2^N := by dsimp [g]; have := Nat.two_pow_pos N; omega
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) within
  have native : a < 2^d := by dsimp [d,a]; rw [Nat.pow_succ]; omega
  change a % 2^d = g at force
  rw [Nat.mod_eq_of_lt native] at force
  change A+g = g at force
  omega

open TableElement in
theorem geometric_background_strict (H : FirstRowUnbounded) {A : Nat}
    (pos : 0 < A) (small : A < 2^targetIndex) (aligned : 2^256 ∣ A) :
    targetIndex < image H (A+(2^256-3)) 256 := by
  have enough : 256 ≤ targetIndex := Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 8 ≤ 2048)
  have high := geometric_background_saturates tables (by decide : 2 ≤ 256) enough targetIndex_eq pos small aligned
  have zero := (le_act_iff tables (targetIndex+1) _ 256 (targetIndex+1) (Nat.le_refl _)).mp (Nat.le_of_eq high.symm)
  rw [canonical_mul] at zero
  exact (numeral_zero_iff H _ _ _).mp zero

#print axioms geometric_background_strict
#print axioms normal_form_necessary
#print axioms target_iff_normal_form_and_midpoint
end Gamma11
