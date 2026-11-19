import LaverLowerBounds.Signature

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- An explicit terminating evaluator. Positive rows only call higher rows,
    except when the last output was zero, which starts their next cycle. -/
def rowAux (size : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, a, b =>
    if a = 0 then b % size else
      Nat.rec 0 (fun _ v =>
        if v = 0 then (a + 1) % size else rowAux size fuel v (a + 1)) b

theorem rowAux_correct {size : Nat} (A : FiniteTable size) (fuel a b : Nat)
    (ha : a < size) (hf : size - a ≤ fuel) :
    rowAux size fuel a b = A.mul a b := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
    by_cases ha0 : a = 0
    · subst a
      simpa only [rowAux, if_true] using (A.zero_mul b).symm
    · simp only [rowAux, if_neg ha0]
      induction b with
      | zero => exact (A.mul_zero a).symm
      | succ b hb =>
        change (if _ = 0 then (a + 1) % size else rowAux size fuel _ (a + 1)) = _
        rw [hb]
        rw [A.row_recurrence a b]
        rcases A.row_grows a b ha with hz | hg
        · simp [hz, A.zero_mul]
        · rw [if_neg (by omega : A.mul a b ≠ 0)]
          exact ih _ _ (A.mul_lt _ _) (by omega)

/-- The ordinary entry at degree d, defined with no table or embedding argument. -/
def entry (d a b : Nat) : Nat :=
  let size := 2 ^ d
  let row := a % size
  rowAux size (size - row) row (b % size)

theorem entry_eq_mul (d : Nat) (A : FiniteTable (2 ^ d)) (a b : Nat) :
    entry d a b = A.mul a b := by
  unfold entry
  rw [rowAux_correct A _ _ _ (Nat.mod_lt _ A.positive) (Nat.le_refl _),
    A.mul_mod_left, A.mul_mod_right]

/-- First degree with a nonzero output in row a, column 2^x is t+1. -/
def FirstChange (a x t : Nat) : Prop :=
  (∀ k, k ≤ t → entry k a (2 ^ x) = 0) ∧ entry (t + 1) a (2 ^ x) ≠ 0

/-- The single entry that certifies an exact critical index. -/
theorem exact_iff_firstChange (F : BinaryFamily) (a x t : Nat) :
    entry (t + 1) a (2 ^ x) = 2 ^ t ↔ FirstChange a x t := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [entry_eq_mul k (F k), ← (F (t + 1)).projection (F k)
        (Nat.pow_dvd_pow 2 (show k ≤ t + 1 by omega)),
        ← entry_eq_mul (t + 1) (F (t + 1)), he]
      exact (pow_mod_zero_iff _ _).mpr hk
    · rw [he]
      exact Nat.ne_of_gt (Nat.two_pow_pos _)
  · rintro ⟨hzero, hne⟩
    have hproj := (F (t + 1)).projection (F t) (Nat.pow_dvd_pow 2 (Nat.le_succ t)) a (2 ^ x)
    rw [← entry_eq_mul _ (F (t + 1)), ← entry_eq_mul _ (F t), hzero t (Nat.le_refl _)] at hproj
    have hlt := (F (t + 1)).mul_lt a (2 ^ x)
    rw [← entry_eq_mul _ (F (t + 1)), Nat.pow_succ] at hlt
    exact (multiple_below_twice hlt hproj).resolve_left hne

theorem exact_iff_act (F : BinaryFamily) (a x t : Nat) :
    entry (t + 1) a (2 ^ x) = 2 ^ t ↔ act F (t + 1) a x = t := by
  rw [exact_iff_firstChange F]
  constructor
  · rintro ⟨hzero, hne⟩
    have hlow := (le_act_iff F (t + 1) a x t (Nat.le_succ t)).mpr
      ((entry_eq_mul t (F t) _ _).symm.trans (hzero t (Nat.le_refl _)))
    have hhi : ¬ t + 1 ≤ act F (t + 1) a x := by
      intro h
      exact hne ((entry_eq_mul _ (F _) _ _).trans
        ((le_act_iff F (t + 1) a x (t + 1) (Nat.le_refl _)).mp h))
    omega
  · intro he
    constructor
    · intro k hk
      rw [entry_eq_mul k (F k)]
      exact (le_act_iff F (t + 1) a x k (by omega)).mp (by omega)
    · intro hz
      rw [entry_eq_mul _ (F _)] at hz
      have := (le_act_iff F (t + 1) a x (t + 1) (Nat.le_refl _)).mpr hz
      omega

def targetIndex : Nat := 2 ^ 2048

/-- An equality of closed natural-number expressions, with no I3 hypothesis. -/
def Target : Prop := entry (targetIndex + 1) 11 8 = 2 ^ targetIndex

instance : Decidable Target := inferInstanceAs (Decidable (_ = _))

theorem target_iff_firstChange (F : BinaryFamily) :
    Target ↔ FirstChange 11 3 targetIndex := exact_iff_firstChange F 11 3 _

theorem target_iff_act (F : BinaryFamily) :
    Target ↔ act F (targetIndex + 1) 11 3 = targetIndex := exact_iff_act F 11 3 _

example : entry 3 3 2 = 0 := by decide
example : entry 3 2 3 = 7 := by decide

end Gamma11
