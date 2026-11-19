import BlockPrefix

/-! Lifting a carry from degree t to t+1. `OldSlice` contains only
decompositions of integers and specified entries in the table at degree t. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds TableElement

def oldEntry (t A i : Nat) := (tables t).mul A i

structure SliceCorners (t N A i : Nat) where
  w : Nat
  p : Nat
  background : Nat
  offset : Nat
  width : IsDyadic w
  width_ge : N ≤ w
  width_two : 2 ≤ w
  aligned : w ∣ p
  block_dvd : 2 ^ (p + w) ∣ background
  offset_dvd : 2 ^ (N * w) ∣ offset
  argument : A + 1 = offset + (2 ^ w - 1)
  start : oldEntry t A i = background + 2 ^ p - 1
  finish : oldEntry t A (i + 1) = background + 2 ^ p * (2 ^ w - 1)

structure OldSlice (t N A i : Nat) extends SliceCorners t N A i where
  line : ∀ v, 1 ≤ v → v ≤ 2 ^ w - 1 →
    oldEntry t (oldEntry t A i) v = background + 2 ^ p * v

theorem finite_comp_rep {t A i : Nat} (positive : 0 < oldEntry t A (i + 1)) :
    ((numeral A).comp (numeral i)).rep t = oldEntry t A (i + 1) - 1 := by
  have old : (tables t).mul ((numeral A).rep t) (i + 1) = oldEntry t A (i + 1) :=
    (tables t).mul_mod_left _ _
  have h := comp_output_succ (numeral A) t i (old.symm ▸ positive)
  rw [old] at h
  omega

theorem lift_slice (H : FirstRowUnbounded) (boundary : BlockBoundary H) (ones : OnesRowShift H)
    {t N A i : Nat} (c : OldSlice t N A i)
    (stretch : image H (2 ^ c.w - 2) N = N * c.w)
    (shortRows : ∀ b, 1 ≤ b → b < 2 ^ c.w - 2 → N * c.w ≤ image H b c.w)
    (outer : t < image H (((numeral A).comp (numeral i)).rep t) N) :
    (tables (t + 1)).mul (oldEntry t A i) (A + 1) = oldEntry t A (i + 1) := by
  let W := oldEntry t A i
  let E := 2 ^ c.w - 1
  let ell := 2 ^ c.w - 2
  have four : 4 ≤ 2 ^ c.w := Nat.pow_le_pow_right (by decide : 0 < 2) c.width_two
  have epos : 0 < E := by dsimp [E]; omega
  have succE : ell + 1 = E := by dsimp [ell, E]; omega
  have pos (v : Nat) (hv : 0 < v) : 0 < c.background + 2 ^ c.p * v :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos _) hv) (Nat.le_add_left ..)
  have e1 := c.line E epos (Nat.le_refl _)
  have z1 : oldEntry t W (ell + 1) = oldEntry t A (i + 1) := by
    rw [succE]; exact e1.trans c.finish.symm
  have zpos : 0 < oldEntry t A (i + 1) := c.finish ▸ pos E epos
  have common : ((numeral W).comp (numeral ell)).rep t = ((numeral A).comp (numeral i)).rep t := by
    rw [finite_comp_rep (z1.symm ▸ zpos), finite_comp_rep zpos, z1]
  have per := inner_period_bound H common outer stretch
  obtain ⟨pp, hp⟩ := (tables t).exists_firstZero ((numeral W).rep t)
  have repW (b : Nat) : (tables t).mul ((numeral W).rep t) b = oldEntry t W b :=
    (tables t).mul_mod_left _ _
  have inside : ell + 1 < pp := by
    rw [succE]; apply Nat.lt_of_not_ge; intro le
    have hit := hp.2.1
    rw [repW, c.line pp hp.1 le] at hit
    exact (Nat.ne_of_gt (pos pp hp.1)) hit
  have protectedRows (v : Nat) (two : 2 ≤ v) (last : v ≤ E) :
      t + 1 ≤ image H (c.background + 2 ^ c.p * v - 1) c.w := by
    let b := v - 1
    have vb : b + 1 = v := by dsimp [b]; omega
    have line := c.line v (by omega) last
    have gtOne : 1 < oldEntry t W (b + 1) := by
      rw [vb, line]
      have small := Nat.mul_le_mul_right v (show 1 ≤ 2 ^ c.p from Nat.two_pow_pos _)
      rw [Nat.one_mul] at small
      omega
    have native := inner_protected H common outer (j := b) (by omega) c.width_ge hp inside
      (show 1 < (tables t).mul ((numeral W).rep t) (b + 1) by rw [repW]; exact gtOne)
      (fun hlt => stretch ▸ shortRows b (by dsimp [b]; omega) hlt)
    rw [finite_comp_rep (Nat.lt_trans (by decide : 0 < 1) gtOne), vb, line] at native
    exact native
  have hz : (tables (t + 1)).mul W (2 ^ (N * c.w)) = 0 := by
    rw [canonical_mul]; exact (numeral_zero_iff H _ _ _).mpr per
  have lifted := aligned_block_prefix H boundary ones c.width c.aligned c.block_dvd epos protectedRows
  have range : c.background + 2 ^ c.p * E < 2 ^ (t + 1) :=
    Nat.lt_trans (c.finish ▸ (tables t).mul_lt A (i + 1)) (Nat.pow_lt_pow_succ (by decide))
  rw [Nat.mod_eq_of_lt range] at lifted
  rw [c.argument, add_period_background c.offset_dvd hz]
  change (tables (t + 1)).mul (oldEntry t A i) E = _
  rw [c.start, c.finish]
  exact lifted

/-- The whole positive prefix of a row is unchanged once each successor
step on its old representatives is protected. Induction is symbolic. -/
theorem lift_prefix {t A k : Nat} (base : oldEntry (t + 1) A 1 = oldEntry t A 1)
    (step : ∀ i, 1 ≤ i → i < k → (tables (t + 1)).mul (oldEntry t A i) (A + 1) = oldEntry t A (i + 1))
    {y : Nat} (lo : 1 ≤ y) (hi : y ≤ k) : oldEntry (t + 1) A y = oldEntry t A y := by
  induction y with
  | zero => omega
  | succ v ih =>
    cases v with
    | zero => exact base
    | succ n =>
      change (tables (t + 1)).mul A ((n+1)+1) = _
      rw [(tables (t + 1)).row_recurrence, show (tables (t + 1)).mul A (n+1) = oldEntry t A (n+1) from ih (by omega) (by omega)]
      exact step _ (by omega) (by omega)

#print axioms lift_slice
end Gamma11
