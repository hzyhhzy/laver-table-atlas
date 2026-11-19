import OldSlices
import EndpointNecessity

/-! Assembly of the upper bound from the old diagonal, the ordinary
short-row estimates, the two block lemmas, and the normal form for (11*3)*1.
The midpoint used here is 2^255, for which the old value is already visible
strictly below the cap. No separate evaluation of the 2^1024-wide row occurs. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds TableElement

theorem lift_odd_row_at (H : FirstRowUnbounded) (boundary : BlockBoundary H) (ones : OnesRowShift H)
    {t k g r N : Nat} (hg : 1 ≤ g) (advance : k+1≤N) (small : oldEntry t g r + 1 < 2 ^ t)
    (floors : t ≤ image H g (image H r k))
    (order : ∀ i, 1 ≤ i → i < g → image H g (k + 1) ≤ image H i N)
    (slices : ∀ i, 1 ≤ i → i ≤ g → ∃ c : OldSlice t N (oldEntry t g r) i,
      image H (2 ^ c.w - 2) N = N * c.w ∧
      ∀ b, 1 ≤ b → b < 2 ^ c.w - 2 → N * c.w ≤ image H b c.w) :
    (tables (t + 1)).mul (oldEntry t g r) (g + 1) = oldEntry t g (r + 1) := by
  let A := oldEntry t g r
  have old : ((numeral g).app (numeral r)).rep t = (numeral A).rep t := by
    change (tables t).mul (g % 2 ^ t) (r % 2 ^ t) = (oldEntry t g r) % 2 ^ t
    rw [oldEntry, (tables t).mul_mod_left, (tables t).mul_mod_right, Nat.mod_eq_of_lt ((tables t).mul_lt g r)]
  have pos (i : Nat) (lo : 1 ≤ i) (hi : i ≤ g) : 1 < oldEntry t A (i + 1) := by
    obtain ⟨c, _, _⟩ := slices i lo hi
    rw [c.finish]
    have hfour : 4 ≤ 2 ^ c.w := Nat.pow_le_pow_right (by decide : 0 < 2) c.width_two
    have hmul := Nat.mul_le_mul_right (2 ^ c.w - 1) (show 1 ≤ 2 ^ c.p from Nat.two_pow_pos _)
    rw [Nat.one_mul] at hmul
    omega
  have first : oldEntry t A 1 = A + 1 :=
    ((tables t).mul_one A).trans (Nat.mod_eq_of_lt small)
  obtain ⟨pp, hp⟩ := (tables t).exists_firstZero ((numeral A).rep t)
  have repA (b : Nat) : (tables t).mul ((numeral A).rep t) b = oldEntry t A b := (tables t).mul_mod_left _ _
  have interior : g + 1 < pp := by
    apply Nat.lt_of_not_ge
    intro h
    have zero := hp.2.1
    rw [repA] at zero
    by_cases eqone : pp = 1
    · rw [eqone, first] at zero; omega
    · have hpos := hp.1
      have high := pos (pp - 1) (by omega) (by omega)
      rw [show pp - 1 + 1 = pp by omega, zero] at high
      omega
  have base : oldEntry (t + 1) A 1 = oldEntry t A 1 := by
    rw [first, oldEntry, (tables (t + 1)).mul_one, Nat.mod_eq_of_lt (Nat.lt_trans small (Nat.pow_lt_pow_succ (by decide)))]
  have step (i : Nat) (lo : 1 ≤ i) (hi : i < g + 1) :
      (tables (t + 1)).mul (oldEntry t A i) (A + 1) = oldEntry t A (i + 1) := by
    obtain ⟨c, stretch, shortRows⟩ := slices i lo (by omega)
    have op := outer_protected_at H old floors (i := i) (by omega) hp interior
      (show 1 < (tables t).mul ((numeral A).rep t) (i + 1) by rw [repA]; exact pos i lo (by omega)) advance (order i lo)
    exact lift_slice H boundary ones c stretch shortRows op
  have right := lift_prefix base step (y := g + 1) (by omega) (Nat.le_refl _)
  exact right.trans ((tables t).row_recurrence g r).symm

theorem lift_odd_row (H : FirstRowUnbounded) (boundary : BlockBoundary H) (ones : OnesRowShift H)
    {t k g r : Nat} (hg : 1 ≤ g) (small : oldEntry t g r + 1 < 2 ^ t)
    (floors : t ≤ image H g (image H r k))
    (order : ∀ i, 1 ≤ i → i < g → image H g (k + 1) ≤ image H i (k + 2))
    (slices : ∀ i, 1 ≤ i → i ≤ g → ∃ c : OldSlice t (k + 2) (oldEntry t g r) i,
      image H (2 ^ c.w - 2) (k + 2) = (k + 2) * c.w ∧
      ∀ b, 1 ≤ b → b < 2 ^ c.w - 2 → (k + 2) * c.w ≤ image H b c.w) :
    (tables (t + 1)).mul (oldEntry t g r) (g + 1) = oldEntry t g (r + 1) :=
  lift_odd_row_at H boundary ones hg (Nat.le_succ _) small floors order slices

/-- Positive even carries require just the single-high-bit estimate on
rows with the specified positive aligned background. -/
theorem lift_even_row (H : FirstRowUnbounded) (boundary : BlockBoundary H) (ones : OnesRowShift H)
    {t N A g r : Nat} (width : IsDyadic N) (aligned : 2 ^ N ∣ A)
    (old : oldEntry t g (r + 1) = A + (g + 1))
    (guards : ∀ b, 1 ≤ b → b ≤ g → t < image H (A + b) N) :
    (tables (t + 1)).mul A (g + 1) = oldEntry t g (r + 1) := by
  have protect (v : Nat) (lo : 2 ≤ v) (hi : v ≤ g + 1) : t + 1 ≤ image H (A + 2 ^ 0 * v - 1) N := by
    rw [show A + 2 ^ 0 * v - 1 = A + (v - 1) by simp; omega]
    exact guards (v - 1) (by omega) (by omega)
  have h := aligned_block_prefix H boundary ones (d := t + 1) (p := 0) width (Nat.dvd_zero N)
    (by simpa only [Nat.zero_add] using aligned) (Nat.zero_lt_succ g) protect
  have lt : A + (g + 1) < 2 ^ (t + 1) :=
    Nat.lt_trans (old ▸ (tables t).mul_lt g (r + 1)) (Nat.pow_lt_pow_succ (by decide))
  simpa only [Nat.pow_zero, Nat.one_mul, Nat.add_one_sub_one, Nat.mod_eq_of_lt lt, old] using h

abbrev geometricRow : Nat := 2 ^ 256 - 3
abbrev midpointColumn : Nat := 2 ^ 255

/-- Descriptions of the old diagonal below the chosen midpoint. Every
table entry in this proposition is at degree T. -/
def OldDiagonalAt (t : Nat) : Prop :=
  let g := geometricRow
  0 < oldEntry t g midpointColumn ∧
  ∀ r, 1 ≤ r → r < midpointColumn →
    let A := oldEntry t g r
    (0 < A ∧ 2 ^ 256 ∣ A ∧ oldEntry t g (r + 1) = A + (g + 1)) ∨
    (A + 1 < 2 ^ t ∧ r % 2 = 1 ∧
      ∀ i, 1 ≤ i → i ≤ g → ∃ c : SliceCorners t 256 A i, c.p + c.w ≤ t ∧
        ∃ m : Nat, 0 < m ∧ c.w = 256 ^ m)

abbrev OldDiagonal : Prop := OldDiagonalAt targetIndex

/-- The short-row and bit-stretch inputs independent of the top normal form. -/
structure WidthEstimates (H : FirstRowUnbounded) : Prop where
  outerOrder : ∀ i, 1 ≤ i → i < geometricRow → image H geometricRow 255 ≤ image H i 256
  backgroundInterior : ∀ A, 0 < A → A < 2 ^ targetIndex → 2 ^ 256 ∣ A → ∀ b, 1 ≤ b → b < geometricRow →
    targetIndex < image H (A + b) 256
  stretch : ∀ m, 0 < m → let w := 256 ^ m; image H (2 ^ w - 2) 256 = 256 * w
  short : ∀ m, 0 < m → let w := 256 ^ m; ∀ b, 1 ≤ b → b < 2 ^ w - 2 → 256 * w ≤ image H b w

theorem WidthEstimates.background {H : FirstRowUnbounded} (est : WidthEstimates H)
    (A : Nat) (pos : 0 < A) (small : A < 2^targetIndex) (divA : 2^256 ∣ A)
    (b : Nat) (lo : 1 ≤ b) (hi : b ≤ geometricRow) : targetIndex < image H (A+b) 256 := by
  rcases Nat.eq_or_lt_of_le hi with rfl | interior
  · exact geometric_background_strict H pos small divA
  · exact est.backgroundInterior A pos small divA b lo interior

theorem target_of_old_diagonal (H : FirstRowUnbounded) (boundary : BlockBoundary H)
    (diagonal : OldDiagonal) (est : WidthEstimates H)
    (nf : entry (targetIndex + 1) (entry (targetIndex + 1) 11 3) 1 = geometricRow) : Target := by
  let t := targetIndex
  let g := geometricRow
  have ones : OnesRowShift H := ones_shift_of_boundary H boundary
  have hs : 256 < targetIndex := Nat.lt_of_lt_of_le (by decide : 256 < 2 ^ 9)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 9 ≤ 2048))
  have rowBound : g + 1 < 2 ^ t := by
    have small : g + 1 ≤ 2 ^ 256 := by dsimp [g, geometricRow]; omega
    exact Nat.lt_of_le_of_lt small (Nat.pow_lt_pow_right (by decide) hs)
  have base : oldEntry (t + 1) g 1 = oldEntry t g 1 := by
    simp only [oldEntry, FiniteTable.mul_one, Nat.mod_eq_of_lt rowBound,
      Nat.mod_eq_of_lt (Nat.lt_trans rowBound (Nat.pow_lt_pow_succ (by decide)))]
  obtain ⟨positive, cases⟩ := diagonal
  have step (r : Nat) (lo : 1 ≤ r) (hi : r < midpointColumn) :
      (tables (t + 1)).mul (oldEntry t g r) (g + 1) = oldEntry t g (r + 1) := by
    rcases cases r lo hi with ⟨pos, dvd, old⟩ | ⟨small, odd, slices⟩
    · exact lift_even_row H boundary ones (width := ⟨8, by decide⟩) dvd old
        (est.background _ pos ((tables t).mul_lt g r) dvd)
    · apply lift_odd_row H boundary ones (k := 254) (by decide : 1 ≤ geometricRow) small (odd_outer_floor H lo odd hi) est.outerOrder
      intro i hlo hup
      obtain ⟨c, window, m, hm, wid⟩ := slices i hlo hup
      exact ⟨c.toOldSlice H ones (by decide) window, wid.symm ▸ est.stretch m hm, wid.symm ▸ est.short m hm⟩
  have same := lift_prefix base step (y := midpointColumn) (Nat.two_pow_pos _) (Nat.le_refl _)
  apply (target_iff_geometric_midpoint nf).mpr
  change 0 < entry (t + 1) g midpointColumn ∧ entry (t + 1) g midpointColumn < 2 ^ t
  rw [← canonical_mul]
  change 0 < oldEntry (t + 1) g midpointColumn ∧ oldEntry (t + 1) g midpointColumn < 2 ^ t
  rw [same]
  exact ⟨positive, (tables t).mul_lt _ _⟩

#print axioms target_of_old_diagonal
end Gamma11
