import CanonicalTables
import EndpointGrowth

/-!
## 第 11 行第三号像的有限表证明

取 T = 256^256 = 2^2048。完整猜测在 EndpointArithmetic.Target 中写成
普通表的等式 11 *_(T+1) 8 = 2^T。

本文件无条件证明所有 k ≤ T 均有 11 *_k 8 = 0。核心是以下两次增长估计。
对于截断在 m 的作用 f，只要末端严格小于 m，首像为 1 的行就满足
f(x) ≥ f(1)^x。第 13 行的首两像为 1、4，而有限表协变性给出
f_11(2) = f_13(4)。所以在可读时，u = f_11(2) 至少为 4^4 = 256。
再取 G = (11*3)*1，有 f_G(0) = 1，f_G(1) = u，f_G(u) = f_11(3)。
同一估计给出 f_11(3) ≥ u^u ≥ T。取 m = T 排除小于 T 的像，再向下投影。

目标阶的非零性仍待证明。以下已证充要条件可单独使用

* target_iff_nonzero：第 T+1 阶第 8 项非零。
* target_iff_fourth_entry：同阶第 4 项恰为 2^T - 2^256。

原纸稿第 3–5 节调用实际复合在更高阶达到某个临界点下标的事实。
本文件没有把这一事实加入假设。最后一个带 nf 前提的定理另行说明
原纸稿正常形与几何行的关系。
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem targetIndex_eq : targetIndex = 256 ^ 256 := by
  calc
    targetIndex = 2 ^ (8 * 256) := congrArg (fun k : Nat => 2 ^ k) (by decide : 2048 = 8 * 256)
    _ = (2 ^ 8) ^ 256 := Nat.pow_mul ..
    _ = _ := rfl

private theorem targetIndex_large : 257 ≤ targetIndex :=
  Nat.le_trans (by decide : 257 ≤ 2 ^ 9)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 9 ≤ 2048))

/-- Two low-degree applications identify f_11(2) with f_13(4). The latter
    has lower bound 4^4 whenever the value is visible below the cap. -/
theorem eleven_second_lower (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m)
    (unsat : act F m 11 2 < m) : 256 ≤ act F m 11 2 := by
  have hsize : 512 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have next11 : (F m).mul 11 1 = 12 := by
    rw [(F m).mul_one, Nat.mod_eq_of_lt (by omega)]
  have next12 : (F m).mul 12 1 = 13 := by
    rw [(F m).mul_one, Nat.mod_eq_of_lt (by omega)]
  have j1 : act F m 1 1 = 2 := act_from_low F _ _ _ 12 _ hm
    (LowProducts.v1_2 (F 9)) (by decide) (by decide)
  have j2 : act F m 1 2 = 4 := act_from_low F _ _ _ 240 _ hm
    (LowProducts.v1_4 (F 9)) (by decide) (by decide)
  have j11 : act F m 11 1 = 4 := act_from_low F _ _ _ 496 _ hm
    (LowProducts.v11_2 (F 9)) (by decide) (by decide)
  have j12 : act F m 12 2 = 4 := act_from_low F _ _ _ 464 _ hm
    (LowProducts.v12_4 (F 9)) (by decide) (by decide)
  have j130 : act F m 13 0 = 1 := act_from_low F _ _ _ 14 _ hm
    ((F 9).mul_one 13) (by decide) (by decide)
  have j131 : act F m 13 1 = 4 := act_from_low F _ _ _ 496 _ hm
    (LowProducts.v13_2 (F 9)) (by decide) (by decide)
  have e1 := act_application F m 11 1 1
  rw [next11, j11, j1] at e1
  have e2 := act_application F m 12 1 2
  rw [next12, j12, j2, e1] at e2
  have h := exponential_growth F m 13 4 j130 (Nat.lt_of_le_of_lt (Nat.le_of_eq e2) unsat)
  rw [j131, e2] at h
  exact h

/-- Already at the level of finite tables, a visible third index is at
    least (f_11(2))^(f_11(2)). -/
theorem eleven_third_growth (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m)
    (unsat : act F m 11 3 < m) : (act F m 11 2) ^ (act F m 11 2) ≤ act F m 11 3 := by
  obtain ⟨h0, h1, h3⟩ := eleven_actions F m hm
  have bound := exponential_growth F m _ (act F m 11 2) h0 (Nat.lt_of_le_of_lt (Nat.le_of_eq h3) unsat)
  rwa [h1, h3] at bound

theorem eleven_third_lower (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m)
    (unsat : act F m 11 3 < m) : targetIndex ≤ act F m 11 3 := by
  have before := act_mono F m 11 (by decide : 2 ≤ 3)
  have hsecond := eleven_second_lower F m hm (Nat.lt_of_le_of_lt before unsat)
  rw [targetIndex_eq]
  calc
    256 ^ 256 ≤ (act F m 11 2) ^ 256 := Nat.pow_le_pow_left hsecond _
    _ ≤ (act F m 11 2) ^ (act F m 11 2) := Nat.pow_le_pow_right (by omega) hsecond
    _ ≤ _ := eleven_third_growth F m hm unsat

/-- The full lower side of the endpoint, in closed arithmetic: every table
    through degree 2^2048 has zero in ordinary row 11, column 8. -/
theorem row11_zero_through_target (k : Nat) (hk : k ≤ targetIndex) : entry k 11 8 = 0 := by
  have hbig := targetIndex_large
  have atTarget : targetIndex ≤ act tables targetIndex 11 3 := by
    apply Nat.le_of_not_gt
    intro h
    have := eleven_third_lower tables targetIndex (by omega) h
    omega
  exact (entry_eq_mul k (tables k) 11 8).trans
    ((le_act_iff tables targetIndex 11 3 k hk).mp (Nat.le_trans hk atTarget))

theorem target_iff_nonzero : Target ↔ entry (targetIndex + 1) 11 8 ≠ 0 := by
  rw [target_iff_firstChange tables]
  exact ⟨And.right, fun h => ⟨row11_zero_through_target, h⟩⟩

/-- No hypotheses. The only remaining check for exactness is whether the
    fourth output in the next degree lies strictly between zero and 2^T. -/
theorem target_iff_midpoint : Target ↔
    0 < entry (targetIndex + 1) 11 4 ∧ entry (targetIndex + 1) 11 4 < 2 ^ targetIndex := by
  have hbig := targetIndex_large
  have h := lift_iff_lower_midpoint tables targetIndex 11 2 (by omega)
    (show (tables targetIndex).mul 11 8 = 0 from (canonical_mul _ _ _).trans
      (row11_zero_through_target _ (Nat.le_refl _)))
  simpa only [Target, canonical_mul] using h

theorem target_iff_threshold : Target ↔ FirstChange 11 3 targetIndex :=
  target_iff_firstChange tables

theorem second_at_equality (F : BinaryFamily) (m : Nat) (hm : 9 ≤ m)
    (ht : targetIndex < m) (hval : act F m 11 3 = targetIndex) : act F m 11 2 = 256 := by
  have unsat : act F m 11 3 < m := by omega
  have hbefore := Nat.lt_of_le_of_lt (act_mono F m 11 (by decide : 2 ≤ 3)) unsat
  have lower := eleven_second_lower F m hm hbefore
  have upper := eleven_third_growth F m hm unsat
  rw [hval, targetIndex_eq] at upper
  apply Nat.le_antisymm _ lower
  apply Nat.le_of_not_gt
  intro h
  have hlt := Nat.pow_lt_pow_right (by decide : 1 < 256) h
  have hle := Nat.pow_le_pow_left lower (act F m 11 2)
  exact Nat.not_lt_of_ge upper (Nat.lt_of_lt_of_le hlt hle)

/-- A single numerical alternative to the midpoint range test. No paper
    normal form, geometric-row assumption, or embedding hypothesis. -/
theorem target_iff_fourth_entry : Target ↔
    entry (targetIndex + 1) 11 4 = 2 ^ targetIndex - 2 ^ 256 := by
  have hbig := targetIndex_large
  have hlow : 2 ^ 256 < 2 ^ targetIndex := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos 256
  constructor
  · intro h
    have hcrit := second_at_equality tables (targetIndex + 1) (by omega) (by omega)
      ((target_iff_act tables).mp h)
    obtain ⟨hp, hu⟩ := target_iff_midpoint.mp h
    have proj := (tables (targetIndex + 1)).projection (tables targetIndex)
      (Nat.pow_dvd_pow 2 (Nat.le_succ targetIndex)) 11 4
    simp only [canonical_mul] at proj
    rw [Nat.mod_eq_of_lt hu] at proj
    have zero := (canonical_mul targetIndex 11 8).trans (row11_zero_through_target _ (Nat.le_refl _))
    have square := midpoint_square_zero tables (m := targetIndex) (a := 11) (r := 2)
      (by omega) zero
    have form := (square_zero_iff tables _ _ ((tables targetIndex).mul_lt 11 4)).mp square
    simp only [canonical_mul] at form
    rcases form with hz | ⟨s, hs, hv⟩
    · exact False.elim ((Nat.ne_of_gt hp) (proj.trans hz))
    · have eqv := proj.trans hv
      change signature (targetIndex + 1) ((tables (targetIndex + 1)).mul 11 4) = 256 at hcrit
      rw [canonical_mul, eqv, dyadic_tail_signature _ _ _ hs (Nat.le_succ _)] at hcrit
      exact hcrit ▸ eqv
  · intro h
    apply target_iff_midpoint.mpr
    rw [h]
    omega

/-- Optional route via the paper's normal form. The old zero for this
    second row follows from the exponential bound as well. -/
theorem target_iff_geometric_midpoint
    (nf : entry (targetIndex + 1) (entry (targetIndex + 1) 11 3) 1 = 2 ^ 256 - 3) :
    Target ↔ 0 < entry (targetIndex + 1) (2 ^ 256 - 3) (2 ^ 255) ∧
      entry (targetIndex + 1) (2 ^ 256 - 3) (2 ^ 255) < 2 ^ targetIndex := by
  have hbig := targetIndex_large
  have norm := normal_form_reduction tables (targetIndex + 1) 256
    (by omega) (by decide) (by omega) (by simpa only [canonical_mul] using nf)
  have old := geometric_row_zero tables targetIndex 256 256 (by decide) hbig
    (Nat.le_of_eq targetIndex_eq)
  rw [target_iff_act tables, norm.2, ← exact_iff_act tables]
  simpa only [canonical_mul] using
    (lift_iff_lower_midpoint tables targetIndex (2 ^ 256 - 3) 255 (by omega) old)

#print axioms row11_zero_through_target
#print axioms target_iff_nonzero
#print axioms target_iff_midpoint
#print axioms target_iff_fourth_entry
#print axioms target_iff_geometric_midpoint

end Gamma11
