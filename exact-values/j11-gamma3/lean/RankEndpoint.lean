import RankDenseSource
import LastNormalProduct
import ShortPeriod

/-! The end-to-end implication with its remaining mathematical inputs as
explicit arguments. None is installed as a Lean axiom. -/

/-!
`endpoint_iff_finite_arithmetic` 给出当前主归约。存在真实 I3 见证时，包含整个谱枚举的
陈述等价于普通 Laver 表的 `FirstRowUnbounded ∧ Target`。对于两个指定的有限位置，
`RankReadout` 直接证明等号与 `Target` 等价，且已经证明下界。每个有限截断都已有真实的
商表同构。最后的非零性以及全谱枚举所需的第一行无界性仍待证明。

`RankSectionConstants.two_target_constants` 将附录 A.3 的两项具体行值从第一行无界性
和有限表分块引理推得。其余三项由 `TwelveCut.normal_transports` 直接从有限表递推推出。
`RankEarlySource.early_source` 用第 65534 行在低阶表中的读值求出两个像的共同下标 256。
`DoubleWidths.sixteen_data_from_blocks` 从上述两个有限表前提得出这些读值，因而也得出 65,520 项加法前缀。
`RankWideSource.appendix_C2` 给出临界位置 16 至 255 的严格界。
`RankWideSource.appendix_E` 推出普通行的旧阶周期、带非零背景行的新阶周期和逐项加法前缀。
`RankDenseSource.target_square` 证明目标阶上 65534 的平方，`target_normal_form` 给出正常形。

早期的 `endpoint_from_inputs` 将证明分解为以下五项。

* `quotients` 是任意行、任意谱下标和任意有限阶的 Laver 商表对应。
* `blocks` 是 Dougherty II 引理 6.3 在右端点的两个恒等式。
* `widths` 包含短行周期、位伸展和带非零高位背景的严格保护。
* `diagonal` 描述旧表第 g 行的进位及相邻两个端点，只出现 T 阶的乘积。
* `normalForm` 将 (11*3)*1 在 T+1 阶的代表确定为 2^256-3。

`SpectrumBits.ones_shift_of_boundary` 已推出需要的全 1 行平移。
`OldSlices.old_slice_line` 从相邻端点确定完整旧表前缀，`CarryLift.lift_slice`
负责提升到下一阶。`CriticalFour.critical_four_applied` 已证明正常形纸稿第 1 节
的应用行严格界。`EndpointNecessity` 给出正常形与中点联合判据的双向证明。
`DiagonalHom.lean` 从旧阶的第三层对角同态及指定位宽的第二层同态
推出所有奇数列的端点分解。`OddDiagonal` 推出偶数列的加法和中点的正值。
`ShortPeriod.lean` 把全由零块或满位块组成的短行归纳到较小的位宽。
`TwelveCut.lean` 中的 `normal_transports` 通过普通有限表证明附录 A.3 中 S、P、U 的三个恒等式。
`RankTransport.lean` 中的 `thirteen_restriction_at_target` 把另两个目标表常数归约到较低位置的
普通限制及越过该位置的像。`RankComposition` 证明普通复合在有限截断下的读法。
`endpoint_of_rank_quotient_laws` 采用上述同态、有限周期界、分块乘法及正常形。秩模型一侧从零商类、
谱枚举推出实际点像的有限表读法。应用的初等性、单值性及临界点的搬运已在实际秩模型内证明。
另一路 `ManuscriptEndpoint.manuscript_midpoint_conclusion` 验证原论文第 6 节的收尾。
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11.RankI3
universe u
open TableElement

theorem lower_bound_for_enumeration {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    {γ : Nat → Below height} (en : Enumerates j γ) :
    γ targetIndex ≤ ordinalImage (powerEmb hj.1 j 11) (γ 3) := by
  rw [enumerates_eq_dyadic hj en]
  exact actual_lower_bound hj

theorem equality_for_enumeration_iff_nonzero {height : Ordinal.{u}} {j : Emb height}
    (hj : IsWitness j) {γ : Nat → Below height} (en : Enumerates j γ) :
    leftPower j 11 (point (γ 3)) (point (γ targetIndex)) ↔ entry (targetIndex+1) 11 8 ≠ 0 := by
  rw [enumerates_eq_dyadic hj en]
  exact (actual_endpoint_iff_target hj).trans target_iff_nonzero

theorem endpoint_from_inputs
    (quotients : ∀ {height : Ordinal.{u}} (j : Emb height), IsWitness j →
      ∃ γ, FiniteCorrespondence j γ)
    (blocks : I3.{u} → ∀ H : FirstRowUnbounded, BlockBoundary H)
    (widths : I3.{u} → ∀ H : FirstRowUnbounded, WidthEstimates H)
    (diagonal : I3.{u} → OldDiagonal)
    (normalForm : I3.{u} → entry (targetIndex + 1) (entry (targetIndex + 1) 11 3) 1 = geometricRow) :
    EndpointStatement.{u} := by
  intro height j hj
  obtain ⟨γ, model⟩ := quotients j hj
  have i3 : I3.{u} := ⟨height, j, hj⟩
  have H := firstRowUnbounded_of_correspondence model
  have exactValue := target_of_old_diagonal H (blocks i3 H) (diagonal i3) (widths i3 H) (normalForm i3)
  exact ⟨γ, model.enumerates, actual_image_of_target model exactValue⟩

#print axioms endpoint_from_inputs

/-- At the rank level the only quotient test is for the identity class.
    All old diagonal and inner-slice data are consequences of the named
    homomorphisms and period guards here. -/
theorem endpoint_of_rank_quotient_laws
    (rankLaws : ∀ {height : Ordinal.{u}} (j : Emb height), IsWitness j →
      ∃ γ, QuotientLaws j γ)
    (blocks : I3.{u} → FiniteBlockLaw)
    (diagonalHom : I3.{u} → DiagonalHomAt 256 targetIndex)
    (stretchHoms : I3.{u} → LicensedStretches)
    (periods : I3.{u} → PeriodGuards)
    (normalForm : I3.{u} → entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow) :
    EndpointStatement.{u} := by
  intro height j hj
  obtain ⟨γ,laws⟩ := rankLaws j hj
  have i3 : I3.{u} := ⟨height,j,hj⟩
  have finiteModel := laws.correspondence hj
  have H := firstRowUnbounded_of_correspondence finiteModel
  have exactValue := target_of_table_laws H (blocks i3) (diagonalHom i3) (stretchHoms i3)
    (periods i3) (normalForm i3)
  exact ⟨γ,laws.enumerates,actual_image_of_target finiteModel exactValue⟩

#print axioms endpoint_of_rank_quotient_laws

/-- For the version that also asserts exhaustion of the whole critical
    spectrum, both outstanding statements are ordinary table arithmetic.
    The backward direction requires no set-theoretic premise beyond the
    witness in the definition of EndpointStatement. -/
theorem endpoint_of_finite_arithmetic (growth : FirstRowUnbounded) (hit : Target) : EndpointStatement.{u} := by
  intro height j hj
  exact ⟨_,(quotientLaws_of_first_row hj growth).enumerates,(actual_endpoint_iff_target hj).mpr hit⟩

theorem endpoint_iff_finite_arithmetic (witness : I3.{u}) :
    EndpointStatement.{u} ↔ FirstRowUnbounded ∧ Target := by
  constructor
  · intro ep
    obtain ⟨height,j,hj⟩ := witness
    obtain ⟨γ,en,value⟩ := ep j hj
    refine ⟨(enumeration_iff_first_row hj).mp ⟨γ,en⟩,?_⟩
    rw [enumerates_eq_dyadic hj en] at value
    exact (actual_endpoint_iff_target hj).mp value
  · exact fun h => endpoint_of_finite_arithmetic h.1 h.2

theorem endpoint_of_growth_and_table_laws
    (growth : I3.{u} → FirstRowUnbounded)
    (blocks : I3.{u} → FiniteBlockLaw)
    (diagonalHom : I3.{u} → DiagonalHomAt 256 targetIndex)
    (stretchHoms : I3.{u} → LicensedStretches)
    (periods : I3.{u} → PeriodGuards)
    (normalForm : I3.{u} → entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow) :
    EndpointStatement.{u} := by
  intro height j hj
  have i3 : I3.{u} := ⟨height,j,hj⟩
  have H := growth i3
  have hit := target_of_table_laws H (blocks i3) (diagonalHom i3) (stretchHoms i3) (periods i3) (normalForm i3)
  exact endpoint_of_finite_arithmetic H hit j hj

#print axioms endpoint_iff_finite_arithmetic
#print axioms endpoint_of_growth_and_table_laws
#print axioms lower_bound_for_enumeration
#print axioms equality_for_enumeration_iff_nonzero

private def NarrowBackground (t : Nat) : Prop :=
  ∀ a, 0<a → a<2^t → 2^256 ∣ a → ∀ b, 1≤b → b<geometricRow → entry (t+1) (a+b) (2^256)=0

private theorem smaller_background {t : Nat} (wide : WidePeriodEstimates t) : NarrowBackground t :=
  fun a pos small aligned b lo hi => wide.background a pos
    (Nat.lt_trans small (Nat.pow_lt_pow_succ (by decide))) aligned b lo
    (Nat.lt_trans hi (by decide : geometricRow<2^256-2))

private theorem smaller_native {t : Nat} (wide : WidePeriodEstimates t) :
    ∀ b, 1≤b → b<geometricRow → entry t b (2^256)=0 :=
  fun b pos hi => wide.native b pos (Nat.lt_trans hi (by decide : geometricRow<2^256-2))

theorem normal_form_from_target_square {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) (h16 : SixteenRowData)
    (square : entry (targetIndex+1) 65534 65534=2^256-2^16) :
    entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1=geometricRow := by
  obtain ⟨r,l⟩ := two_target_constants hj H blocks
  have cap : 256≤targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  exact normal_form_of_last_product (d:=targetIndex+1) (Nat.le_trans cap (Nat.le_succ targetIndex))
    (Nat.le_refl (targetIndex+1)) r l square (appendix_B3_endpoint hj H blocks h16)

private theorem guards_using_wide {t : Nat} (wide : WidePeriodEstimates t)
    (short : ∀ m, 0<m → ∀ b, 1≤b → b<2^(256^m)-2 → entry (256*(256^m)) b (2^(256^m))=0) :
    PeriodGuardsAt t where
  native := smaller_native wide
  background := smaller_background wide
  short := short

/-- Current end-to-end implication. The representative of 11*3 and two
whole families of period tests are theorems here. The remaining finite
inputs and first-row unboundedness are visible in the signature. -/
theorem endpoint_at_witness_of_remaining {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) (h16 : SixteenRowData)
    (diag : DiagonalHomAt 256 targetIndex) (stretches : LicensedStretches)
    (short : ∀ m, 0<m → ∀ b, 1≤b → b<2^(256^m)-2 → entry (256*(256^m)) b (2^(256^m))=0)
    (square : entry (targetIndex+1) 65534 65534=2^256-2^16) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  have normal := normal_form_from_target_square hj H blocks h16 square
  have periods := guards_using_wide (appendix_E hj H blocks h16) short
  have hit := target_of_table_laws H blocks diag stretches periods normal
  exact ⟨_,(quotientLaws_of_first_row hj H).enumerates,(actual_endpoint_iff_target hj).mpr hit⟩

#print axioms endpoint_at_witness_of_remaining
#print axioms normal_form_from_target_square

theorem target_normal_form {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) :
    entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1=geometricRow :=
  normal_form_from_target_square hj H blocks (sixteen_data_from_blocks H blocks) (target_square hj H blocks)

/-- The normal form and both wide period families are derived inside this
implication. The remaining arithmetic hypotheses are given explicitly. -/
theorem endpoint_of_remaining_laws {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw)
    (diag : DiagonalHomAt 256 targetIndex) (stretches : LicensedStretches)
    (short : ∀ m, 0<m → ∀ b, 1≤b → b<2^(256^m)-2 → entry (256*(256^m)) b (2^(256^m))=0) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_at_witness_of_remaining hj H blocks (sixteen_data_from_blocks H blocks) diag stretches short
    (target_square hj H blocks)

#print axioms target_normal_form
#print axioms endpoint_of_remaining_laws
end Gamma11.RankI3
