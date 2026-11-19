import RankEndpoint
import GeometricPrefix
import LocalPeriodTarget
import OneBitBlock
import BackwardCompression

/-! Two alternative sufficient conditions at the actual critical spectrum. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11.RankI3
universe u
open TableElement

theorem endpoint_from_one_prefix {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) (row : GeometricPrefix) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  have hit := target_from_one_column H blocks (target_normal_form hj H blocks)
    (fun _ room => run_moves_to_edge tables room) row
  exact ⟨_,(quotientLaws_of_first_row hj H).enumerates,(actual_endpoint_iff_target hj).mpr hit⟩

#print axioms endpoint_from_one_prefix
/-- A local update of a dyadic block implies the mixed-period estimates
and the ordinary block law used by the normal form. -/
theorem endpoint_of_local_block_periods {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (restore : RestoreBlockLaw)
    (diag : DiagonalHomAt 256 targetIndex) (stretches : LicensedStretches) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  have blocks : FiniteBlockLaw := finite_block_of_restore restore
  have period := short_period_induction (auxiliary_stretches_from_blocks H blocks)
    (mixed_periods_of_restore H blocks restore) stretches
  exact endpoint_of_remaining_laws hj H blocks diag stretches
    (fun m hm b lo hi => period m hm b lo (Nat.le_of_lt hi))

#print axioms endpoint_of_local_block_periods

/-- Under a real witness, the ordinary table inputs on the diagonal
route reduce to first-row growth, one local period update and the
third-level homomorphism. -/
theorem endpoint_of_growth_restore_diagonal {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (restore : RestoreBlockLaw) (diag : DiagonalHomAt 256 targetIndex) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  have law : FiniteBlockLaw := finite_block_of_restore restore
  have hit := target_from_local_restoration H restore diag (appendix_E hj H law (sixteen_data_from_blocks H law))
    (target_normal_form hj H law)
  exact ⟨_,(quotientLaws_of_first_row hj H).enumerates,(actual_endpoint_iff_target hj).mpr hit⟩

#print axioms endpoint_of_growth_restore_diagonal

theorem endpoint_of_backward_row_and_diagonal {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (backwards : Backward.PositiveFullDigitRow) (diag : DiagonalHomAt 256 targetIndex) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_of_growth_restore_diagonal hj H (Backward.restore_of_full_digit
    (Backward.full_of_positive_digits backwards)) diag

#print axioms endpoint_of_backward_row_and_diagonal

theorem endpoint_of_wide_digits_and_diagonal {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (wide : Backward.WidePositiveDigits) (diag : DiagonalHomAt 256 targetIndex) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_of_growth_restore_diagonal hj H (Backward.restore_of_full_digit
    (Backward.full_of_wide_digits wide)) diag

#print axioms endpoint_of_wide_digits_and_diagonal

/-- The finite restoration argument is unconditional. For this route
only first-row growth and the old diagonal remain to be discharged. -/
theorem endpoint_of_growth_and_diagonal {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (diag : DiagonalHomAt 256 targetIndex) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_of_growth_restore_diagonal hj H Backward.finite_restoration diag

/-- The alternative single-column route uses the same unconditional
finite block theorem; an equality at its one specified old column is
still an argument. -/
theorem endpoint_of_growth_and_prefix {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (row : GeometricPrefix) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_from_one_prefix hj H (finite_block_of_restore Backward.finite_restoration) row

#print axioms endpoint_of_growth_and_diagonal
#print axioms endpoint_of_growth_and_prefix
end Gamma11.RankI3
