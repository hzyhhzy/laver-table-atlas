import RankGeometric
import CubicSeed

/-! The conditional equality uses just the first-row period theorem.
The genuine rank-embedding calculations provide all wide period data,
and the cubic seed supplies the diagonal homomorphism. -/
set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open TableElement
variable {height : Ordinal.{u}} {j : Emb height}

theorem endpoint_of_first_row (hj : IsWitness j) (H : FirstRowUnbounded) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  have blocks : FiniteBlockLaw := finite_block_of_restore Backward.finite_restoration
  have wide := appendix_E hj H blocks (sixteen_data_from_blocks H blocks)
  exact endpoint_of_growth_and_diagonal hj H (diagonal_from_first_row H wide)

theorem endpoint_iff_first_row (hj : IsWitness j) :
    (∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex))) ↔ FirstRowUnbounded :=
  ⟨fun ⟨γ,hγ,_⟩ => (enumeration_iff_first_row hj).mp ⟨γ,hγ⟩,endpoint_of_first_row hj⟩

theorem endpoint_of_cofinal_left_powers (hj : IsWitness j) (cof : LeftPowersCofinal j) :
    ∃ γ, Enumerates j γ ∧ leftPower j 11 (point (γ 3)) (point (γ targetIndex)) :=
  endpoint_of_first_row hj (first_row_of_left_powers_cofinal hj cof)

#print axioms endpoint_of_first_row
#print axioms endpoint_iff_first_row
end Gamma11.RankI3
