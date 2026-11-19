import StretchComposition
import TailRestore
import WidePeriods

/-! Only the local restoration of one dyadic digit block and the old
geometric diagonal are needed in addition to the normal form, wide
periods and first-row unboundedness. -/
set_option autoImplicit false
set_option exponentiation.threshold 512
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

theorem short_periods_from_restore (H : FirstRowUnbounded) (restore : RestoreBlockLaw) :
    ∀ m, 0<m → ∀ x, 1≤x → x≤2^(256^m)-2 → entry (256*256^m) x (2^(256^m))=0 := by
  have law : FiniteBlockLaw := finite_block_of_restore restore
  apply short_period_induction_with_last (auxiliary_stretches_from_blocks H law)
    (mixed_periods_of_restore H law restore)
  intro m mp
  let w := 256^m
  have ge : 256≤w := Nat.pow_le_pow_right (by decide : 0<256) mp
  have reached := (licensed_readings H law m mp).2
  apply (numeral_zero_iff H _ _ _).mpr
  exact Nat.le_trans (Nat.le_of_eq reached.symm) (index_mono (numeral_total H (2^w-2)) ge)

theorem target_from_local_restoration (H : FirstRowUnbounded) (restore : RestoreBlockLaw)
    (diag : DiagonalHomAt 256 targetIndex) (wide : WidePeriodEstimates targetIndex)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1=geometricRow) : Target := by
  have law : FiniteBlockLaw := finite_block_of_restore restore
  apply target_of_table_readings H law diag (fun m mp => (licensed_readings H law m mp).1)
    (fun m mp => (licensed_readings H law m mp).2) _ nf
  have rowBound : geometricRow<2^256-2 := by decide
  refine ⟨fun b bp stop => wide.native b bp (Nat.lt_trans stop rowBound),?_,?_⟩
  · intro A pos fit aligned b bp stop
    exact wide.background A pos (Nat.lt_trans fit (Nat.pow_lt_pow_succ (by decide))) aligned
      b bp (Nat.lt_trans stop rowBound)
  · intro m mp
    dsimp only
    intro b lo hi
    exact short_periods_from_restore H restore m mp b lo (Nat.le_of_lt hi)

#print axioms short_periods_from_restore
#print axioms target_from_local_restoration
end Gamma11
