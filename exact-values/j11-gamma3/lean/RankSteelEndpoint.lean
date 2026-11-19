import RankSteelReduction
import RankEndpointGrowth
import LaverTables.Algebra.SteelCorollaries

/-! Steel's cofinality relative to the critical sequence suffices at any
actual witness, even when the height is larger than the orbit supremum. -/
set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open TableElement
variable {height : Ordinal.{u}} {j : Emb height}

theorem first_row_of_witness (hj : IsWitness j) : FirstRowUnbounded := by
  apply first_row_of_steel_crossings hj
  let e := asSteelEmbedding j
  let c := fun _ : Nat => asSteelFn j
  have moved : ∃ x, e x≠x := hj.2
  have gen (n : Nat) : LaverTables.IterMem (asSteelFn j) (c n) := LaverTables.IterMem.base
  have sup := LaverTables.iSup_critOf_appChain (j:=e) hj.1 moved (k:=c) gen
  intro b hb
  have less := LaverTables.critOf_iterMem_lt_deltaOf (j:=e) hj.1 moved hb
  rw [←sup] at less
  by_contra missing
  apply less.not_ge
  apply ciSup_le
  intro n
  exact le_of_not_gt (fun h => missing ⟨n,h⟩)

/-- At every real I3 witness, the eleventh left power sends the fourth
critical point (starting at index 0) to the point at index 2^2048. -/
theorem j11_gamma3_exact : EndpointStatement.{u} :=
  fun _ hj => endpoint_of_first_row hj (first_row_of_witness hj)

theorem j11_at_any_enumeration (hj : IsWitness j) {γ : Nat → Below height} (enum : Enumerates j γ) :
    leftPower j 11 (point (γ 3)) (point (γ targetIndex)) := by
  obtain ⟨δ,hδ,read⟩ := endpoint_of_first_row hj (first_row_of_witness hj)
  rwa [(enumerates_eq_dyadic hj enum).trans (enumerates_eq_dyadic hj hδ).symm]

/-- The same hypothesis yields the corresponding statement purely
about ordinary finite tables. -/
theorem finite_table_reading_of_I3 (h : I3.{u}) : Target := by
  obtain ⟨height,j,hj⟩ := h
  obtain ⟨γ,enum,read⟩ := endpoint_of_first_row hj (first_row_of_witness hj)
  rw [enumerates_eq_dyadic hj enum] at read
  exact (actual_endpoint_iff_target hj).mp read

#print axioms LaverTables.Steel
#print axioms first_row_of_witness
#print axioms j11_gamma3_exact
#print axioms j11_at_any_enumeration
#print axioms finite_table_reading_of_I3
#check @j11_at_any_enumeration
end Gamma11.RankI3
