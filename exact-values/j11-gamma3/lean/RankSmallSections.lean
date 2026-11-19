import RankLowCrossings

/-! Dougherty II (8.2), as a sequence of genuine evaluations of sets
coding partial functions. Applying any embedding to all thirteen terms
preserves each edge of that sequence. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

/-- Argument positions in (8.2) use the one-based indexing of J_i. -/
def sectionLevel : Nat → Nat
  | 5 | 6 | 7 | 9 | 10 | 11 => 1
  | _ => 2

noncomputable def sectionArgument {j : Emb height} (hj : IsWitness j) (i : Nat) : Rank height :=
  sectionAt hj.1 j (dyadicPoint hj (sectionLevel i))

noncomputable def sectionValue {j : Emb height} (hj : IsWitness j) (i : Nat) : Rank height :=
  powerEmb hj.1 j i (sectionArgument hj i)

private theorem argument_bound {j : Emb height} (hj : IsWitness j) (i : Nat) :
    (sectionArgument hj i).val.rank < (dyadicPoint hj (if sectionLevel i=1 then 2 else 4)).val := by
  obtain ⟨one,two⟩ := bounded_generator_sections hj
  have options : sectionLevel i=1 ∨ sectionLevel i=2 := by fun_cases sectionLevel i <;> simp_all
  rcases options with h|h
  · simpa [sectionArgument,h] using one
  · simpa [sectionArgument,h] using two

private theorem section_certificate (i : Nat) (positive : 1 ≤ i) (hi : i < 13) :
    ∃ v y : Nat, (tables 9).mul i (2^(sectionLevel i)) = v ∧ signature 9 v = y ∧ y<9 ∧
      (if sectionLevel (i+1)=1 then 2 else 4) ≤ y := by
  rcases (show i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,4,LowProducts.v1_4 _,by decide,by decide,by decide⟩
  · exact ⟨_,4,LowProducts.v2_4 _,by decide,by decide,by decide⟩
  · exact ⟨_,4,LowProducts.v3_4 _,by decide,by decide,by decide⟩
  · exact ⟨_,3,LowProducts.v4_4 _,by decide,by decide,by decide⟩
  · exact ⟨_,3,LowProducts.v5_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,3,LowProducts.v6_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,4,LowProducts.v7_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,2,LowProducts.v8_4 _,by decide,by decide,by decide⟩
  · exact ⟨_,2,LowProducts.v9_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,2,LowProducts.v10_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,4,LowProducts.v11_2 _,by decide,by decide,by decide⟩
  · exact ⟨_,4,LowProducts.v12_4 _,by decide,by decide,by decide⟩

theorem argument_below_four {j : Emb height} (hj : IsWitness j) (i : Nat) :
    (sectionArgument hj i).val.rank < (dyadicPoint hj 4).val :=
  (argument_bound hj i).trans_le ((dyadicPoint_strict hj).monotone (by split <;> decide))

theorem sectionValue_as_restriction {j : Emb height} (hj : IsWitness j) (i : Nat) :
    sectionValue hj i = sectionAt hj.1 (powerEmb hj.1 j (i+1))
      (ordinalImage (powerEmb hj.1 j i) (dyadicPoint hj (sectionLevel i))) := by
  unfold sectionValue sectionArgument
  rw [section_natural,apply_generator]

/-- Start at j applied to the first restriction, follow the twelve
edges, and read the final set as the graph of J14 below J13(delta_2). -/
theorem expansion_8_2 {j : Emb height} (hj : IsWitness j) :
    sectionValue hj 1 = j (sectionAt hj.1 j (dyadicPoint hj 2)) ∧
    (∀ i, 1 ≤ i → i < 13 → ZFSet.pair (sectionArgument hj (i+1)).val (sectionValue hj (i+1)).val ∈
      (sectionValue hj i).val) ∧
    sectionValue hj 13 = sectionAt hj.1 (powerEmb hj.1 j 14)
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 2)) := by
  refine ⟨rfl,?_,sectionValue_as_restriction hj 13⟩
  intro i positive hi
  obtain ⟨v,y,raw,index,vis,adequate⟩ := section_certificate i positive hi
  have read := read9 hj positive raw index vis
  rw [sectionValue_as_restriction hj i]
  apply ((sectionAt_spec hj.1 _ _).edge _ _).mpr
  refine ⟨?_,rfl⟩
  rw [read]
  exact (argument_bound hj (i+1)).trans_le ((dyadicPoint_strict hj).monotone adequate)

theorem map_expansion_8_2 {j : Emb height} (hj : IsWitness j) (a : Emb height) (i : Nat)
    (positive : 1 ≤ i) (hi : i < 13) :
    ZFSet.pair (a (sectionArgument hj (i+1))).val (a (sectionValue hj (i+1))).val ∈
      (a (sectionValue hj i)).val :=
  (map_edge hj.1 a _ _ _).mpr ((expansion_8_2 hj).2.1 i positive hi)

#print axioms expansion_8_2
end Gamma11.RankI3
