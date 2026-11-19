import RankSectionIteration
import BinarySlices

/-! The two constants in Dougherty II §8. The binary carry law for
fourfold stretches supplies all fourteen source positions. The
equalities on V_mu are deduced before reading in A_(T+1).
-/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement
variable {height : Ordinal.{u}}

/-- Stretch a four-bit argument by replacing each bit with four copies. -/
private abbrev stretch4 := repeatBits 4 4

private theorem stretched_step {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {i : Nat} (short : i<14) (x : Rank height)
    (small : x.val.rank < (dyadicPoint hj 4).val) :
    powerEmb hj.1 j (stretch4 i) (powerEmb hj.1 j 14 x) = powerEmb hj.1 j (stretch4 (i+1)-1) x := by
  obtain ⟨X,p,align,_,div,a,tail⟩ := repeatBits_carry 4 4 i (by omega)
  have b : stretch4 (i+1) = X+15*2^p := tail.trans (congrArg (X+·) (Nat.mul_comm _ _))
  exact (congrArg (fun n => powerEmb hj.1 j n (powerEmb hj.1 j 14 x)) a).trans
    ((shifted_fourteen hj H law align div x small).trans
      (congrArg (fun n => powerEmb hj.1 j (n-1) x) b.symm))

private theorem stretched_chain {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {i : Nat} (pos : 1 ≤ i) (inside : i ≤ 13) :
    powerEmb hj.1 j 14 (sectionValue hj i) = powerEmb hj.1 j (stretch4 (i+1)-1) (sectionArgument hj i) := by
  let a := powerEmb hj.1 j 14
  apply transport_section_chain hj a (fun i => stretch4 (i+1)-1) _ _ i pos inside
  · have c := (applyEmb_commutes hj.1 a j (sectionArgument hj 1)).symm
    exact c.trans (stretched_step hj H law (by decide : 1<14) _ (argument_below_four hj 1))
  · intro k _ hi
    have small : k+1 < 14 := by omega
    have positive : 0<stretch4 (k+1) := repeatBits_pos (by decide) (by omega) (by omega)
    rw [Nat.sub_add_cancel positive]
    exact stretched_step hj H law small _ (argument_below_four hj (k+1))

private theorem mapped_first {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) :
    powerEmb hj.1 j 13 (sectionValue hj 1) = powerEmb hj.1 j 65519 (sectionArgument hj 13) := by
  let C := powerEmb hj.1 j 13
  have c := (applyEmb_commutes hj.1 C j (sectionArgument hj 1)).symm
  exact c.trans (stretched_chain hj H law (by decide : 1≤13) (le_refl 13))

private theorem mapped_second {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) :
    powerEmb hj.1 j 13 (sectionValue hj 2) = powerEmb hj.1 j 65533 (sectionArgument hj 13) := by
  let C := powerEmb hj.1 j 13
  have h := map_expansion_8_2 hj C 1 (by decide) (by decide)
  change ZFSet.pair _ _ ∈ (powerEmb hj.1 j 13 (sectionValue hj 1)).val at h
  rw [mapped_first hj H law] at h
  have r := (read_argument_graph hj 65519 13 h).symm
  exact r.trans (shifted_section_chain hj H law (p:=0) (X:=65520) (by decide) (by decide)
    (i:=13) (by decide) (by decide))

private theorem section_coincidence {j : Emb height} (hj : IsWitness j) {A : Emb height} {μ : Below height}
    (k : Nat) (s : sectionAt hj.1 A μ = powerEmb hj.1 j k (sectionArgument hj 13)) (x : Rank height)
    (small : x.val.rank < μ.val) : A x = powerEmb hj.1 j (k+1) x := by
  have h := ((sectionAt_spec hj.1 A μ).edge x (A x)).mpr ⟨small,rfl⟩
  rw [s] at h
  exact (read_argument_graph hj k 13 h).symm

/-- Both ordinary restriction identities on V_(J13(delta_4)). -/
theorem two_ordinary_restrictions {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (a k : Nat) (which : (a=2 ∧ k=65520) ∨ (a=3 ∧ k=65534))
    (x : Rank height) (small : x.val.rank < (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)).val) :
    applyEmb hj.1 (powerEmb hj.1 j 13) (powerEmb hj.1 j a) x = powerEmb hj.1 j k x := by
  let δ := dyadicPoint hj
  let e := powerEmb hj.1 j
  have s1 : sectionValue hj 1 = sectionAt hj.1 (e 2) (δ 4) := by
    have eqv := sectionValue_as_restriction hj 1
    change sectionValue hj 1 = sectionAt hj.1 (e 2) (ordinalImage j (δ 2)) at eqv
    rwa [generator_two hj] at eqv
  have s2 : sectionValue hj 2 = sectionAt hj.1 (e 3) (δ 4) := by
    have eqv := sectionValue_as_restriction hj 2
    change sectionValue hj 2 = sectionAt hj.1 (e 3) (ordinalImage (e 2) (δ 2)) at eqv
    have b2 : ordinalImage (e 2) (δ 2) = δ 4 := read9 hj (by decide) (LowProducts.v2_4 _) (by decide) (by decide)
    rwa [b2] at eqv
  rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · apply section_coincidence hj 65519 _ x small
    rw [← section_natural,← s1]
    exact mapped_first hj H law
  · apply section_coincidence hj 65533 _ x small
    rw [← section_natural,← s2]
    exact mapped_second hj H law

theorem two_target_constants {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded) (law : FiniteBlockLaw) :
    entry (targetIndex+1) 13 2 = 65520 ∧ entry (targetIndex+1) 13 3 = 65534 :=
  thirteen_two_and_three_of_restrictions hj (two_ordinary_restrictions hj H law)

#print axioms two_ordinary_restrictions
#print axioms two_target_constants
end Gamma11.RankI3
