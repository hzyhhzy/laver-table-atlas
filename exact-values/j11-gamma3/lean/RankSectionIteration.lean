import RankSectionBlocks

/-! Transport the entire thirteen-argument restriction expression through
an aligned block, with an arbitrary fourteenth argument below delta_4. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement
variable {height : Ordinal.{u}}

theorem read_argument_graph {j : Emb height} (hj : IsWitness j) (n i : Nat) {x y : Rank height}
    (edge : ZFSet.pair x.val y.val ∈ (powerEmb hj.1 j n (sectionArgument hj i)).val) :
    powerEmb hj.1 j (n+1) x = y := by
  unfold sectionArgument at edge
  rw [section_natural,apply_generator] at edge
  exact (((sectionAt_spec hj.1 _ _).edge x y).mp edge).2

/-- Evaluate the mapped chain from its first expression and the transition
on each argument. The fact that the new argument belongs to the graph's
domain follows from the original evaluation edge and elementarity. -/
theorem transport_section_chain {j : Emb height} (hj : IsWitness j) (a : Emb height) (b : Nat → Nat)
    (first : a (sectionValue hj 1) = powerEmb hj.1 j (b 1) (sectionArgument hj 1))
    (step : ∀ i, 1 ≤ i → i < 13 →
      powerEmb hj.1 j (b i+1) (a (sectionArgument hj (i+1))) =
        powerEmb hj.1 j (b (i+1)) (sectionArgument hj (i+1))) :
    ∀ i, 1 ≤ i → i ≤ 13 → a (sectionValue hj i) = powerEmb hj.1 j (b i) (sectionArgument hj i) := by
  intro i
  induction i with
  | zero => omega
  | succ i ih =>
    intro _ hi
    by_cases zero : i=0
    · subst i; exact first
    have pos : 1 ≤ i := by omega
    have strict : i < 13 := by omega
    have edge := map_expansion_8_2 hj a i pos strict
    rw [ih pos strict.le] at edge
    exact (read_argument_graph hj _ _ edge).symm.trans (step i pos strict)

private def blockStart (X p i : Nat) : Nat := X+i*2^p

private theorem next_start (X p i : Nat) : blockStart X p (i+1) = blockStart X p i+2^p := by
  simp only [blockStart,Nat.succ_mul,Nat.add_assoc]

private theorem restore_start (X p i : Nat) : blockStart X p (i+1)-1+1 = blockStart X p (i+1) := by
  have pp := Nat.two_pow_pos p
  rw [next_start]; omega

private theorem block_step {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {X p : Nat} (align : 4 ∣ p) (div : 2^(p+4) ∣ X)
    (i : Nat) (x : Rank height) (small : x.val.rank < (dyadicPoint hj 4).val) :
    powerEmb hj.1 j (blockStart X p i) (powerEmb hj.1 j (X+2^p-1) x) =
      powerEmb hj.1 j (blockStart X p (i+1)-1) x := by
  have mul : 2^p ∣ i*2^p := dvd_mul_left _ _
  have base : 2^p ∣ blockStart X p i := Nat.dvd_add
    ((Nat.pow_dvd_pow 2 (Nat.le_add_right p 4)).trans div) mul
  rw [block_action_8_4 hj H law align div x small,next_start]
  exact (block_action_8_3 hj H law align base x small).symm

theorem shifted_section_chain {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {X p : Nat} (align : 4 ∣ p) (div : 2^(p+4) ∣ X)
    {i : Nat} (pos : 1 ≤ i) (inside : i ≤ 13) :
    powerEmb hj.1 j (X+2^p-1) (sectionValue hj i) =
      powerEmb hj.1 j (X+(i+1)*2^p-1) (sectionArgument hj i) := by
  let R := powerEmb hj.1 j (X+2^p-1)
  apply transport_section_chain hj R (fun k => blockStart X p (k+1)-1) _ _ i pos inside
  · have pp := Nat.two_pow_pos p
    have c := (applyEmb_commutes hj.1 R j (sectionArgument hj 1)).symm
    rw [show applyEmb hj.1 R j = powerEmb hj.1 j (blockStart X p 1) by
      dsimp [R]; rw [apply_generator]; congr 1; simp only [blockStart,Nat.one_mul]; omega] at c
    exact c.trans (block_step hj H law align div 1 _ (argument_below_four hj 1))
  · intro k _ _
    rw [restore_start]
    exact block_step hj H law align div (k+1) _ (argument_below_four hj _)

private theorem thirteenth_has_room {j : Emb height} (hj : IsWitness j) :
    dyadicPoint hj 4 ≤ ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 2) := by
  apply ((dyadicPoint_strict hj).monotone (by decide : 4≤9)).trans
  apply (native_cut hj (by decide : 0<13) 2 9).mp
  exact (canonical_mul 9 13 4).symm.trans (LowProducts.v13_4 _)

/-- The last argument is arbitrary, so this also works for a restriction
to delta_1 instead of delta_2 in the last position of (8.2). -/
theorem shifted_fourteen {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {X p : Nat} (align : 4 ∣ p) (div : 2^(p+4) ∣ X)
    (x : Rank height) (small : x.val.rank < (dyadicPoint hj 4).val) :
    powerEmb hj.1 j (X+2^p-1) (powerEmb hj.1 j 14 x) = powerEmb hj.1 j (X+15*2^p-1) x := by
  let R := powerEmb hj.1 j (X+2^p-1)
  have source : ZFSet.pair x.val (powerEmb hj.1 j 14 x).val ∈ (sectionValue hj 13).val := by
    rw [sectionValue_as_restriction hj 13]
    exact ((sectionAt_spec hj.1 _ _).edge _ _).mpr ⟨small.trans_le (thirteenth_has_room hj),rfl⟩
  have mapped := (map_edge hj.1 R _ _ _).mpr source
  change ZFSet.pair _ _ ∈ (powerEmb hj.1 j (X+2^p-1) (sectionValue hj 13)).val at mapped
  rw [shifted_section_chain hj H law align div (by decide : 1≤13) (le_refl 13)] at mapped
  have read := (read_argument_graph hj _ _ mapped).symm
  change R _ = powerEmb hj.1 j (blockStart X p (13+1)-1+1) (R x) at read
  rw [restore_start] at read
  exact read.trans (block_step hj H law align div 14 x small)

#print axioms shifted_section_chain
#print axioms shifted_fourteen
end Gamma11.RankI3
