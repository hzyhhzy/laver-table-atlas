import RankSectionConstants
import FullBlockFour

/-! Identify the smaller source used in the normal-form argument.
Only the degree-256 square and visible actions of row 65534 are used
in addition to the two section constants.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement
variable {height : Ordinal.{u}}

/-- The first moved position of a single run of ones lands exactly at
its right edge. The square vanishes at degree b and survives at b+1. -/
theorem run_moves_to_edge (F : BinaryFamily) {s b : Nat} (sb : s<b) :
    act F (b+1) (2^b-2^s) s = b := by
  let a := 2^b-2^s
  have pos : 0<a := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) sb)
  have fit : a<2^b := by dsimp [a]; have := Nat.two_pow_pos s; have := Nat.two_pow_pos b; omega
  have fit' := fit.trans (Nat.pow_lt_pow_succ (by decide : 1<2))
  have sz (d : Nat) (bd : b≤d) : signature d a=s := dyadic_tail_signature d b s sb bd
  have low : (F b).mul a a=0 := (square_zero_iff F b a fit).mpr (Or.inr ⟨s,sb,rfl⟩)
  have high : (F (b+1)).mul a a ≠ 0 := by
    intro zero
    rcases (square_zero_iff F _ _ fit').mp zero with hz|⟨k,hk,eqv⟩
    · omega
    · have kBound := Nat.pow_le_pow_right (by decide : 0<2) (show k≤b by omega)
      rw [Nat.pow_succ] at eqv
      omega
  have l := signature_mul F b a a
  rw [low,signature_zero,sz b le_rfl] at l
  have cap := act_at_smaller_degree F (Nat.le_succ b) a s
  have h := signature_mul F (b+1) a a
  rw [sz _ (Nat.le_succ _)] at h
  have bound := (F (b+1)).mul_lt a a
  have hi : signature (b+1) ((F (b+1)).mul a a) < b+1 := by
    apply Nat.lt_of_not_ge
    intro top
    exact high ((Nat.mod_eq_of_lt bound).symm.trans ((le_signature _ _ _ le_rfl).mp top))
  rw [h] at hi
  change act F (b+1) a s=b
  exact Nat.le_antisymm (Nat.le_of_lt_succ hi) ((l.trans cap).le.trans (Nat.min_le_right ..))

private theorem read_mapped_restriction {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {a k : Nat} (which : (a=2 ∧ k=65520) ∨ (a=3 ∧ k=65534))
    {x : Below height} (small : x < dyadicPoint hj 4) :
    ordinalImage (powerEmb hj.1 j 13) (ordinalImage (powerEmb hj.1 j a) x) =
      ordinalImage (powerEmb hj.1 j k) (ordinalImage (powerEmb hj.1 j 13) x) := by
  let C := powerEmb hj.1 j 13
  let β := ordinalImage C x
  have below := (ordinalImage_strictMono C) small
  have rank : (point β).val.rank < (ordinalImage C (dyadicPoint hj 4)).val := by
    change β.val.toZFSet.rank < _
    rw [Ordinal.rank_toZFSet]; exact below
  have h := two_ordinary_restrictions hj H law a k which (point β) rank
  rw [ordinalImage_spec,ordinalImage_spec] at h
  exact (ordinalImage_commutes hj.1 C _ x).symm.trans (point_injective h)

theorem thirteen_second_image {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) : ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 2) = dyadicPoint hj 16 := by
  let δ := dyadicPoint hj
  let e := powerEmb hj.1 j
  have b1 : ordinalImage (e 2) (δ 1)=δ 2 := read9 hj (by decide) (LowProducts.v2_2 _) (by decide) (by decide)
  have c1 : ordinalImage (e 13) (δ 1)=δ 4 := read9 hj (by decide) (LowProducts.v13_2 _) (by decide) (by decide)
  have h := read_mapped_restriction hj H law (Or.inl ⟨rfl,rfl⟩ : (2=2 ∧ 65520=65520) ∨ (2=3 ∧ 65520=65534))
    ((dyadicPoint_strict hj) (by decide : 1<4))
  rw [b1,c1] at h
  exact h.trans (native_read_act hj (a:=65520) (by decide) (run_moves_to_edge tables (by decide : 4<16)) (by decide))

theorem small_square_of_row_data {j : Emb height} (hj : IsWitness j)
    (hom : SixteenRowData) :
    ordinalImage (powerEmb hj.1 j 65534) (dyadicPoint hj 16) = dyadicPoint hj 256 := by
  have value := hom.action (Nat.le_refl 272) (by decide : 16<17)
  exact native_read_act hj (by decide) value (by decide)

theorem early_source {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (hom : SixteenRowData) :
    ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) = dyadicPoint hj 256 ∧
      ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2) = dyadicPoint hj 256 := by
  have c2 := thirteen_second_image hj H law
  have g2 : ordinalImage (powerEmb hj.1 j 3) (dyadicPoint hj 2) = dyadicPoint hj 4 :=
    read9 hj (by decide) (LowProducts.v3_4 _) (by decide) (by decide)
  have h := read_mapped_restriction hj H law (Or.inr ⟨rfl,rfl⟩ : (3=2 ∧ 65534=65520) ∨ (3=3 ∧ 65534=65534))
    ((dyadicPoint_strict hj) (by decide : 2<4))
  rw [g2,c2] at h
  have first := h.trans (small_square_of_row_data hj hom)
  exact ⟨first,(restriction_source hj).symm.trans first⟩

theorem fourteen_at_target {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) : act tables (targetIndex+1) 14 4=16 := by
  have one : ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 1)=dyadicPoint hj 4 :=
    read9 hj (by decide) (LowProducts.v13_2 _) (by decide) (by decide)
  have j1 : ordinalImage j (dyadicPoint hj 1)=dyadicPoint hj 2 :=
    read9 hj (a:=1) (by decide) (LowProducts.v1_2 _) (by decide) (by decide)
  have four := ordinalImage_commutes hj.1 (powerEmb hj.1 j 13) j (dyadicPoint hj 1)
  rw [apply_generator,one,j1,thirteen_second_image hj H law] at four
  have f := (dyadicPoint_strict hj).injective ((native_image_of_index hj H (a:=14) (by decide) 4).symm.trans four)
  have cap : 256 ≤ targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  rw [numeral_cap_eq_min H,f,Nat.min_eq_right (by omega)]

theorem thirteen_four_target_bound {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (h16 : SixteenRowData) : act tables (targetIndex+1) 13 4 ≤ 256 := by
  have index := (dyadicPoint_strict hj).injective
    ((native_image_of_index hj H (a:=13) (by decide) 4).symm.trans (early_source hj H law h16).1)
  rw [numeral_cap_eq_min H,index]; exact Nat.min_le_right ..

theorem full_small_critical_bound {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (h16 : SixteenRowData)
    {r a : Nat} (lower : 4≤r) (upper : r<16) (crit : signature (targetIndex+1) a=r)
    (jump : 256 ≤ act tables (targetIndex+1) a r) : act tables (targetIndex+1) a 256=targetIndex+1 := by
  have read := thirteen_four_target_bound hj H law h16
  have cap : 256 ≤ targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  apply critical_four_to_fifteen (by omega) (by decide) (fourteen_at_target hj H law) _ r a lower upper crit jump
  intro z zc zj
  exact critical_four_actor tables (by decide) (by omega) cap targetIndex_eq read zc zj

/-- Keep the degree symbolic in the finite calculation. In particular this
    proof does not materialize the cardinality of the target table. -/
def AdditionPrefix16 (d : Nat) : Prop :=
  ∀ e : Nat, e<2^d → signature d e=16 → 256≤act tables d e 16 →
    ∀ i, i<65520 → (tables d).mul e (i+1)=e+(i+1)

private theorem addition_from_small {d : Nat} (room : 256≤d) (scale : d-1≤256^256)
    (four : act tables d 14 4=16) (small : ∀ {r a}, 4≤r → r<16 →
      signature d a=r → 256≤act tables d a r → act tables d a 256=d) : AdditionPrefix16 d :=
  fun _ fit crit jump => full_sixteen_prefix room scale four
    (fun _ => small (Nat.le_refl 4) (by decide : 4<16)) fit crit jump

private theorem addition_at_run {d : Nat} (room : 257≤d) (additions : AdditionPrefix16 d) :
    entry d (2^256-2^16) 65520 = 2^256-16 := by
  let v := 2^256-2^16
  have fit : v<2^d := Nat.lt_of_lt_of_le (show v<2^256 by decide)
    (Nat.pow_le_pow_right (by decide) (by omega : 256≤d))
  have sig : signature d v=16 := dyadic_tail_signature d 256 16 (by decide) (by omega)
  have hit := run_moves_to_edge tables (by decide : 16<256)
  have pr := act_at_smaller_degree tables room v 16
  change act tables (256+1) v 16=256 at hit
  have jump : 256≤act tables d v 16 := (hit.symm.trans pr).le.trans (Nat.min_le_right ..)
  have h := additions v fit sig jump 65519 (by decide)
  rw [← canonical_mul]
  exact h.trans (by decide)

theorem appendix_B3 {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (h16 : SixteenRowData) : AdditionPrefix16 (targetIndex+1) := by
  have cap : 256 ≤ targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  exact addition_from_small (Nat.le_trans cap (Nat.le_succ _))
    ((Nat.add_sub_cancel targetIndex 1).le.trans targetIndex_eq.le)
    (fourteen_at_target hj H law) (@full_small_critical_bound _ _ hj H law h16)

theorem appendix_B3_endpoint {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) (h16 : SixteenRowData) :
    entry (targetIndex+1) (2^256-2^16) 65520 = 2^256-16 := by
  have cap : 256 ≤ targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  exact addition_at_run (Nat.succ_le_succ cap) (appendix_B3 hj H law h16)

#print axioms run_moves_to_edge
#print axioms thirteen_second_image
#print axioms early_source
#print axioms full_small_critical_bound
#print axioms appendix_B3
#print axioms appendix_B3_endpoint
end Gamma11.RankI3
