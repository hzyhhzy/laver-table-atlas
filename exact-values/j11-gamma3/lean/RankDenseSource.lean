import RankWideSource
import RepeatDensity
import DoubleWidths

/-! Critical-interval bounds give both carry cases for the square of
65534 in the actual target table. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem even_and_square {d : Nat} (room : 272≤d) (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    (four : act tables d 14 4=16) (wide : MovedBelow256 d) :
    (∀ y, y%2≠0 → y+1<65536 → (tables d).mul (repeatBits 16 16 y) 65535=repeatBits 16 16 (y+1)) ∧
    (MixedWidth16 d → entry d 65534 65534=2^256-2^16) := by
  have cond (r z : Nat) (lo : 16≤r) (hi : r<256) (sig : signature d z=r)
      (move : 256≤act tables d z r) : d≤act tables d z 256 := Nat.le_of_eq (wide r z lo hi sig move).symm
  have even (y : Nat) (odd : y%2≠0) (fit : y+1<65536) :=
    even_stretched_step H law (n:=16) ⟨4,rfl⟩ (by decide) (by omega : 16*16≤d)
      (upper_bridges_16 (by omega) four) cond odd fit
  exact ⟨even,fun mixed => square_of_mixed_16 (by omega) mixed even⟩

theorem even_carries_and_target_square {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) (h16 : SixteenRowData) :
    (∀ y, y%2≠0 → y+1<65536 → (tables (targetIndex+1)).mul (repeatBits 16 16 y) 65535 =
      repeatBits 16 16 (y+1)) ∧
    (MixedWidth16 (targetIndex+1) → entry (targetIndex+1) 65534 65534=2^256-2^16) := by
  have cap : 512≤targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 9≤2048)
  have room : 272≤targetIndex+1 := Nat.le_trans (by decide : 272≤512) (Nat.le_trans cap (Nat.le_succ _))
  exact even_and_square (d:=targetIndex+1) room H law (fourteen_at_target hj H law) (appendix_C2 hj H law h16)

#print axioms even_carries_and_target_square

private theorem square_at_degree {m : Nat} (room : 272≤m) (scale : m-1≤256^256)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) (hom : SixteenRowData)
    (four : act tables m 14 4=16) (two : act tables m 13 2=16)
    (atFour : ∀ k, signature m k=4 → 256≤act tables m k 4 → act tables m k 256=m)
    (wide : MovedBelow256 m) : entry m 65534 65534=2^256-2^16 := by
  have project (a k : Nat) (val : act tables m a k=16) : act tables 256 a k=16 := by
    rw [act_at_smaller_degree tables (by omega : 256≤m),val]
    decide
  have native := native_periods_16 (project _ _ four) (project _ _ two)
  have cap := mixed_to_cap room scale native hom four atFour wide
  exact (even_and_square room H law four wide).2 (mixed_width_of_cap cap)

theorem target_square_of_row_data {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) (h16 : SixteenRowData) :
    entry (targetIndex+1) 65534 65534=2^256-2^16 := by
  have cap : 512≤targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 9≤2048)
  have room : 272≤targetIndex+1 := Nat.le_trans (by decide : 272≤512) (Nat.le_trans cap (Nat.le_succ _))
  exact square_at_degree (m:=targetIndex+1) room (Nat.le_of_eq targetIndex_eq) H law h16
    (fourteen_at_target hj H law) (thirteen_two_at_target hj H law)
    (fun _ => full_small_critical_bound hj H law h16 (Nat.le_refl 4) (by decide)) (appendix_C2 hj H law h16)

#print axioms target_square_of_row_data

theorem target_square {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) :
    entry (targetIndex+1) 65534 65534=2^256-2^16 :=
  target_square_of_row_data hj H law (sixteen_data_from_blocks H law)

#print axioms target_square
end Gamma11.RankI3
