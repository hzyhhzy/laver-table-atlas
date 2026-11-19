import TailRestore
import ManuscriptEndpoint

/-! Recover the finite target from one entry at the preceding column of
the geometric row. Widths are manipulated symbolically. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def GeometricPrefix : Prop :=
  (tables (targetIndex+1)).mul geometricRow (2^128-1)=2^(256^128)-2
private def LastSquare (H : FirstRowUnbounded) (w : Nat) : Prop := image H (2^w-2) w=w*w

private theorem family_last_square (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) (e : Nat) :
    LastSquare H (2^(2^e)) := special_last_image H blocks e

private theorem midpoint_with_square (H : FirstRowUnbounded) {t W : Nat} (big : 257≤t)
    (normal : entry (t+1) (entry (t+1) 11 3) 1=geometricRow)
    (old : image H geometricRow 128=W)
    (prefixEq : (tables (t+1)).mul geometricRow (2^128-1)=2^W-2)
    (last : LastSquare H W) (square : W*W=t) : entry (t+1) 11 8=2^t :=
  manuscript_midpoint_at (t:=t) (W:=W) H big normal old prefixEq (Eq.trans last square)

private theorem midpoint_at_family_width
    (H : FirstRowUnbounded) (blocks : FiniteBlockLaw) (w e : Nat)
    (key : w=2^(2^e)) (widthSq : w*w=targetIndex)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1=geometricRow)
    (old : image H geometricRow 128=w)
    (row : (tables (targetIndex+1)).mul geometricRow (2^128-1)=2^w-2) : Target := by
  have big : 257≤targetIndex := Nat.le_trans (by decide : 257≤2^9)
    (Nat.pow_le_pow_right (by decide : 0<2) (by decide : 9≤2048))
  have last : LastSquare H w := key ▸ family_last_square H blocks e
  exact midpoint_with_square (t:=targetIndex) (W:=w) H big nf old row last widthSq
private theorem image_from_preceding_column (H : FirstRowUnbounded) {d W : Nat}
    (lower : act tables (W+1) (2^W-2) 1=W) (room : W<d) (wide : 256≤d)
    (row : (tables d).mul geometricRow (2^128-1)=2^W-2) : image H geometricRow 128=W := by

  have cut := act_at_smaller_degree tables room (2^W-2) 1
  change LaverLowerBounds.FiniteTable.act tables (W+1) (2^W-2) 1=W at lower
  rw [lower] at cut
  have first : LaverLowerBounds.FiniteTable.act tables d (2^W-2) 1=W := by omega
  have arg : LaverLowerBounds.FiniteTable.signature d (geometricRow+1)=1 := by
    rw [show geometricRow+1=2^256-2^1 by decide]
    exact dyadic_tail_signature _ _ _ (by decide) wide
  have step := (tables d).row_recurrence geometricRow (2^128-1)
  rw [Nat.sub_add_cancel (Nat.two_pow_pos 128),row] at step
  have got : LaverLowerBounds.FiniteTable.act tables d geometricRow 128=W := by
    unfold LaverLowerBounds.FiniteTable.act
    rw [step,LaverLowerBounds.FiniteTable.signature_mul,arg,first]
  rw [numeral_cap_eq_min H] at got
  omega

theorem target_from_one_column (H : FirstRowUnbounded) (blocks : FiniteBlockLaw)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1=geometricRow)
    (edge : ∀ w, 1<w → act tables (w+1) (2^w-2) 1=w) (row : GeometricPrefix) : Target := by
  have bound : 256^128≤targetIndex := targetIndex_eq.symm ▸
    Nat.pow_le_pow_right (by decide : 0<256) (by decide : 128≤256)
  have wide : 256≤256^128 := Nat.pow_le_pow_right (by decide : 0<256) (by decide : 1≤128)
  have old := image_from_preceding_column (d:=targetIndex+1) (W:=256^128) H
    (edge _ (Nat.lt_of_lt_of_le (by decide : 1<256) wide)) (Nat.lt_succ_of_le bound)
    (Nat.le_trans wide (Nat.le_trans bound (Nat.le_succ _))) row
  exact midpoint_at_family_width H blocks (256^128) 10 (by decide)
    ((Nat.pow_add 256 128 128).symm.trans targetIndex_eq.symm) nf old row

#print axioms target_from_one_column
end Gamma11
