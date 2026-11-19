import EndpointAssembly
import LaverLowerBounds.StandardLine

/-! The endpoint argument in §6 of the original manuscript, which stops at
2^128-1. This is separate from the alternative 2^255 midpoint argument. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds TableElement

theorem numeral_cap_eq_min (H : FirstRowUnbounded) (d a x : Nat) :
    FiniteTable.act tables d a x = min d (image H a x) := by
  have h := (numeral a).cap_eq_min (numeral_total H a) d x
  change FiniteTable.signature d ((tables d).mul (a % 2^d) (2^x)) = min d (image H a x) at h
  rw [(tables d).mul_mod_left] at h
  exact h

theorem standard_128 (H : FirstRowUnbounded) : image H (2^128-1) 128 = 256 := by
  have fin : FiniteTable.act tables 257 (2^128-1) 128 = 256 :=
    (FiniteTable.standard_segment tables 257 7 (by decide)).2.2
  rw [numeral_cap_eq_min H] at fin
  omega

theorem read_application_at_cut (H : FirstRowUnbounded) {A B C d x z y t : Nat}
    (rep : ((numeral A).app (numeral B)).rep d = (numeral C).rep d)
    (ax : image H A x = z) (bx : image H B x = y) (cz : image H C z = t) (lt : t < d) :
    image H A y = t := by
  have rd := ((numeral A).app (numeral B)).finite_read (numeral C)
    (total_app (numeral_total H A) (numeral_total H B)) (numeral_total H _) d (image H A x) rep
  rw [index_app (numeral_total H A) (numeral_total H B)] at rd
  change min d (image H A (image H B x)) = min d (image H C (image H A x)) at rd
  rw [ax, bx, cz] at rd
  omega

/-- Once the protected prefix reaches 2^128-1, the standard 128→256
segment and Dougherty's 7.2(c) determine the value itself. -/
theorem manuscript_midpoint_at (H : FirstRowUnbounded) {t W : Nat} (big : 257 ≤ t)
    (nf : entry (t + 1) (entry (t + 1) 11 3) 1 = geometricRow)
    (oldImage : image H geometricRow 128 = W)
    (atPrefix : (tables (t + 1)).mul geometricRow (2^128-1) = 2^W-2)
    (squareImage : image H (2^W-2) W = t) : entry (t+1) 11 8 = 2^t := by
  let d := t + 1
  let E := 2 ^ 128 - 1
  let V := 2 ^ W - 2
  have stored : (tables d).mul geometricRow E = V := atPrefix
  have small : V < 2 ^ d := stored ▸ (tables d).mul_lt geometricRow E
  have rep : ((numeral geometricRow).app (numeral E)).rep d = (numeral V).rep d := by
    change (tables d).mul (geometricRow % 2^d) (E % 2^d) = V % 2^d
    rw [(tables d).mul_mod_left, (tables d).mul_mod_right, Nat.mod_eq_of_lt small]
    exact atPrefix
  have image256 := read_application_at_cut H rep oldImage (standard_128 H) squareImage (Nat.lt_succ_self _)
  have norm := normal_form_reduction tables d 256 (by dsimp [d]; omega) (by decide) (by dsimp [d]; omega)
    (by simpa only [canonical_mul] using nf)
  apply (exact_iff_act tables 11 3 t).mpr
  change FiniteTable.act tables d 11 3 = _
  rw [norm.2, numeral_cap_eq_min H]
  change min d (image H geometricRow 256) = t
  rw [image256, Nat.min_eq_right (Nat.le_succ _)]

theorem manuscript_midpoint_conclusion (H : FirstRowUnbounded)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow)
    (oldImage : image H geometricRow 128 = 256 ^ 128)
    (atPrefix : (tables (targetIndex+1)).mul geometricRow (2^128-1) = 2^(256^128)-2)
    (squareImage : image H (2^(256^128)-2) (256^128) = (256^128)*(256^128)) : Target := by
  have sq : (256^128)*(256^128) = targetIndex := (Nat.pow_add 256 128 128).symm.trans targetIndex_eq.symm
  have big : 257 ≤ targetIndex := Nat.le_trans (by decide : 257 ≤ 2 ^ 9)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 9 ≤ 2048))
  exact manuscript_midpoint_at H big nf oldImage atPrefix (squareImage.trans sq)

#print axioms manuscript_midpoint_conclusion
end Gamma11
