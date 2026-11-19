import TwelveCut
import CriticalFour
import EndpointAssembly
import ShortPeriod

/-! Finish Appendix D.3 from its one remaining product at the target
degree. The known product of 65534 with itself at degree 256 would
not suffice in place of this hypothesis. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- Precisely the degrees to which a supplied width-16 stretch transfers
this square by direct projection. For the source A_17 this includes A_272. -/
theorem normal_square_in_stretch_range {n d : Nat} (source : 16≤n) (lo : 256≤d) (hi : d≤n*16)
    (hom : StretchHomAt 16 n) : entry d 65534 65534=2^256-2^16 := by
  have fit16 : 65534<2^16 := by decide
  have fits := Nat.lt_of_lt_of_le fit16 (Nat.pow_le_pow_right (by decide : 0<2) source)
  have exactRow := stretch_row (by decide : 0<16) (by omega : 0<n) hom 65534 fits
  rw [repeatBits_padding 16 16 n 65534 source fit16] at exactRow
  have pr := (tables (n*16)).projection (tables d) (Nat.pow_dvd_pow 2 hi) 65534 65534
  change (tables (n*16)).mul 65534 65534=repeatBits 16 16 65534 at exactRow
  rw [exactRow,show repeatBits 16 16 65534=2^256-2^16 by decide,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 2^256-2^16<2^256) (Nat.pow_le_pow_right (by decide) lo))] at pr
  exact (canonical_mul d _ _).symm.trans pr.symm

theorem normal_form_of_last_product {d : Nat} (room : 256≤d) (upper : d≤targetIndex+1)
    (r : entry d 13 2=65520) (l : entry d 13 3=65534)
    (square : entry d 65534 65534=2^256-2^16)
    (b3 : entry d (2^256-2^16) 65520=2^256-16) :
    entry d (entry d 11 3) 1=geometricRow := by
  have d9 : 9≤d := by omega
  have pow := Nat.pow_le_pow_right (by decide : 0<2) room
  have next (i : Nat) (small : i≤13) : (tables d).mul i 1=i+1 :=
    ((tables d).mul_one i).trans (Nat.mod_eq_of_lt (by omega))
  have r0 := (canonical_mul d 13 2).trans r
  have l0 := (canonical_mul d 13 3).trans l
  obtain ⟨s,p,uu⟩ := normal_transports tables d d9 upper
  rw [l0,(canonical_mul d 65534 65534).trans square] at s
  rw [s] at p
  have rr := (tables d).mul_distrib 13 1 1
  rw [next 1 (by decide),next 13 (by decide),r0] at rr
  rw [p,← (tables d).mul_distrib,← rr,(canonical_mul d _ _).trans b3] at uu
  have k2 := (tables d).row_recurrence 11 1
  rw [next 11 (by decide),uu] at k2
  have size := upper
  rw [targetIndex_eq] at size
  have b1 := protected_prefix_twelve tables d9 (by decide : 5≤256) room size
  have k3 := (tables d).row_recurrence 11 2
  rw [k2,b1] at k3
  rw [← canonical_mul d 11 3,k3,← canonical_mul,(tables d).mul_one,
    Nat.mod_eq_of_lt (by omega : 2^256-4+1<2^d)]

#print axioms normal_form_of_last_product
#print axioms normal_square_in_stretch_range
end Gamma11
