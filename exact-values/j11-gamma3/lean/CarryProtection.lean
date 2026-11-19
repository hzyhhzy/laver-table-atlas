import SpectrumTransfer

/-! Protection of the outer and inner carries (equations 5, 7 and 8).
The hypotheses refer to indices of the shorter rows or to entries in the old
table. The conclusion refers to the extra bit in the native lift. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds TableElement

noncomputable abbrev image (H : FirstRowUnbounded) (a x : Nat) : Nat :=
  (numeral a).index (numeral_total H a) x

theorem index_mono {A : TableElement} (hA : A.Total) {x y : Nat} (h : x ≤ y) :
    A.index hA x ≤ A.index hA y := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (A.index_strict hA h)

theorem native_truncation (H : FirstRowUnbounded) (A : TableElement) (hA : A.Total)
    (t x : Nat) : min t (image H (A.rep t) x) = min t (A.index hA x) :=
  (numeral (A.rep t)).finite_read A (numeral_total H _) hA t x (Nat.mod_eq_of_lt (A.bound t))

theorem native_strict_to_actual (H : FirstRowUnbounded) (A : TableElement) (hA : A.Total)
    {t x : Nat} (h : t < image H (A.rep t) x) : t < A.index hA x := by
  apply Nat.lt_of_succ_le
  apply (A.zero_iff hA (t + 1) x).mp
  apply native_zero_lifts A
  rw [canonical_mul]
  exact (numeral_zero_iff H _ _ _).mpr h

/-- A protected later native row protects the earlier native row. The
order assumption may be checked before applying D. -/
theorem protect_earlier (H : FirstRowUnbounded) (D : TableElement) (hD : D.Total)
    {t i j r s p : Nat} (hij : i < j) (period : (tables t).FirstZero (D.rep t) p)
    (inside : j + 1 < p) (positive : 1 < (tables t).mul (D.rep t) (i + 1))
    (protectedLast : t < image H ((D.comp (numeral j)).rep t) s)
    (ordered : image H j s ≤ image H i r) :
    t < image H ((D.comp (numeral i)).rep t) r := by
  have last := native_strict_to_actual H (D.comp (numeral j)) (total_comp hD (numeral_total H j)) protectedLast
  rw [index_comp hD (numeral_total H j)] at last
  change t < D.index hD (image H j s) at last
  have ord := index_mono hD ordered
  have floor := native_truncation H (D.comp (numeral i)) (total_comp hD (numeral_total H i)) t r
  rw [index_comp hD (numeral_total H i)] at floor
  change min t (image H _ r) = min t (D.index hD (image H i r)) at floor
  have enough : t ≤ image H ((D.comp (numeral i)).rep t) r := by omega
  apply Nat.lt_of_le_of_ne enough
  intro eqv
  have hit := comp_transfer H D hD hij period inside positive eqv.symm last ord
  exact (Nat.ne_of_gt protectedLast) hit

/-- The old representative of g applied to r forces the last outer
composition to clear the cut one input before N. -/
theorem last_outer_protected (H : FirstRowUnbounded) (g r A t k : Nat)
    (old : ((numeral g).app (numeral r)).rep t = (numeral A).rep t)
    (base : t ≤ image H g (image H r k)) :
    t < image H (((numeral A).comp (numeral g)).rep t) (k + 1) := by
  have rd := ((numeral g).app (numeral r)).finite_read (numeral A)
    (total_app (numeral_total H g) (numeral_total H r)) (numeral_total H A) t (image H g k) old
  rw [index_app (numeral_total H g) (numeral_total H r)] at rd
  have floor := native_truncation H ((numeral A).comp (numeral g))
    (total_comp (numeral_total H A) (numeral_total H g)) t k
  rw [index_comp (numeral_total H A) (numeral_total H g)] at floor
  change min t (image H g (image H r k)) = min t (image H A (image H g k)) at rd
  change min t (image H _ k) = min t (image H A (image H g k)) at floor
  have h := (numeral (((numeral A).comp (numeral g)).rep t)).index_strict
    (numeral_total H _) (Nat.lt_succ_self k)
  change image H _ k < image H _ (k + 1) at h
  omega

/-- The last row is protected at k+1. All the rows may then be
tested at any common input N at least that large. -/
theorem outer_protected_at (H : FirstRowUnbounded) {g r A t k i p N : Nat}
    (old : ((numeral g).app (numeral r)).rep t = (numeral A).rep t)
    (base : t ≤ image H g (image H r k)) (hi : i ≤ g)
    (period : (tables t).FirstZero ((numeral A).rep t) p) (inside : g + 1 < p)
    (positive : 1 < (tables t).mul ((numeral A).rep t) (i + 1))
    (advance : k+1≤N) (order : i < g → image H g (k + 1) ≤ image H i N) :
    t < image H (((numeral A).comp (numeral i)).rep t) N := by
  have hlast := last_outer_protected H g r A t k old base
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · exact Nat.lt_of_lt_of_le hlast (index_mono (numeral_total H _) advance)
  · exact protect_earlier H (numeral A) (numeral_total H A) hlt period inside positive hlast (order hlt)

theorem outer_protected (H : FirstRowUnbounded) {g r A t k i p : Nat}
    (old : ((numeral g).app (numeral r)).rep t = (numeral A).rep t)
    (base : t ≤ image H g (image H r k)) (hi : i ≤ g)
    (period : (tables t).FirstZero ((numeral A).rep t) p) (inside : g + 1 < p)
    (positive : 1 < (tables t).mul ((numeral A).rep t) (i + 1))
    (order : i < g → image H g (k + 1) ≤ image H i (k + 2)) :
    t < image H (((numeral A).comp (numeral i)).rep t) (k + 2) :=
  outer_protected_at H old base hi period inside positive (Nat.le_succ _) order

/-- The two uses of the same residue in equation 7. -/
theorem inner_period_bound (H : FirstRowUnbounded) {t N W A i ell nw : Nat}
    (common : ((numeral W).comp (numeral ell)).rep t = ((numeral A).comp (numeral i)).rep t)
    (outer : t < image H (((numeral A).comp (numeral i)).rep t) N)
    (stretch : image H ell N = nw) : t < image H W nw := by
  rw [← common] at outer
  have h := native_strict_to_actual H _ (total_comp (numeral_total H W) (numeral_total H ell)) outer
  rw [index_comp (numeral_total H W) (numeral_total H ell)] at h
  change t < image H W (image H ell N) at h
  rwa [stretch] at h

/-- Equation 8, including the rightmost position and the weak inequality
of input indices there. No product at degree t+1 is assumed. -/
theorem inner_protected (H : FirstRowUnbounded) {t N w W A i ell j p : Nat}
    (common : ((numeral W).comp (numeral ell)).rep t = ((numeral A).comp (numeral i)).rep t)
    (outer : t < image H (((numeral A).comp (numeral i)).rep t) N)
    (hj : j ≤ ell) (nw : N ≤ w) (period : (tables t).FirstZero ((numeral W).rep t) p)
    (inside : ell + 1 < p) (positive : 1 < (tables t).mul ((numeral W).rep t) (j + 1))
    (order : j < ell → image H ell N ≤ image H j w) :
    t < image H (((numeral W).comp (numeral j)).rep t) w := by
  rw [← common] at outer
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · exact Nat.lt_of_lt_of_le outer (index_mono (numeral_total H _) nw)
  · exact protect_earlier H (numeral W) (numeral_total H W) hlt period inside positive outer (order hlt)

#print axioms outer_protected
#print axioms inner_period_bound
#print axioms inner_protected
end Gamma11
