import GeometricHalf
import LocalPeriodTarget
import BackwardCompression

/-! Protection of an odd carry at an intermediate degree of the
geometric diagonal. The source index h varies while the block
test for the interior rows stays at 256. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

theorem odd_floor_at_height (H : FirstRowUnbounded) {h r t : Nat}
    (hlo : 4≤h) (degree : 257≤t) (limit : t≤256^h) (pos : 0<r) (odd : r%2=1)
    (short : r<2^(h-1)) : t≤image H geometricRow (image H r (h-2)) := by
  have enough : h≤image H r (h-2) := by
    by_cases one : r=1
    · subst r
      have read : image H 1 2=4 := by
        apply image_eq_of_exact_entry
        have val : (tables 9).mul 1 4=240 := LowProducts.v1_4 (tables 9)
        have pr := (tables 9).projection (tables 5) (Nat.pow_dvd_pow 2 (by decide : 5≤9)) 1 4
        rw [val] at pr; exact pr.symm
      have steps := image_distance H 1 2 (h-4)
      rw [read,show 2+(h-4)=h-2 by omega] at steps
      omega
    · have div : 2^1∣r+1 := Nat.dvd_of_mod_eq_zero (by change (r+1)%2=0; omega)
      have room := Nat.le_of_lt (Nat.pow_lt_pow_succ (n:=h-1) (by decide : 1<2))
      have cap : r<2^(1+(h-2)+1) := by rw [show 1+(h-2)+1=h-1+1 by omega]; omega
      have gap := extra_bit_after_ones H (p:=1) (w:=h-2) div (by change 2≤r; omega) cap
      omega
  have zero := geometric_row_zero tables t 256 h (by decide) degree limit
  have high := (numeral_zero_iff H geometricRow t h).mp ((canonical_mul ..).symm.trans zero)
  exact Nat.le_trans high (index_mono (numeral_total H _) enough)

theorem protected_odd_at_height (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex)
    {t h r : Nat} (hMin : 4≤h) (hMax : h≤256) (degree : 257≤t) (limit : t≤256^h)
    (priorImage : image H geometricRow (h-1)≤targetIndex)
    (rp : 0<r) (odd : r%2=1) (short : r<2^(h-1)) (ends : OddColumnEndpoints t r) :
    (tables (t+1)).mul (oldEntry t geometricRow r) (geometricRow+1)=oldEntry t geometricRow (r+1) := by
  let A := oldEntry t geometricRow r
  have law : FiniteBlockLaw := finite_block_of_restore Backward.finite_restoration
  have bound : BlockBoundary H := (finite_block_iff_boundary H).mp law
  have ones : OnesRowShift H := ones_shift_of_boundary H bound
  have base := odd_floor_at_height H hMin degree limit rp odd short
  have gFit : geometricRow+1<2^256 := by decide
  have nz := repeatBits_pos (Nat.pow_pos (by decide : 0<256) : 0<256^ends.m)
    (Nat.zero_lt_succ geometricRow) gFit
  have finish : 0<oldEntry t geometricRow (r+1) := by
    rw [ends.finish]; exact Nat.lt_of_lt_of_le nz (Nat.le_add_left ..)
  have ltNext := ((tables t).row_grows A (geometricRow+1) ((tables t).mul_lt geometricRow r)).resolve_left (by
    rw [show (tables t).mul A (geometricRow+1)=oldEntry t geometricRow (r+1) from
      ((tables t).row_recurrence ..).symm]; exact Nat.ne_of_gt finish)
  have room := (tables t).mul_lt A (geometricRow+1)
  apply lift_odd_row_at H bound ones (k:=h-2) (N:=256) (by decide : 1≤geometricRow)
    (by omega) (by change A+1<2^t; omega) base
  · intro i lo hi
    rw [show h-2+1=h-1 by omega]
    have guard := wide.native i lo (Nat.lt_trans hi (by decide : geometricRow<2^256-2))
    exact Nat.le_trans priorImage ((numeral_zero_iff H i _ _).mp guard)
  · intro i lo hi
    obtain ⟨corners,window,m,pos,width⟩ := corners_of_endpoints ends
      (fun m hm => (licensed_readings H law m hm).1) i lo hi
    refine ⟨corners.toOldSlice H ones (by decide) window,width.symm ▸ (licensed_readings H law m pos).2,?_⟩
    intro b bp small
    change b<2^corners.w-2 at small
    change 256*corners.w≤image H b corners.w
    rw [width] at small ⊢
    exact (numeral_zero_iff H b _ _).mp
      (short_periods_from_restore H Backward.finite_restoration m pos b bp (Nat.le_of_lt small))

theorem protected_even_at_height {upper t A r : Nat} (wide : WidePeriodEstimates upper) (degree : t≤upper)
    (pos : 0<A) (fit : A<2^t) (aligned : 2^256∣A)
    (next : oldEntry t geometricRow (r+1)=A+(geometricRow+1)) :
    (tables (t+1)).mul A (geometricRow+1)=oldEntry t geometricRow (r+1) := by
  have above := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_trans degree (Nat.le_succ _))
  have sum := wide.addition A pos (Nat.lt_of_lt_of_le fit above) aligned (geometricRow+1)
    (Nat.zero_lt_succ _) (by decide)
  have pr := (tables (upper+1)).projection (tables (t+1)) (Nat.pow_dvd_pow 2 (Nat.succ_le_succ degree)) A (geometricRow+1)
  have range : oldEntry t geometricRow (r+1)<2^t := (tables t).mul_lt geometricRow (r+1)
  rw [sum,←next,Nat.mod_eq_of_lt (Nat.lt_trans range (Nat.pow_lt_pow_succ (by decide : 1<2)))] at pr
  exact pr.symm

#print axioms protected_odd_at_height
end Gamma11
