import BackwardPowers

/-! The full generator acts by one predecessor on every positive
encoded value used in the induction. The mixed generator agrees with
its short left power below the highest bit of a positive background. -/
set_option autoImplicit false
namespace Gamma11.Backward

theorem predecessor_on_code {L X z b l m : Nat} (ih : RowsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b) (below : X<L)
    (mp : 0<m) (room : encodeDigit X z b m≤L) :
    mul (encodeDigit X z b m) (X+2^z*(2^b-1))=encodeDigit X z b (m-1) := by
  let p := 2^b
  let w := m/p
  let r := m%p
  have pp : 0<p := Nat.two_pow_pos b
  have split : p*w+r=m := Nat.div_add_mod ..
  have rFit : r<p := Nat.mod_lt _ pp
  by_cases zero : r=0
  · have wp : 0<w := by
      apply Nat.pos_of_ne_zero; intro wz
      rw [wz,zero,Nat.mul_zero,Nat.zero_add] at split; omega
    let u := w-1
    have ws : u+1=w := Nat.sub_add_cancel wp
    have cur : p*(u+1)+0=m := by rw [ws,←zero]; exact split
    have predEq : m-1=p*u+(p-1) := by rw [Nat.mul_succ] at cur; omega
    have aFit : mul (X+1) (u+1)≤X := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ X) _)
    rw [predEq,←cur,encoding_parts pp,encoding_parts (show p-1<p by omega),Nat.mul_zero,Nat.add_zero]
    exact boundary_step_below (local_full ih) dy dz X dX per lb (Nat.le_of_lt below) u (Nat.lt_of_le_of_lt aFit below)
  · let h := r-1
    have rs : h+1=r := Nat.sub_add_cancel (Nat.pos_of_ne_zero zero)
    have predEq : m-1=p*w+h := by omega
    have cur : p*w+(h+1)=m := by rw [rs]; exact split
    obtain ⟨k,period,hk⟩ := generated_period_le per w
    have out := inner_step_below ih dy dz (generated_divisible dX w) dX period (Nat.le_trans hk lb)
      (show h+1<p by omega) (show mul (X+1) w+2^z*(h+1)≤L by
        rw [←encoding_parts (show h+1<p by omega),cur]; exact room)
    rw [predEq,←cur,encoding_parts (show h+1<p by omega),encoding_parts (show h<p by omega)]
    exact out

theorem short_power_mod_top {L X z b l : Nat} (full : FullDigitsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b) (positive : 0<X) (cut : X≤L)
    {r : Nat} (small : r<2^b) :
    powers (X+2^z*(2^b-1)) (2^b-r)%2^X.log2=(X+2^z*r)%2^X.log2 := by
  let M := X.log2
  let X₀ := X%2^M
  have floor : 2^M≤X := Nat.log2_self_le (Nat.ne_of_gt positive)
  have room : z+b≤M := (Nat.le_log2 (Nat.ne_of_gt positive)).mpr (Nat.le_of_dvd positive dX)
  have offset {Y : Nat} (sm : Y<2^b) : 2^z*Y<2^(z+b) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_left sm (Nat.two_pow_pos _)
  have pos := Nat.two_pow_pos b
  have low := aligned_add_residue room dX (offset (show 2^b-1<2^b by omega))
  obtain ⟨h,ph⟩ := has_period_exp (Nat.zero_lt_succ X₀)
  have hl : h≤l := (ph l).mp (by
    rw [show mul (X₀+1) (2^l)=mul (X+1) (2^l)%2^M from (generated_mod ..).symm,
      (per l).mpr (Nat.le_refl _),Nat.zero_mod])
  have fits : X₀+2^z*(2^b-1)<L := Nat.lt_of_lt_of_le (low.1 ▸ Nat.mod_lt _ (Nat.two_pow_pos M))
    (Nat.le_trans floor cut)
  have row := full dy dz low.2 ph (Nat.le_trans hl lb) fits
  rw [powers_project,low.1,(aligned_add_residue room dX (offset small)).1,short_powers_of_digit row ph small]

theorem mixed_right_from_power {L X z b l Y a : Nat} (full : FullDigitsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b) (xp : 0<X) (cut : X≤L)
    (yFit : Y<2^b) (ap : 0<a) (fits : a≤X+2^z*Y) :
    mul a (X+2^z*Y)=powers (mul a (X+2^z*(2^b-1))) (2^b-Y) := by
  let M := X.log2
  have room : z+b≤M := (Nat.le_log2 (Nat.ne_of_gt xp)).mpr (Nat.le_of_dvd xp dX)
  have low : 2^z*Y<2^(z+b) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_left yFit (Nat.two_pow_pos _)
  have top := aligned_add_residue (Nat.le_succ_of_le room) dX low
  have large : X<2^(M+1) := Nat.lt_log2_self
  have rightFit := Nat.mod_lt (X+2^z*Y) (Nat.two_pow_pos (M+1))
  rw [top.1,Nat.mod_eq_of_lt large] at rightFit
  obtain ⟨k,pk⟩ := has_period_exp ap
  have cap := (pk M).mp (positive_half ap (Nat.lt_of_le_of_lt fits rightFit))
  rw [←map_powers]
  apply row_congr ap pk
  have div := Nat.pow_dvd_pow 2 cap
  rw [←Nat.mod_mod_of_dvd (X+2^z*Y) div,←Nat.mod_mod_of_dvd (powers _ _) div,
    short_power_mod_top full dy dz dX per lb xp cut yFit]

theorem smaller_encoded_power {L X z b l s : Nat} (ih : RowsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (fit : s<2^(l+b)) (cutX : encodeDigit X z b s<L) (cutS : s<L) (k : Nat) :
    powers (encodeDigit X z b s) k=encodeDigit X z b (powers s k) := by
  have pp := Nat.two_pow_pos b
  have hi := (Nat.div_lt_iff_lt_mul pp).mpr (show s<2^l*2^b by rwa [←Nat.pow_add])
  have out := powers_at_smaller_digit ih dy dz dX per lb hi (Nat.mod_lt s pp) cutX
    (show 2^b*(s/2^b)+s%2^b<L by rw [Nat.div_add_mod]; exact cutS) k
  rwa [Nat.div_add_mod] at out

#print axioms mixed_right_from_power
#print axioms predecessor_on_code
end Gamma11.Backward
