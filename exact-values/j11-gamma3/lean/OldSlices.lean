import CarryLift
import SpectrumBits

/-! Recover the whole old arithmetic progression from its two adjacent
endpoints. The argument uses monotonicity on the first period and
divisibility of every output by 2^p. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds TableElement

private theorem last_row_zero (p v : Nat) : (tables p).mul (2 ^ p - 1) v = 0 := by
  have one : (tables p).mul (2 ^ p - 1) 1 = 0 := by
    rw [(tables p).mul_one, Nat.sub_add_cancel (Nat.two_pow_pos _), Nat.mod_self]
  rw [(tables p).reduce_period one, Nat.mod_one, (tables p).mul_zero]

private theorem background_residue {K q m : Nat} (bg : m ∣ K) (hq : 0 < q) (hm : q ≤ m) :
    (K + q - 1) % m = q - 1 := by
  rw [show K+q-1 = K+(q-1) by omega, Nat.add_mod, Nat.mod_eq_zero_of_dvd bg,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

theorem old_slice_line (H : FirstRowUnbounded) (ones : OnesRowShift H)
    {t w p B A i : Nat} (width : IsDyadic w) (pw : 0 < w) (aligned : w ∣ p)
    (bg : 2 ^ (p+w) ∣ B) (window : p+w ≤ t)
    (lowArg : (A+1) % 2 ^ w = 2 ^ w - 1)
    (start : oldEntry t A i = B + 2 ^ p - 1)
    (finish : oldEntry t A (i+1) = B + 2 ^ p * (2 ^ w - 1)) :
    ∀ v, 1 ≤ v → v ≤ 2 ^ w - 1 → oldEntry t (oldEntry t A i) v = B + 2 ^ p * v := by
  let W := oldEntry t A i
  let q := 2 ^ p
  let E := 2 ^ w - 1
  let V := oldEntry t W
  have qq : 0 < q := Nat.two_pow_pos p
  have wtwo : 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) pw
  have epos : 0 < E := by dsimp [E]; omega
  have startW : W = B+q-1 := start
  have bgp : q ∣ B := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show p ≤ p+w by omega)) bg
  have lowP : W % q = q-1 := startW ▸ background_residue bgp qq (Nat.le_refl _)
  have qsmall : q ≤ 2 ^ (p+w) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have wlow : W % 2 ^ (p+w) = q-1 := startW ▸ background_residue bg qq qsmall
  have shift := ones width aligned
  have sub : w - 1 < w := by omega
  have earlier := (numeral (q-1)).index_strict (numeral_total H _) sub
  change image H (q-1) (w-1) < image H (q-1) w at earlier
  change image H (q-1) w = p+w at shift
  rw [shift] at earlier
  have compatible : (numeral W).rep (p+w) = (numeral (q-1)).rep (p+w) :=
    wlow.trans (Nat.mod_eq_of_lt (by omega)).symm
  have rd := (numeral W).finite_read (numeral (q-1)) (numeral_total H _) (numeral_total H _) (p+w) (w-1) compatible
  change min (p+w) (image H W (w-1)) = min (p+w) (image H (q-1) (w-1)) at rd
  have noz : (tables t).mul W (2 ^ (w-1)) ≠ 0 := by
    intro hz
    have high := (numeral_zero_iff H W t (w-1)).mp ((canonical_mul _ _ _).symm.trans hz)
    change t ≤ image H W (w-1) at high
    omega
  obtain ⟨pp, period⟩ := (tables t).exists_firstZero W
  obtain ⟨k, _, hk⟩ := FiniteTable.period_is_power_two tables t W pp period
  have kw : w ≤ k := by
    apply Nat.le_of_not_gt; intro lt
    have dv : pp ∣ 2 ^ (w-1) := hk ▸ Nat.pow_dvd_pow 2 (by omega)
    exact noz (((tables t).firstZero_iff_mod period _).mpr (Nat.mod_eq_zero_of_dvd dv))
  have dv : 2 ^ w ∣ pp := hk ▸ Nat.pow_dvd_pow 2 kw
  let u := (A+1) % pp
  have umod : u % 2 ^ w = E := (Nat.mod_mod_of_dvd _ dv).trans lowArg
  have e_le_u : E ≤ u := umod ▸ Nat.mod_le _ _
  have up : u < pp := Nat.mod_lt _ period.1
  have eless : E < pp := Nat.lt_of_le_of_lt e_le_u up
  have lastAt : V u = B+q*E := calc
    V u = (tables t).mul W (A+1) := ((tables t).reduce_period period.2.1 _).symm
    _ = oldEntry t A (i+1) := ((tables t).row_recurrence A i).symm
    _ = _ := finish
  have endBound : V E ≤ B+q*E := by
    rw [← lastAt]
    rcases Nat.eq_or_lt_of_le e_le_u with eqv | lt
    · rw [eqv]; exact Nat.le_refl _
    · exact Nat.le_of_lt ((tables t).firstZero_strict period epos lt up)
  have multiple (v : Nat) : q ∣ V v := by
    apply Nat.dvd_of_mod_eq_zero
    have proj := (tables t).projection (tables p) (Nat.pow_dvd_pow 2 (show p ≤ t by omega)) W v
    change V v % q = (tables p).mul W v at proj
    rw [proj, ← (tables p).mul_mod_left W]
    change (tables p).mul (W % q) v = 0
    rw [lowP]; exact last_row_zero p v
  have inc (v : Nat) (positive : 0 < v) (small : v < E) : V v + q ≤ V (v+1) := by
    have upv := (tables t).firstZero_strict period positive (Nat.lt_succ_self v) (show v+1 < pp by omega)
    change V v < V (v+1) at upv
    obtain ⟨a, ha⟩ := multiple v
    obtain ⟨b, hb⟩ := multiple (v+1)
    have lt : a < b := by
      apply Nat.lt_of_not_ge; intro le
      have := Nat.mul_le_mul_left q le
      omega
    rw [ha, hb, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left q lt
  have run (v k' : Nat) (lo : 0 < v) (hi : v+k' ≤ E) : V v + q*k' ≤ V (v+k') := by
    induction k' with
    | zero => simp
    | succ n ih =>
      have a := ih (by omega)
      have b := inc (v+n) (by omega) (by omega)
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact Nat.le_trans (Nat.add_le_add_right a q) b
  have nonzero := period.2.2 1 (by decide) (show 1 < pp by omega)
  have wBound : W < 2 ^ t := (tables t).mul_lt A i
  have notMax : W+1 < 2 ^ t := by
    apply Nat.lt_of_not_ge; intro h
    rw [(tables t).mul_one, show W+1=2^t by omega, Nat.mod_self] at nonzero
    exact nonzero rfl
  have first : V 1 = B+q := ((tables t).mul_one W).trans
    ((Nat.mod_eq_of_lt notMax).trans (by omega))
  intro v vlo vhi
  have lower := run 1 (v-1) (by decide) (by omega)
  have upper := run v (E-v) vlo (by omega)
  rw [first, show 1+(v-1)=v by omega, Nat.mul_sub, Nat.mul_one] at lower
  rw [show v+(E-v)=E by omega, Nat.mul_sub] at upper
  have le1 : q ≤ q*v := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q vlo
  have le2 := Nat.mul_le_mul_left q vhi
  change V v = B+q*v
  omega

def SliceCorners.toOldSlice (H : FirstRowUnbounded) (ones : OnesRowShift H)
    {t N A i : Nat} (c : SliceCorners t N A i) (posN : 0 < N) (window : c.p+c.w ≤ t) : OldSlice t N A i where
  toSliceCorners := c
  line := by
    have wid : c.w ≤ N*c.w := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right c.w posN
    have dv := Nat.dvd_trans (Nat.pow_dvd_pow 2 wid) c.offset_dvd
    have qq := Nat.two_pow_pos c.w
    have low : (A+1) % 2 ^ c.w = 2 ^ c.w - 1 := by
      rw [c.argument, Nat.add_mod, Nat.mod_eq_zero_of_dvd dv, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega)]
    exact old_slice_line H ones c.width (Nat.lt_of_lt_of_le (by decide : 0 < 2) c.width_two)
      c.aligned c.block_dvd window low c.start c.finish

#print axioms old_slice_line
end Gamma11
