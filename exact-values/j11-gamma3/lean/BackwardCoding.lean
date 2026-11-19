import BackwardAssemble

/-! Canonical coordinates for a background of known row period. The
zero-background digit shift gives a whole row of scaled indices. -/
set_option autoImplicit false
namespace Gamma11.Backward

theorem model_split (b l Y : Nat) : modelGenerator b l Y=2^b*(2^l-1)+Y := by
  rw [modelGenerator,Nat.mul_sub,Nat.mul_one,Nat.pow_add,Nat.mul_comm (2^l) (2^b)]

theorem encoding_parts {X z b i r : Nat} (small : r<2^b) :
    encodeDigit X z b (2^b*i+r)=mul (X+1) i+2^z*r := by
  rw [encodeDigit,Nat.mul_add_div (Nat.two_pow_pos b),Nat.div_eq_of_lt small,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt small]
  rfl

theorem model_fits {b l Y : Nat} (fits : Y<2^b) : modelGenerator b l Y<2^(l+b) := by
  have lp := Nat.two_pow_pos l
  rw [model_split,Nat.pow_add,Nat.mul_comm (2^l) (2^b)]
  have eqv := Nat.mul_add (2^b) (2^l-1) 1
  rw [Nat.sub_add_cancel lp,Nat.mul_one] at eqv
  omega

theorem encoded_model {X z b l Y : Nat} (per : PeriodExp (X+1) l) (small : Y<2^b) :
    encodeDigit X z b (modelGenerator b l Y)=X+2^z*Y := by
  rw [model_split,encoding_parts small,period_last X l per]

theorem scaled_generator {b z w : Nat} (dy : IsDyadic b) (dz : b∣z) (small : w<2^b) (k : Nat) :
    mul (2^z*w+1) k=2^z*mul (w+1) k := by
  let F := 2^z*(2^b-1)+1
  have first : mul F w=2^z*w := (full_block_at_zero dy dz w).trans (by rw [Nat.mod_eq_of_lt small])
  have below : mul (w+1) k≤w := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ _) k)
  rw [← first,compose_rows,full_block_at_zero dy dz,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt below small)]

theorem zero_digit_compressed {X z b l : Nat} (dy : IsDyadic b) (per : PeriodExp (X+1) l)
    (lb : l≤b) : CompressedRow X z b l 0 := by
  have lp := Nat.two_pow_pos l
  have width := Nat.pow_le_pow_right (by decide : 0<2) lb
  have fit : 2^l-1<2^b := by omega
  intro i
  rw [model_split,Nat.add_zero,scaled_generator dy (Nat.dvd_refl _) fit,Nat.sub_add_cancel lp,power_row]
  have base := encoding_parts (X:=X) (z:=z) (b:=b) (i:=i%2^l) (r:=0) (Nat.two_pow_pos b)
  simp only [Nat.mul_zero,Nat.add_zero] at base ⊢
  exact (row_congr (Nat.zero_lt_succ _) per (Nat.mod_mod ..).symm).trans base.symm

theorem zero_base_compressed {z b l Y : Nat} (dy : IsDyadic b) (dz : b∣z)
    (per : PeriodExp (0+1) l) (small : Y<2^b) : CompressedRow 0 z b l Y := by
  have one (k : Nat) : mul 1 k=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (mul_lt_left (by decide : 0<1) k))
  have lz : l=0 := Nat.eq_zero_of_le_zero ((per 0).mp (one _))
  subst l
  intro i
  rw [Nat.zero_add,model_split,Nat.pow_zero,Nat.sub_self,Nat.mul_zero,Nat.zero_add,scaled_generator dy dz small,
    encodeDigit,Nat.zero_add,one,Nat.zero_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ Y) _)) small)]

theorem increasing_row {X l i : Nat} (per : PeriodExp (X+1) l) (small : i+1<2^l) :
    mul (X+1) i < mul (X+1) (i+1) := by
  have nonzero : mul (X+1) (i+1)≠0 := by
    intro zero
    have hit := (zero_iff_period (Nat.zero_lt_succ X) per (i+1)).mp zero
    rw [Nat.mod_eq_of_lt small] at hit
    exact Nat.succ_ne_zero i hit
  rw [previous_column X i]; exact mul_lt_left (Nat.pos_of_ne_zero nonzero) X

theorem generated_lower {X q l : Nat} (dv : 2^q∣X) (per : PeriodExp (X+1) l) (i : Nat)
    (small : i<2^l) : 2^q*i≤mul (X+1) i := by
  induction i with
  | zero => simp only [Nat.mul_zero,mul_zero_right,Nat.le_refl]
  | succ i ih =>
    have prior := ih (show i<2^l by omega)
    have grow := increasing_row per small
    obtain ⟨t,dt⟩ := generated_divisible dv i
    obtain ⟨s,ds⟩ := generated_divisible dv (i+1)
    rw [dt,ds] at grow
    have step := Nat.mul_le_mul_left (2^q) (Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left grow))
    rw [Nat.mul_succ,← dt,← ds] at step
    rw [Nat.mul_succ]
    exact Nat.le_trans (Nat.add_le_add_right prior _) step

theorem encode_dominates {X z b l m : Nat} (dv : 2^(z+b)∣X) (per : PeriodExp (X+1) l)
    (fit : m<2^(l+b)) : m≤encodeDigit X z b m := by
  let p := 2^b
  have pp : 0<p := Nat.two_pow_pos b
  have hf : m/p<2^l := (Nat.div_lt_iff_lt_mul pp).mpr (by rwa [Nat.pow_add] at fit)
  have upper := generated_lower dv per _ hf
  have weight := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left b z)
  have high := Nat.le_trans (Nat.mul_le_mul_right (m/p) weight) upper
  have low := Nat.le_mul_of_pos_left (m%p) (Nat.two_pow_pos z)
  exact Nat.le_trans (Nat.le_of_eq (Nat.div_add_mod m p).symm) (Nat.add_le_add high low)

theorem induced_period {X l w : Nat} (per : PeriodExp (X+1) l) (small : w<2^l)
    {h : Nat} (ph : PeriodExp (w+1) h) : PeriodExp (mul (X+1) w+1) h := by
  intro k
  have fit := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ w) (2^k))) small
  rw [compose_rows,zero_iff_period (Nat.zero_lt_succ _) per,Nat.mod_eq_of_lt fit,ph]

theorem scaled_period {b z w h : Nat} (dy : IsDyadic b) (dz : b∣z) (small : w<2^b)
    (ph : PeriodExp (w+1) h) : PeriodExp (2^z*w+1) h := by
  intro k; rw [scaled_generator dy dz small,Nat.mul_eq_zero]
  exact (or_iff_right (Nat.ne_of_gt (Nat.two_pow_pos z))).trans (ph k)

#print axioms encode_dominates
end Gamma11.Backward
