import BackwardBlocks

/-! The zero-background case of the backwards full-digit formula,
obtained using the finite dyadic anchors without any block-law premise. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem count_aligned_row {d a r k : Nat}
    (hit : (tables d).mul a (2^k)=2^r*2^k)
    (aligned : ∀ i, 2^r ∣ (tables d).mul a i) (y : Nat) (small : y≤2^k) :
    (tables d).mul a y=2^r*y := by
  let V := (tables d).mul a
  let f := fun i => V i/2^r
  have pos := Nat.two_pow_pos r
  have recover (i : Nat) : 2^r*f i=V i := Nat.mul_div_cancel' (aligned i)
  have edge : f (2^k)=2^k := Nat.eq_of_mul_eq_mul_left pos ((recover _).trans hit)
  have start : f 0=0 := by dsimp [f,V]; rw [(tables _).mul_zero,Nat.zero_div]
  obtain ⟨p,hp⟩ := (tables d).exists_firstZero a
  obtain ⟨l,_,rfl⟩ := period_is_power_two tables d _ _ hp
  have longer : k<l := by
    apply Nat.lt_of_not_ge
    intro le
    have z := ((tables d).firstZero_iff_mod hp (2^k)).mpr ((pow_mod_zero_iff ..).mpr le)
    rw [hit] at z
    exact (Nat.ne_of_gt (Nat.mul_pos pos (Nat.two_pow_pos k))) z
  have stop := Nat.pow_lt_pow_right (by decide : 1<2) longer
  have incr (i : Nat) (before : i<2^k) : f i<f (i+1) := by
    apply Nat.lt_of_mul_lt_mul_left (a:=2^r)
    rw [recover,recover]
    by_cases eqv : i=0
    · subst i; change (tables d).mul a 0<(tables d).mul a 1
      rw [(tables _).mul_zero]
      exact Nat.pos_of_ne_zero (hp.2.2 1 (by decide) (by omega))
    · exact (tables _).firstZero_strict hp (Nat.pos_of_ne_zero eqv) (Nat.lt_succ_self _) (by omega)
  have distance (i n : Nat) (limit : i+n≤2^k) : f i+n≤f (i+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      exact Nat.lt_of_le_of_lt (ih (by omega)) (incr (i+n) (by omega))
  have low := distance 0 y (by omega)
  have high := distance y (2^k-y) (by omega)
  simp only [start,Nat.zero_add] at low
  rw [show y+(2^k-y)=2^k by omega,edge] at high
  exact (recover y).symm.trans (congrArg (fun n => 2^r*n) (show f y=y by omega))

def ShiftHomAt (z k : Nat) : Prop := ∀ a b, a<2^k → b<2^k →
  2^z*((tables k).mul a b)=(tables (z+k)).mul (2^z*a) (2^z*b)

theorem dyadic_shift (e k : Nat) (small : k≤2^e) : ShiftHomAt (2^e) k := by
  let r := 2^e
  let m := 2*r+1
  let d := r+k
  let a := 2^r-1
  have twice : 2^(e+1)=2*r := by rw [Nat.pow_succ,Nat.mul_comm]
  have hm : 2^(e+1)<m := by rw [twice]; exact Nat.lt_succ_self _
  obtain ⟨_,first,last⟩ := standard_segment tables m e hm
  rw [twice] at last
  have high : act tables m a k=d := act_rigid tables m a r first last (Nat.lt_succ_self _) small
  have dm : d+1≤m := by dsimp [d,m,r] at *; omega
  have cut := act_at_smaller_degree tables dm a k
  rw [high,Nat.min_eq_right (Nat.le_succ _)] at cut
  have final := (exact_iff_act tables a k d).mpr cut
  rw [← canonical_mul] at final
  have aligned (i : Nat) : 2^r ∣ (tables (d+1)).mul a i := by
    apply Nat.dvd_of_mod_eq_zero
    rw [(tables _).projection (tables r) (Nat.pow_dvd_pow 2 (show r≤d+1 by dsimp [d]; omega))]
    have one : (tables r).mul a 1=0 := by
      rw [(tables r).mul_one]; dsimp only [a]; rw [Nat.sub_add_cancel (Nat.two_pow_pos r),Nat.mod_self]
    rw [(tables r).reduce_period one,Nat.mod_one,(tables r).mul_zero]
  have final' : (tables (d+1)).mul a (2^k)=2^r*2^k := final.trans (Nat.pow_add ..)
  have project (i : Nat) := (tables (d+1)).projection (tables d) (Nat.pow_dvd_pow 2 (Nat.le_succ _)) a i
  have zero := project (2^k)
  rw [final,Nat.mod_self] at zero
  have row (i : Nat) (fit : i<2^k) : (tables d).mul a i=2^r*i := by
    have line := project i
    rw [count_aligned_row final' aligned i (Nat.le_of_lt fit),
      Nat.mod_eq_of_lt (show 2^r*i<2^d from Nat.pow_add 2 r k ▸ Nat.mul_lt_mul_of_pos_left fit (Nat.two_pow_pos _))] at line
    exact line.symm
  intro x y xf yf
  have pr := (tables d).projection (tables k) (Nat.pow_dvd_pow 2 (Nat.le_add_left k r)) x y
  have per := (tables d).reduce_period zero.symm ((tables d).mul x y)
  rw [pr,row _ ((tables k).mul_lt ..)] at per
  exact per.symm.trans (((tables d).mul_distrib a x y).trans (by rw [row x xf,row y yf]))

private theorem shift_compose {r s k : Nat} (first : ShiftHomAt s k) (second : ShiftHomAt r (s+k)) :
    ShiftHomAt (r+s) k := by
  intro a b ap bp
  have af : 2^s*a<2^(s+k) := Nat.pow_add 2 s k ▸ Nat.mul_lt_mul_of_pos_left ap (Nat.two_pow_pos _)
  have bf : 2^s*b<2^(s+k) := Nat.pow_add 2 s k ▸ Nat.mul_lt_mul_of_pos_left bp (Nat.two_pow_pos _)
  rw [Nat.pow_add,Nat.mul_assoc,first a b ap bp,second _ _ af bf,Nat.add_assoc]
  simp only [Nat.mul_assoc]

theorem aligned_shift {b z : Nat} (dy : IsDyadic b) (divide : b ∣ z) : ShiftHomAt z b := by
  obtain ⟨e,rfl⟩ := dy
  induction z using Nat.strongRecOn with
  | ind z ih =>
    by_cases empty : z=0
    · subst z; intro a b _ _
      simp only [Nat.pow_zero,Nat.one_mul]
      exact (congrArg (fun t => (tables t).mul a b) (Nat.zero_add (2^e))).symm
    · let r := 2^z.log2
      let s := z-r
      have rp : 0<r := Nat.two_pow_pos _
      have rz : r≤z := Nat.log2_self_le empty
      have height := (Nat.le_log2 empty).mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero empty) divide)
      have dr : 2^e ∣ r := Nat.pow_dvd_pow 2 height
      have ds : 2^e ∣ s := Nat.dvd_sub divide dr
      have top := Nat.lt_log2_self (n:=z)
      rw [Nat.pow_succ] at top
      change z<r*2 at top
      have sr : s<r := by dsimp [s]; omega
      have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt sr) (Nat.dvd_sub dr ds)
      have first := ih s (by dsimp [s]; omega) ds
      have second := dyadic_shift z.log2 (s+2^e) (by omega)
      have total : r+s=z := by dsimp [s]; omega
      exact total ▸ shift_compose first second

#print axioms aligned_shift

theorem shifted_row {z k : Nat} (kp : 0<k) (hom : ShiftHomAt z k) (y : Nat) :
    (tables (z+k)).mul (2^z-1) y=2^z*(y%2^k) := by
  induction y with
  | zero => rw [(tables _).mul_zero,Nat.zero_mod,Nat.mul_zero]
  | succ y ih =>
    have P := Nat.two_pow_pos k
    have step := hom (y%2^k) 1 (Nat.mod_lt y P) (Nat.one_lt_two_pow (by omega))
    rw [(tables k).mul_one,Nat.mod_add_mod,Nat.mul_one] at step
    rw [(tables _).row_recurrence,ih,Nat.sub_add_cancel (Nat.two_pow_pos z),← step]

theorem neg_scaled (z k y : Nat) : neg (z+k) (2^z*y)=2^z*neg k y := by
  unfold neg
  rw [Nat.pow_add,Nat.mul_mod_mul_left]
  by_cases empty : y%2^k=0
  · rw [empty,Nat.mul_zero,if_pos rfl,if_pos rfl,Nat.mul_zero]
  · have pos := Nat.mul_pos (Nat.two_pow_pos z) (Nat.pos_of_ne_zero empty)
    rw [if_neg (Nat.ne_of_gt pos),if_neg empty,Nat.mul_sub]

/-- Exact row of a contiguous b-bit block at every offset divisible by
b. This is the zero-background case of the published full-block law. -/
theorem full_block_at_zero {b z : Nat} (dy : IsDyadic b) (aligned : b ∣ z) (y : Nat) :
    mul (2^z*(2^b-1)+1) y=2^z*(y%2^b) := by
  have bp : 0<b := by obtain ⟨e,rfl⟩ := dy; exact Nat.two_pow_pos _
  let F := 2^z*(2^b-1)+1
  let d := z+b
  have q := Nat.two_pow_pos z
  have P := Nat.two_pow_pos b
  have sum : F+(2^z-1)=2^d := by
    dsimp [F,d]; rw [Nat.pow_add,Nat.mul_sub,Nat.mul_one]
    have comp := Nat.mul_le_mul_left (2^z) P
    rw [Nat.mul_one] at comp
    omega
  have fp : 0<F := Nat.zero_lt_succ _
  have upper := Nat.le_of_eq sum
  have inv : 2^z-1=neg d F := unique_inverse (by omega) (by rw [sum,Nat.mod_self])
  have small : mul F y<2^d := Nat.lt_of_lt_of_le (mul_lt_left fp y) (by omega)
  have pr := mul_projects d F y
  rw [Nat.mod_eq_of_lt small,finite,← inv,shifted_row bp (aligned_shift dy aligned),
    neg_project (show b≤d from Nat.le_add_left ..),neg_scaled,neg_neg] at pr
  exact pr

theorem zero_background_row {b z : Nat} (dy : IsDyadic b) (aligned : b ∣ z)
    (i r : Nat) (small : r<2^b) :
    mul (0+2^z*(2^b-1)+1) (2^b*i+r)=mul (0+1) i+2^z*r := by
  have base : mul 1 i=0 := by have := mul_lt_left (by decide : 0<1) i; omega
  rw [Nat.zero_add,Nat.zero_add,base,Nat.zero_add,full_block_at_zero dy aligned,
    Nat.mul_add_mod,Nat.mod_eq_of_lt small]

#print axioms full_block_at_zero

def PositiveFullDigitRow : Prop := ∀ {b z X l : Nat}, 0<X → IsDyadic b → b ∣ z →
  2^(z+b) ∣ X → PeriodExp (X+1) l → l≤b → ∀ i r, r<2^b →
    mul (X+2^z*(2^b-1)+1) (2^b*i+r)=mul (X+1) i+2^z*r

theorem full_of_positive_digits (positive : PositiveFullDigitRow) : FullDigitRow := by
  intro b z X l dy divZ divX per lb i r small
  by_cases empty : X=0
  · subst X; exact zero_background_row dy divZ i r small
  · exact positive (Nat.pos_of_ne_zero empty) dy divZ divX per lb i r small

end Gamma11.Backward
