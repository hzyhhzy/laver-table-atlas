import BackwardLift

/-! Dougherty II, Lemma 4.8. The highest bit of a product cannot be
inferred just from a projected row. It is recovered by taking one
left power, applying distributivity and using a genuinely smaller
full-digit generator in each of two places. -/
set_option autoImplicit false
namespace Gamma11.Backward

theorem boundary_step_below {L b z : Nat} (full : FullDigitsBelow L) (dy : IsDyadic b) (dz : b∣z)
    (X : Nat) {l : Nat} (dX : 2^(z+b)∣X) (per : PeriodExp (X+1) l) (lb : l≤b)
    (cut : X≤L) (i : Nat) (acut : mul (X+1) (i+1)<L) :
    mul (mul (X+1) (i+1)) (X+2^z*(2^b-1))=mul (X+1) i+2^z*(2^b-1) := by
  let a := mul (X+1) (i+1)
  let y := mul (X+1) i
  let D := 2^z*(2^b-1)
  have step : y=mul a X := previous_column X i
  change mul a (X+D)=y+D
  by_cases empty : a=0
  · rw [step,empty,mul_zero_left,mul_zero_left]
  have ap := Nat.pos_of_ne_zero empty
  have ax : a≤X := Nat.le_of_lt_succ (mul_lt_left (Nat.zero_lt_succ X) (i+1))
  have xp : 0<X := Nat.lt_of_lt_of_le ap ax
  let M := X.log2
  let U := 2^M
  let X₀ := X%U
  let Q := 2^(z+b)
  have floor : U≤X := Nat.log2_self_le (Nat.ne_of_gt xp)
  have ceil : X<2^(M+1) := Nat.lt_log2_self
  have smallX : X₀<U := Nat.mod_lt X (Nat.two_pow_pos M)
  have earlierX : X₀<X := Nat.lt_of_lt_of_le smallX floor
  have mRoom : z+b≤M := (Nat.le_log2 (Nat.ne_of_gt xp)).mpr (Nat.le_of_dvd xp dX)
  have digitSmall : D<Q := by
    dsimp [D,Q]; rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (Nat.two_pow_pos b) (by decide)) (Nat.two_pow_pos _)
  have splitX := aligned_add_residue mRoom dX digitSmall
  change (X+D)%U=X₀+D ∧ Q∣X₀ at splitX
  have lowFullCut : X₀+D<L := Nat.lt_of_lt_of_le (splitX.1 ▸ Nat.mod_lt (X+D) (Nat.two_pow_pos _))
    (Nat.le_trans floor cut)
  obtain ⟨l₀,perLow⟩ := has_period_exp (Nat.zero_lt_succ X₀)
  have lowExpo : l₀≤l := (perLow l).mp (by
    change mul (X%2^M+1) (2^l)=0
    rw [← generated_mod,(per l).mpr (Nat.le_refl _),Nat.zero_mod])
  have genA : a%U=mul (X₀+1) (i+1) := generated_mod ..
  have genY : y%U=mul (X₀+1) i := generated_mod ..
  have aCutLow : mul (X₀+1) (i+1)<L := genA ▸
    Nat.lt_of_lt_of_le (Nat.mod_lt a (Nat.two_pow_pos M)) (Nat.le_trans floor cut)
  have recurse := boundary_step_below full dy dz X₀ splitX.2 perLow (Nat.le_trans lowExpo lb)
    (Nat.le_trans (Nat.le_of_lt earlierX) cut) i aCutLow
  change mul (mul (X₀+1) (i+1)) (X₀+D)=mul (X₀+1) i+D at recurse
  let v := mul a (X+D)
  let A := Q*(v/Q)
  have dA : Q∣A := Nat.dvd_mul_right ..
  have da : Q∣a := generated_divisible dX (i+1)
  have reduceV : v%Q=D := by
    rw [show v%Q=mul (a%Q) ((X+D)%Q) from project_native ..,Nat.mod_eq_zero_of_dvd da,
      mul_zero_left,Nat.add_mod,Nat.mod_eq_zero_of_dvd dX,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt digitSmall]
  have parts : v=A+D := by
    have split := Nat.div_add_mod v Q
    rw [reduceV] at split
    exact split.symm
  have smallV : v<a := mul_lt_left ap (X+D)
  have projected := project_native M a (X+D)
  change v%U=mul (a%U) ((X+D)%U) at projected
  rw [parts,(aligned_add_residue mRoom dA digitSmall).1,splitX.1,genA,recurse,← genY] at projected
  have agree : A%U=y%U := Nat.add_right_cancel projected
  have smallY : y<a := step ▸ mul_lt_left ap X
  have drop := smaller_generated_period per (Nat.lt_of_lt_of_le smallY ax)
  have prevZero : mul (A+1) (2^(l-1))%U=0 := by
    rw [generated_mod,agree,← generated_mod,drop.2,Nat.zero_mod]
  have raised := period_lifts_once (M:=M) (x:=A+1) (Nat.zero_lt_succ _)
    (show A+1≤2^(M+1) by omega) prevZero
  rw [Nat.sub_add_cancel drop.1] at raised
  obtain ⟨h,perA⟩ := has_period_exp (Nat.zero_lt_succ A)
  have hb : h≤b := Nat.le_trans ((perA l).mp raised) lb
  have digitA := full dy dz dA perA hb (show A+D<L by change a<L at acut; omega)
  have digitLow := full dy dz splitX.2 perLow (Nat.le_trans lowExpo lb) lowFullCut
  have recover {S e : Nat} (row : DigitRow S z b) (expo : PeriodExp (S+1) e) :
      powers (S+D) (2^b)=S := by
    have extract := short_powers_of_digit row expo (r:=0) (Nat.two_pow_pos b)
    simpa only [Nat.sub_zero,Nat.mul_zero,Nat.add_zero] using extract
  have congruent := powers_project M (X+D) (2^b)
  rw [splitX.1,recover digitLow perLow] at congruent
  have lifted := map_powers a (X+D) (2^b)
  change mul a (powers (X+D) (2^b))=powers v (2^b) at lifted
  rw [parts,recover digitA perA] at lifted
  obtain ⟨k,pa⟩ := has_period_exp ap
  have kM : k≤M := (pa M).mp (positive_half ap (Nat.lt_of_le_of_lt ax ceil))
  have right : mul a (powers (X+D) (2^b))=mul a X := by
    apply row_congr ap pa
    have dk := Nat.pow_dvd_pow 2 kM
    rw [← Nat.mod_mod_of_dvd (powers _ _) dk,← Nat.mod_mod_of_dvd X dk,congruent]
  exact parts.trans (congrArg (fun t => t+D) (lifted.symm.trans (right.trans step.symm)))
termination_by X
decreasing_by exact earlierX

#print axioms boundary_step_below
end Gamma11.Backward
