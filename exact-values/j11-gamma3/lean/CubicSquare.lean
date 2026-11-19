import CubicDensity
import GeometricBootstrap

/-! At the cubic starting degree, the dense repeated-digit rows and
the second-level period estimate determine the square of 2^256-2. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

theorem cap_of_positive_even_cut (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {d q : Nat} (dy : IsDyadic q) (width : 2≤q) (room : q<d) (bound : d≤q*q)
    (bridges : UpperBridges tables d q) {z r : Nat} (positive : 0<r) (below : r<q)
    (crit : signature d z=r) : d≤act tables d z q := by
  let x := z%2^q
  have inRange : x<2^q := Nat.mod_lt z (Nat.two_pow_pos _)
  have nonzero : 0<x := by
    apply Nat.pos_of_ne_zero; intro hz
    have h := (le_signature d z q (Nat.le_of_lt room)).mpr hz
    omega
  have low := (le_signature d z 1 (by omega)).mp (show 1≤signature d z by omega)
  have dw := Nat.pow_dvd_pow 2 (show 1≤q by omega)
  have base := Nat.mod_eq_zero_of_dvd dw
  have same := Nat.mod_mod_of_dvd z dw
  change x%2=z%2 at same
  change z%2=0 at low
  change 2^q%2=0 at base
  have hi : x≤2^q-2 := by omega
  have hz : z%2^(0+q)=2^0*x+(2^0-1) := by simp [x]
  exact shifted_period_bound H law width dy (Nat.dvd_zero _) (by omega : 0+q≤d) room
    (Nat.le_refl d) (by omega) bridges z x nonzero hi hz (by intro h; omega)

theorem wide_add_projection {u d A y : Nat} (wide : WidePeriodEstimates u) (degree : d≤u+1)
    (aligned : 2^256∣A) (positive : 0<A) (yPos : 0<y) (yFit : y≤2^256-2) (fit : A+y<2^d) :
    (tables d).mul A y=A+y := by
  have up := Nat.pow_le_pow_right (by decide : 0<2) degree
  have known := wide.addition A positive (by omega) aligned y yPos yFit
  have pr := (tables (u+1)).projection (tables d) (Nat.pow_dvd_pow 2 degree) A y
  rw [known,Nat.mod_eq_of_lt fit] at pr; exact pr.symm

private theorem next_even_word {n y : Nat} (width : 0<n) (even : y%2=0) :
    repeatBits n n (y+1)=repeatBits n n y+(2^n-1) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width)
  conv => lhs; arg 2; rw [hk]
  conv => rhs; arg 1; arg 2; rw [hk]
  rw [repeatBits,if_neg (show (y+1)%2≠0 by omega),repeatBits,if_pos even,Nat.zero_add,
    show (y+1)/2=y/2 by omega,Nat.add_comm]

theorem square_from_dense_backgrounds (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {n d : Nat} (dy : IsDyadic n) (width : 2≤n) (room : n*n≤d) (bridges : UpperBridges tables d n)
    (guard : ∀ r z, n≤r → r<n*n → signature d z=r → n*n≤act tables d z r → d≤act tables d z (n*n))
    (add : ∀ A, 0<A → 2^n∣A → A+(2^n-2)<2^d → (tables d).mul A (2^n-2)=A+(2^n-2)) :
    (tables d).mul (2^n-2) (2^n-2)=2^(n*n)-2^n := by
  let p := 2^n
  let a := p-2
  have pp : 4≤p := Nat.pow_le_pow_right (by decide : 0<2) width
  have nn : n≤n*n := Nat.le_mul_of_pos_left _ (by omega)
  have high := Nat.pow_le_pow_right (by decide : 0<2) room
  have pfit := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_trans nn room)
  have last : a+1=p-1 := by dsimp [a]; omega
  have formula (v : Nat) (stop : v+1≤a) : (tables d).mul a (v+1)=repeatBits n n (v+1) := by
    induction v with
    | zero =>
      rw [(tables d).mul_one,repeatBits_one _ _ (by omega),Nat.mod_eq_of_lt (by change a+1<2^d; change p≤2^d at pfit; omega)]
      exact last
    | succ i ih =>
      rw [(tables d).row_recurrence a (i+1),ih (by omega),last]
      by_cases even : (i+1)%2=0
      · let A := repeatBits n n (i+1)
        have data := repeated_background width (Nat.zero_lt_succ i) even (show i+1<2^n-2 from stop)
        change 2^n∣A ∧ 0<A ∧ A+(2^n-2)<2^(n*n)-2 ∧ _ at data
        obtain ⟨dv,pos,sm,dense⟩ := data
        change zeroDigits (A+a) (n*n)≤zeroDigits (A+a) n+(n-2)*n at dense
        change A+a<2^(n*n)-2 at sm
        have word : (A+a)%2^n=2^n-2 := by
          rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd dv,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by change p-2<p; omega)]
        have jump := first_move_from_run tables (s:=1) (by omega : 1<n) (Nat.le_trans nn room) word
        have small : act tables d (A+a) 1<n*n := by
          apply Nat.lt_of_not_ge; intro big
          have forced := first_moved_low tables jump.1 (by omega : 1<n*n) room big
          rw [Nat.mod_eq_of_lt (show A+a<2^(n*n) by omega)] at forced
          omega
        have period := dense_terminal tables width room bridges guard word small dense
        have zero := (le_act_iff tables d (A+a) n d (Nat.le_refl _)).mp period
        have one : (A+1)%2^n=1 := by
          rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd dv,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (show 1<p by omega)]
        change (tables d).mul A (p-1)=repeatBits n n ((i+1)+1)
        rw [←last,(tables d).row_recurrence A a,add A pos dv (by omega), (tables d).reduce_period zero (A+1),one,
          (tables d).mul_one,Nat.mod_eq_of_lt (show A+a+1<2^d by omega),next_even_word (by omega : 0<n) even]
        change A+a+1=A+(p-1); omega
      · exact even_stretched_step H law dy width room bridges guard even (by change i+1+1<p; dsimp [a] at stop; omega)
  have eqv : a-1+1=a := Nat.sub_add_cancel (by dsimp [a]; omega)
  have out := formula (a-1) (Nat.le_of_eq eqv)
  rw [eqv,repeatBits_penultimate _ _ (by omega : 0<n)] at out
  exact out

def CubicSquare : Prop := (tables seedDegree).mul (2^256-2) (2^256-2)=2^(256*256)-2^256

theorem square_at_cubic_degree (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) : CubicSquare := by
  have law : FiniteBlockLaw := finite_block_of_restore Backward.finite_restoration
  have low : UpperBridges tables seedDegree 256 := double_width_bridges H law 3 _ (by decide)
  have high : UpperBridges tables seedDegree (256*256) := double_width_bridges H law 4 _ (by decide)
  have limit : seedDegree≤targetIndex+1 := Nat.succ_le_succ (targetIndex_eq.symm ▸
    Nat.pow_le_pow_right (by decide : 0<256) (by decide : 3≤256))
  apply square_from_dense_backgrounds (n:=256) (d:=seedDegree) H law ⟨8,rfl⟩ (by decide) (by decide) low
  · intro r z lo highR crit _
    exact cap_of_positive_even_cut H law (q:=256*256) ⟨16,rfl⟩ (by decide) (by decide) (by decide)
      high (by omega) highR crit
  · intro A pos dv fits
    exact wide_add_projection wide limit dv pos (by decide) (Nat.le_refl _) fits

#print axioms square_at_cubic_degree
end Gamma11
