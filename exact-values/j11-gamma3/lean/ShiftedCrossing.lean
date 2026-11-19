import ShiftedBoundary

/-! The shifted crossing in Dougherty's Claim 1 (Appendix D.1):
move to a strictly larger even residue in the same block. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem first_bridge (F : BinaryFamily) {m n : Nat} (width : 2≤n) (room : n<m) :
    let z := 2^n-3
    signature m z=0 ∧ act F m z 0=1 ∧ act F m z 1=n := by
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have first : act F m (2^n-3) 0=1 := by
    rw [act_zero,show 2^n-3+1=2^n-2^1 by omega]
    exact dyadic_tail_signature m n 1 (by omega) (by omega)
  have sig : signature m (2^n-3)=0 := by
    apply Nat.eq_zero_of_not_pos; intro h
    have fixed := fixes_below_signature F m (2^n-3) 0 h
    omega
  exact ⟨sig,first,act_of_lower_entry F room (row_minus_three_at_two F n width)⟩

/-- The two lowest zero positions determine the first two images at
the boundary, allowing the second image to lie beyond the cutoff. -/
theorem run_after_zero (F : BinaryFamily) {m a s p : Nat} (sp : s<p) (pm : p≤m)
    (word : a%2^p=2^p-2^s-1) : act F m a 0=s ∧ p≤act F m a 1 := by
  have lt := Nat.pow_lt_pow_right (by decide : 1<2) sp
  have pos := Nat.two_pow_pos s
  have cut : (a+1)%2^p=2^p-2^s := by
    rw [Nat.add_mod,word,Nat.mod_eq_of_lt (by omega : 1<2^p),Nat.mod_eq_of_lt (by omega : 2^p-2^s-1+1<2^p)]
    omega
  have sq0 := (square_zero_iff F p (2^p-2^s) (by omega)).mpr (Or.inr ⟨s,sp,rfl⟩)
  have sig := (first_move_from_run F sp pm cut).1
  refine ⟨(act_zero F m a).trans sig,(le_act_iff F m a 1 p pm).mpr ?_⟩
  change (F p).mul a 2=0
  rw [(F p).row_recurrence a 1,(F p).mul_one,cut,← (F p).mul_mod_right _ (a+1),cut]
  exact sq0

private theorem remainder_before_block {a s n x : Nat}
    (word : a%2^(s+n)=2^s*x+(2^s-1)) : a%2^s=2^s-1 := by
  have low := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (Nat.le_add_right s n))
  rw [word,Nat.add_mod,Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right (2^s) x),
    Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by have := Nat.two_pow_pos s; omega : 2^s-1<2^s)] at low
  exact low.symm

theorem shifted_crossing_with_row (F : BinaryFamily) {m n s a x : Nat} (width : 2≤n)
    (room : s+n≤m) (endRoom : n<m) (bridges : UpperBridges F m n)
    (low : 0<x) (inside : x<2^n-2) (word : a%2^(s+n)=2^s*x+(2^s-1)) :
    ∃ z x' β, x<x' ∧ x'≤2^n-2 ∧ z%2^(s+n)=2^s*x' ∧ 2^s ∣ z ∧
      s+n≤act F m a β ∧ act F m z (act F m a β)=act F m a n ∧ ∃ c, z=(F m).mul a c := by
  let f := act F m a
  have ps := Nat.two_pow_pos s
  have pn := Nat.two_pow_pos n
  have snpow : 2^(s+n)=2^s*2^n := Nat.pow_add ..
  have space := Nat.mul_le_mul_left (2^s) (show x+2≤2^n-1 by omega)
  have lesser := Nat.mul_lt_mul_of_pos_left (show x+2<2^n by omega) ps
  rw [Nat.mul_add] at lesser
  have beforeEnd : a%2^(s+n)<2^(s+n)-1 := by rw [word,snpow]; omega
  have start : s≤f 0 := by
    apply (le_act_iff F m a 0 s (by omega)).mpr
    change (F s).mul a 1=0
    rw [← (F s).mul_mod_left a,(F s).mul_one,remainder_before_block word,
      show 2^s-1+1=2^s by omega,Nat.mod_self]
  have init : f 0<s+n := act_zero_lt_of_residue F m a _ room beforeEnd
  have high : s+n≤f (n-1) := by
    apply Nat.le_of_not_gt; intro stop
    have vis : f (n-1)<m := Nat.lt_of_lt_of_le stop room
    have d := act_distance F m a (Nat.zero_le (n-1)) vis
    change f 0+(n-1-0)≤f (n-1) at d
    have f0 : f 0=s := by omega
    have endv : f (n-1)+1=s+n := by omega
    have tight := consecutive_residue_lt F (Nat.zero_le (n-1)) vis (show f (n-1)=f 0+((n-1)-0) by omega)
    change a%2^(f (n-1)+1)<2^(f 0) at tight
    rw [endv,f0,word] at tight
    have lower := Nat.mul_le_mul_left (2^s) (show 1≤x from low)
    rw [Nat.mul_one] at lower; omega
  obtain ⟨r,short,hit,prior⟩ := least_bounded_hit (P:=fun i => s+n≤f i) (n-1) high
  have rp : 0<r := by rcases Nat.eq_zero_or_pos r with h|h; rw [h] at hit; omega; exact h
  have pair : ∃ α β c, α<r ∧ r≤β ∧ signature m c=α ∧ act F m c α=β ∧ act F m c β=n ∧ s<f α := by
    by_cases early : r=1
    · rw [early] at hit
      have strict : s<f 0 := by
        apply Nat.lt_of_not_ge; intro small
        have exactS : f 0=s := by omega
        have top := first_two_cut F room (by omega : s<s+n) exactS hit
        rw [word,snpow] at top; omega
      obtain ⟨cs,c0,c1⟩ := first_bridge F width endRoom
      exact ⟨0,1,_,rp,early ▸ Nat.le_refl _,cs,c0,c1,strict⟩
    · obtain ⟨α,β,c,positive,left,right,cs,c0,c1⟩ := bridges r (by omega) (by omega)
      have sm := Nat.lt_of_not_ge (prior α left)
      have vis : f α<m := Nat.lt_of_lt_of_le sm room
      have strict := act_strict_below_cap F m a 0 α positive vis
      exact ⟨α,β,c,left,right,cs,c0,c1,Nat.lt_of_le_of_lt start strict⟩
  obtain ⟨α,β,c,left,right,cs,_,last,greater⟩ := pair
  let z := (F m).mul a c
  have zs : signature m z=f α := (signature_mul F m a c).trans (congrArg f cs)
  have below := Nat.lt_of_not_ge (prior α left)
  have nz : z%2^(s+n)≠0 := fun h => (Nat.not_le_of_gt below) (zs ▸ (le_signature m z (s+n) room).mpr h)
  have more := left_residue_lt F (a:=a) (b:=c) room nz
  change a%2^(s+n)<z%2^(s+n) at more
  rw [word] at more
  have evenZ := (le_signature m z (s+1) (by omega)).mp (zs.symm ▸ greater)
  have dv := Nat.pow_dvd_pow 2 (show s+1≤s+n by omega)
  obtain ⟨u,hu⟩ : 2^(s+1) ∣ z%2^(s+n) :=
    Nat.dvd_of_mod_eq_zero ((Nat.mod_mod_of_dvd z dv).trans evenZ)
  have rep : z%2^(s+n)=2^s*(2*u) := by rw [hu,Nat.pow_succ,Nat.mul_assoc]
  have first : x<2*u := by
    apply Nat.lt_of_not_ge; intro reverse
    have bad := Nat.mul_le_mul_left (2^s) reverse
    rw [rep] at more; omega
  have size := Nat.mod_lt z (Nat.two_pow_pos (s+n))
  rw [rep,snpow] at size
  have second : 2*u<2^n := Nat.lt_of_mul_lt_mul_left size
  have evenN := Nat.pow_succ 2 (n-1)
  rw [show (n-1).succ=n by omega] at evenN
  have div : 2^s ∣ z := Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ _)) (Nat.dvd_of_mod_eq_zero evenZ)
  have endv := act_application F m a c β
  rw [last] at endv
  exact ⟨z,2*u,β,first,by omega,rep,div,Nat.le_trans hit (act_mono F m a right),endv,c,rfl⟩

theorem shifted_crossing (F : BinaryFamily) {m n s a x : Nat} (width : 2≤n)
    (room : s+n≤m) (endRoom : n<m) (bridges : UpperBridges F m n)
    (low : 0<x) (inside : x<2^n-2) (word : a%2^(s+n)=2^s*x+(2^s-1)) :
    ∃ z x' β, x<x' ∧ x'≤2^n-2 ∧ z%2^(s+n)=2^s*x' ∧ 2^s ∣ z ∧
      s+n≤act F m a β ∧ act F m z (act F m a β)=act F m a n := by
  obtain ⟨z,y,β,l,u,p,d,reaches,last,_⟩ := shifted_crossing_with_row F width room endRoom bridges low inside word
  exact ⟨z,y,β,l,u,p,d,reaches,last⟩

#print axioms shifted_crossing

private theorem terminal_shift {m n s a h : Nat} (width : 2≤n) (room : n*n≤m)
    (ns : n≤s) (smax : s<n*n) (span : s+n≤m) (bridges : UpperBridges tables m n)
    (guard : ∀ r z, n≤r → r<n*n → signature m z=r → n*n≤act tables m z r → h≤act tables m z (n*n))
    (word : a%2^(s+n)=2^s*(2^n-2)+(2^s-1)) : h≤act tables m a n := by
  let f := act tables m a
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have ps := Nat.two_pow_pos s
  have product := congrArg (fun z => 2^s*z) (Nat.sub_add_cancel (show 2≤2^n by omega))
  change 2^s*(2^n-2+2)=2^s*2^n at product
  rw [Nat.mul_add] at product
  have converted : a%2^(s+n)=2^(s+n)-2^s-1 := by rw [word,Nat.pow_add]; omega
  obtain ⟨f0,f1⟩ := run_after_zero tables (by omega : s<s+n) span converted
  have high : n*n≤f (n-1) := by
    by_cases vis : f (n-1)<m
    · have bound := linear_growth tables m a (n-1) vis
      rw [f0] at bound
      have b := Nat.mul_le_mul_right (n-1) (show n≤act tables m a 1-s by omega)
      have square := Nat.mul_succ n (n-1)
      rw [show (n-1).succ=n by omega] at square
      change _≤f (n-1) at bound; omega
    · omega
  obtain ⟨r,lesser,hit,before⟩ := least_bounded_hit (P:=fun i => n*n≤f i) (n-1) high
  have rp : 0<r := by
    rcases Nat.eq_zero_or_pos r with eqv|yes
    · rw [eqv] at hit; change n*n≤act tables m a 0 at hit; omega
    · exact yes
  have pair : ∃ α β c, α<r ∧ r≤β ∧ signature m c=α ∧ act tables m c α=β ∧ act tables m c β=n := by
    by_cases first : r=1
    · obtain ⟨sig,fst,snd⟩ := first_bridge tables width (by omega : n<m)
      exact ⟨0,1,_,rp,first ▸ Nat.le_refl _,sig,fst,snd⟩
    · obtain ⟨α,β,c,_,l,u,sig,fst,snd⟩ := bridges r (by omega) (by omega)
      exact ⟨α,β,c,l,u,sig,fst,snd⟩
  obtain ⟨α,β,c,l,u,sig,fst,snd⟩ := pair
  let z := (tables m).mul a c
  have low := Nat.le_trans ns (f0 ▸ act_mono tables m a (Nat.zero_le α))
  have upper := Nat.lt_of_not_ge (before α l)
  have zs : signature m z=f α := (signature_mul tables m a c).trans (congrArg f sig)
  have zα := act_application tables m a c α
  have zβ := act_application tables m a c β
  rw [fst] at zα
  rw [snd] at zβ
  have jump := Nat.le_trans hit (act_mono tables m a u)
  exact Nat.le_trans (guard (f α) z low upper zs (zα.symm ▸ jump))
    (Nat.le_trans (act_mono tables m z jump) (Nat.le_of_eq zβ))

/-- Descending induction on the shifted base-2^n digit. The right
endpoint of the block lemma and the small-critical estimates are the
only nonlocal inputs. -/
theorem shifted_digit_bound (H : TableElement.FirstRowUnbounded) (law : FiniteBlockLaw)
    {m n s h : Nat} (dyadic : IsDyadic n) (multiple : n ∣ s) (width : 2≤n)
    (room : n*n≤m) (ns : n≤s) (smax : s<n*n) (span : s+n≤m) (bridges : UpperBridges tables m n)
    (guard : ∀ r z, n≤r → r<n*n → signature m z=r → n*n≤act tables m z r → h≤act tables m z (n*n))
    (a x : Nat) (lo : 1≤x) (top : x≤2^n-2) (word : a%2^(s+n)=2^s*x+(2^s-1)) :
    h≤act tables m a n := by
  by_cases last : x=2^n-2
  · rw [last] at word; exact terminal_shift width room ns smax span bridges guard word
  obtain ⟨z,y,β,inc,ymax,rep,aligned,passed,link⟩ := shifted_crossing tables width span (by omega)
    bridges lo (by omega : x<2^n-2) word
  have pos := Nat.two_pow_pos s
  have less := Nat.mul_lt_mul_of_pos_left (show y+1<2^n by omega) pos
  rw [Nat.mul_succ] at less
  have replace : z+2^s-1=z+(2^s-1) := by omega
  have fit : 2^s-1<2^(s+n) := Nat.lt_of_lt_of_le (by omega : 2^s-1<2^s)
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right s n))
  have zword : (z+2^s-1)%2^(s+n)=2^s*y+(2^s-1) := by
    rw [replace,Nat.add_mod,rep,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt (by rw [Nat.pow_add]; omega : 2^s*y+(2^s-1)<2^(s+n))]
  have next := shifted_digit_bound H law dyadic multiple width room ns smax span bridges guard
    (z+2^s-1) y (by omega) ymax zword
  have advance := shifted_action_bound H law dyadic multiple aligned m
  exact Nat.le_trans next (Nat.le_trans advance (Nat.le_trans (act_mono tables m z passed) (Nat.le_of_eq link)))
termination_by 2^n-1-x
decreasing_by omega

#print axioms shifted_digit_bound

private theorem repeated_low_odd {n t : Nat} (np : 0<n) (odd : t%2≠0) :
    repeatBits n n t%2^n=2^n-1 := by
  have pos := Nat.two_pow_pos n
  rw [show n=(n-1)+1 by omega] at *
  rw [repeatBits,if_neg odd,Nat.add_mod,Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right ..),
    Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

/-- D.2 in the displayed formulas of the manuscript (the even carry
in Section D.1). It applies at any width with the indicated bridges
and critical-position bounds, not only at width 16. -/
theorem even_stretched_step (H : TableElement.FirstRowUnbounded) (law : FiniteBlockLaw)
    {m n y : Nat} (dyadic : IsDyadic n) (width : 2≤n) (room : n*n≤m) (bridges : UpperBridges tables m n)
    (guard : ∀ r z, n≤r → r<n*n → signature m z=r → n*n≤act tables m z r → m≤act tables m z (n*n))
    (odd : y%2≠0) (fit : y+1<2^n) :
    (tables m).mul (repeatBits n n y) (2^n-1)=repeatBits n n (y+1) := by
  obtain ⟨B,s,div,span,background,old,next⟩ := repeatBits_carry n n y fit
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have start : 0<s := by
    apply Nat.pos_of_ne_zero
    intro eqv
    rw [eqv,Nat.zero_add] at background
    rw [eqv,Nat.pow_zero,Nat.add_sub_cancel] at old
    have forced := repeated_low_odd (by omega : 0<n) odd
    rw [old,Nat.mod_eq_zero_of_dvd background] at forced; omega
  have ns := Nat.le_of_dvd start div
  have sm : s<n*n := by omega
  have value (j : Nat) (lo : 2≤j) (hi : j≤2^n-1) : act tables m (B+2^s*j-1) n=m := by
    have ps := Nat.two_pow_pos s
    have jp : 1≤j := by omega
    have prev : 2^s*(j-1)+2^s=2^s*j := by rw [← Nat.mul_succ,show (j-1).succ=j by omega]
    have upper := Nat.mul_lt_mul_of_pos_left (show j<2^n by omega) ps
    have floor : B+2^s*j-1=B+(2^s*(j-1)+(2^s-1)) := by omega
    have inside : 2^s*(j-1)+(2^s-1)<2^(s+n) := by rw [Nat.pow_add]; omega
    have word : (B+2^s*j-1)%2^(s+n)=2^s*(j-1)+(2^s-1) := by
      rw [floor,Nat.add_mod,Nat.mod_eq_zero_of_dvd background,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt inside]
    have high := shifted_digit_bound H law dyadic div width room ns sm (Nat.le_trans span room) bridges guard
      _ (j-1) (by omega) (by omega) word
    exact Nat.le_antisymm (act_le ..) high
  have prev := guarded_shift_multiplication H law dyadic div background (2^n-2)
    (fun j lb ub => value j lb (by omega))
  rw [show 2^n-2+1=2^n-1 by omega,← old,← next] at prev
  exact prev.trans (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (repeatBits_lt n n (y+1)) (Nat.pow_le_pow_right (by decide) room)))

#print axioms even_stretched_step
end Gamma11
