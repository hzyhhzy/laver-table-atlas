import DoubleWidths

/-! Restore a filled binary tail by removing the least dyadic divisor of
its current length. The period allowance grows by that divisor, which
is at most the next divisor. The mixed-digit bound used before this
restoration is derived from the ordinary finite block law. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def fillLow (a s : Nat) := 2^s*(a/2^s)+(2^s-1)

/-- The one-block period consequence used from Dougherty II, 4.2/4.6,
in forward representatives. Starting with z+b low ones, restore b
digits and leave z low ones. -/
def RestoreBlockLaw : Prop := ∀ {d z b q A y : Nat}, IsDyadic b → b ∣ z → z+b≤d →
    2^(z+b) ∣ A → q≤b → y<2^b → act tables d (A+(2^(z+b)-1)) q=d →
    act tables d (A+2^z*y+(2^z-1)) (if y=0 then q+b else b)=d

theorem odd_factor {k : Nat} (pos : 0<k) : ∃ l t, k=2^l*(2*t+1) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases odd : k%2=1
    · exact ⟨0,k/2,by simp only [Nat.pow_zero,Nat.one_mul]; omega⟩
    · have small : k/2<k := Nat.div_lt_self pos (by decide)
      obtain ⟨l,t,eqv⟩ := ih _ small (by omega)
      refine ⟨l+1,t,?_⟩
      rw [Nat.pow_succ,Nat.mul_comm (2^l) 2,Nat.mul_assoc,← eqv]; omega

private theorem split_filled {a z b : Nat} :
    fillLow a z=2^(z+b)*(a/2^(z+b))+2^z*((a/2^z)%2^b)+(2^z-1) := by
  have pieces := congrArg (fun x => 2^z*x) (Nat.div_add_mod (a/2^z) (2^b))
  change 2^z*(2^b*((a/2^z)/2^b)+(a/2^z)%2^b)=2^z*(a/2^z) at pieces
  rw [Nat.mul_add,← Nat.mul_assoc,Nat.div_div_eq_div_mul,← Nat.pow_add] at pieces
  unfold fillLow; rw [← pieces]

theorem restore_tail_periods (restore : RestoreBlockLaw) {d a : Nat} (s q : Nat)
    (room : s≤d) (license : ∃ u, IsDyadic u ∧ q≤u ∧ u ∣ s) (start : act tables d (fillLow a s) q=d) :
    act tables d a (q+s)=d ∧ (a%2^s≠0 → act tables d a s=d) := by
  by_cases done : s=0
  · subst s; exact ⟨by simpa [fillLow] using start,fun bad => False.elim (bad (Nat.mod_one a))⟩
  obtain ⟨u,⟨e,ue⟩,qu,k,sk⟩ := license
  have positive : 0<u := ue ▸ Nat.two_pow_pos e
  have kp : 0<k := by
    apply Nat.pos_of_ne_zero; intro kz; rw [kz,Nat.mul_zero] at sk; exact done sk
  obtain ⟨l,t,eqv⟩ := odd_factor kp
  let b := u*2^l
  let z := (2*b)*t
  have bp : 0<b := Nat.mul_pos positive (Nat.two_pow_pos l)
  have dy : IsDyadic b := ⟨e+l,by dsimp [b]; rw [ue,Nat.pow_add]⟩
  have size : s=z+b := by
    rw [sk,eqv,← Nat.mul_assoc,Nat.mul_succ,← Nat.mul_assoc,Nat.mul_comm _ 2]
  have decrease : z<s := by omega
  have qb : q≤b := Nat.le_trans qu (Nat.le_of_dvd bp (Nat.dvd_mul_right ..))
  have bz : b ∣ z := Nat.dvd_trans (Nat.dvd_mul_left b 2) (Nat.dvd_mul_right ..)
  have dy2 : IsDyadic (2*b) := by
    obtain ⟨f,rep⟩ := dy
    exact ⟨f+1,by rw [Nat.pow_succ,← rep,Nat.mul_comm]⟩
  let A := 2^(z+b)*(a/2^(z+b))
  have old : act tables d (A+(2^(z+b)-1)) q=d := by
    change act tables d (fillLow a (z+b)) q=d; rw [← size]; exact start
  have next := restore dy bz (by omega : z+b≤d) (show 2^(z+b) ∣ A from Nat.dvd_mul_right ..)
    qb (Nat.mod_lt (a/2^z) (Nat.two_pow_pos b)) old
  rw [← split_filled] at next
  let y := a/2^z%2^b
  let p := if y=0 then q+b else b
  have pb : p≤q+b := by dsimp [p]; split <;> omega
  have tail := restore_tail_periods restore z p (by omega : z≤d)
    ⟨2*b,dy2,by omega,Nat.dvd_mul_right ..⟩ next
  have reaches {l h : Nat} (val : act tables d a l=d) (leq : l≤h) : act tables d a h=d :=
    Nat.le_antisymm (act_le ..) (Nat.le_trans (Nat.le_of_eq val.symm) (act_mono tables d a leq))
  refine ⟨reaches tail.1 (by omega),?_⟩
  intro nonzero
  by_cases already : a%2^z≠0
  · exact reaches (tail.2 already) (Nat.le_of_lt decrease)
  · have yd : y≠0 := by
      intro eq0
      have low : a%2^z=0 := by omega
      rw [size,Nat.pow_add,Nat.mod_mul,low,show a/2^z%2^b=0 from eq0,Nat.mul_zero] at nonzero
      exact nonzero rfl
    have reduced : p=b := if_neg yd
    exact reaches tail.1 (by omega)
termination_by s
decreasing_by exact decrease

theorem restore_tail (restore : RestoreBlockLaw) {d a : Nat} (s q : Nat)
    (room : s≤d) (license : ∃ u, IsDyadic u ∧ q≤u ∧ u ∣ s) (start : act tables d (fillLow a s) q=d) :
    act tables d a (q+s)=d := (restore_tail_periods restore s q room license start).1

/-- The sharp restoration bound also gives the full additive prefix
needed at the right endpoint of Dougherty II, Lemma 6.3. -/
theorem finite_block_of_restore (restore : RestoreBlockLaw) : FiniteBlockLaw := by
  intro w p X d dyadic mult divX endRow
  have qpos := Nat.two_pow_pos p
  by_cases limit : d≤p
  · have divides := Nat.pow_dvd_pow 2 limit
    have x0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans divides divX)
    have q0 := Nat.mod_eq_zero_of_dvd divides
    rw [← (tables d).mul_mod_right X,q0,(tables d).mul_zero,Nat.add_mod,x0,q0,Nat.zero_add,Nat.zero_mod]
  by_cases empty : p=0
  · subst p; exact (tables d).mul_one X
  have big : 1<2^p := Nat.one_lt_two_pow empty
  have guard : act tables d (X+(2^p-1)) w=d := by
    have zero : (tables d).mul (X+(2^p-1)) (2^w)=0 := by
      rw [canonical_mul,show X+(2^p-1)=X+2^p-1 by omega]; exact endRow
    exact Nat.le_antisymm (act_le ..) ((le_act_iff tables d _ w d (Nat.le_refl _)).mpr zero)
  have one : (X+1)%2^p=1 := by
    rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd divX,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt big]
  have periodic (i : Nat) (pos : 0<i) (small : i<2^p) : act tables d (X+i) p=d := by
    have floor : fillLow (X+i) p=X+(2^p-1) := by
      obtain ⟨b,xb⟩ := divX
      rw [fillLow,xb,Nat.mul_add_div qpos,Nat.div_eq_of_lt small,Nat.add_zero]
    have nonzero : (X+i)%2^p≠0 := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd divX,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt small]; omega
    exact (restore_tail_periods restore p w (by omega) ⟨w,dyadic,Nat.le_refl _,mult⟩ (floor.symm ▸ guard)).2 nonzero
  have add (i : Nat) (hi : i+1≤2^p) : (tables d).mul X (i+1)=(X+(i+1))%2^d := by
    induction i with
    | zero => exact (tables d).mul_one X
    | succ i ih =>
      have hit := periodic (i+1) (by omega) (by omega)
      have zero := (le_act_iff tables d (X+(i+1)) p d (Nat.le_refl _)).mp (Nat.le_of_eq hit.symm)
      rw [(tables d).row_recurrence X (i+1),ih (by omega),(tables d).mul_mod_left,(tables d).reduce_period zero,
        one,(tables d).mul_one,Nat.add_assoc]
  have last := add (2^p-1) (by omega)
  rwa [Nat.sub_add_cancel qpos] at last

private theorem mixed_block_or_repeat (v k x : Nat) (vp : 0<v) (fit : x<2^(k*v)) :
    (∃ u, u<2^k ∧ x=repeatBits v k u) ∨
    ∃ j, j<k ∧ 0<(x/2^(j*v))%2^v ∧ (x/2^(j*v))%2^v<2^v-1 := by
  induction k generalizing x with
  | zero =>
    have xz : x=0 := by simpa using fit
    exact Or.inl ⟨0,by decide,xz⟩
  | succ k ih =>
    let q := 2^v
    let r := x%q
    let h := x/q
    have qp : 1<q := Nat.one_lt_two_pow (by omega : v≠0)
    have rp : r<q := Nat.mod_lt x (by omega : 0<q)
    have div : q*h+r=x := Nat.div_add_mod x q
    by_cases mixed : 0<r ∧ r<q-1
    · exact Or.inr ⟨0,Nat.zero_lt_succ _,by simpa using mixed⟩
    have hf : h<2^(k*v) := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<q)).mpr
      rwa [Nat.succ_mul,Nat.pow_add] at fit
    rcases ih h hf with ⟨u,uf,hu⟩|⟨j,jk,low,top⟩
    · rw [Nat.pow_succ]
      by_cases empty : r=0
      · exact Or.inl ⟨2*u,by omega,by rw [repeatBits,if_pos (by omega : 2*u%2=0),
          Nat.zero_add,show 2*u/2=u by omega,← hu]; change x=q*h; omega⟩
      · exact Or.inl ⟨2*u+1,by omega,by rw [repeatBits,if_neg (by omega : (2*u+1)%2≠0),
          show (2*u+1)/2=u by omega,← hu]; change x=q-1+q*h; omega⟩
    · have align : h/2^(j*v)=x/2^((j+1)*v) := by
        dsimp [h,q]; rw [Nat.div_div_eq_div_mul,← Nat.pow_add,Nat.succ_mul,Nat.add_comm v]
      rw [align] at low top
      exact Or.inr ⟨j+1,by omega,low,top⟩

private theorem filled_word (a s v : Nat) :
    fillLow a s%2^(s+v)=2^s*((a/2^s)%2^v)+(2^s-1) := by
  have ps := Nat.two_pow_pos s
  have hit := (aligned_add_residue (Nat.le_add_right s v) (show 2^s ∣ 2^s*(a/2^s) from Nat.dvd_mul_right ..)
    (by omega : 2^s-1<2^s)).1
  unfold fillLow; rw [hit,Nat.pow_add,Nat.mul_mod_mul_left]

theorem mixed_periods_of_restore (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    (restore : RestoreBlockLaw) : MixedShortPeriods := by
  intro m mp
  dsimp only
  intro x _ upper nonuniform
  let b := 2^m.log2
  let v := 256^b
  let k := 256^(m-b)
  let w := 256^m
  let d := 256*w
  have bm : b≤m := Nat.log2_self_le (by omega)
  have bound := Nat.lt_log2_self (n:=m)
  rw [Nat.pow_succ] at bound
  change m<b*2 at bound
  have width : k*v=w := by dsimp [k,v,w]; rw [← Nat.pow_add,Nat.sub_add_cancel bm]
  have bpos : 0<b := Nat.two_pow_pos _
  have vp : 2≤v := Nat.le_trans (by decide : 2≤256) (Nat.pow_le_pow_right (by decide : 0<256) bpos)
  have kpos : 1≤k := Nat.pow_pos (by decide : 0<256)
  have wd : w≤d := by dsimp [d]; omega
  have lower : v≤w := width ▸ (show v≤k*v by simpa only [Nat.one_mul] using Nat.mul_le_mul_right v kpos)
  have dmax : d≤v*v := by
    dsimp [d,w,v]; rw [Nat.mul_comm 256,← Nat.pow_succ,← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have xFit : x<2^(k*v) := by rw [width]; change x<2^(256^m); omega
  obtain ⟨j,jk,lo,hi⟩ := (mixed_block_or_repeat v k x (by omega) xFit).resolve_left nonuniform
  let s := j*v
  have sv : s+v≤w := by
    have mlt := Nat.mul_le_mul_right v jk
    change (j+1)*v≤k*v at mlt; rw [Nat.succ_mul,width] at mlt; exact mlt
  have eqv : v=2^(2^(m.log2+3)) := by
    dsimp [v,b]; rw [show 256=2^8 by decide,← Nat.pow_mul,Nat.pow_add 2 m.log2 3,Nat.mul_comm 8]
  have dy : IsDyadic v := ⟨_,eqv⟩
  have div : v ∣ s := Nat.dvd_mul_left .. 
  have room : v<d := by dsimp [d]; omega
  have br : UpperBridges tables d v := eqv ▸ double_width_bridges H law (m.log2+3) d (eqv ▸ room)
  have start := shifted_period_bound H law vp dy div (Nat.le_trans sv wd) room (Nat.le_refl d)
    (by omega : d≤s+v*v+1) br (fillLow x s) _ lo (by omega) (filled_word x s v) (by intro high; omega)
  have eqStart := Nat.le_antisymm (act_le ..) start
  have raised := restore_tail restore s v (by omega : s≤d) ⟨v,dy,Nat.le_refl _,div⟩ eqStart
  have full := Nat.le_trans (Nat.le_of_eq raised.symm) (act_mono tables d x (by omega : v+s≤w))
  exact (canonical_mul _ _ _).symm.trans ((le_act_iff tables d x w d (Nat.le_refl _)).mp full)

#print axioms restore_tail
#print axioms finite_block_of_restore
#print axioms mixed_periods_of_restore
end Gamma11
