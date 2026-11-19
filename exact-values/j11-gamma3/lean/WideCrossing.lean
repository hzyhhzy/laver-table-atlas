import CriticalSixteen

/-! Propagation of the critical-sixteen estimate to 16 ≤ r < 256.
The first two bridges are transported by the row 65534. The others
are members of the ordinary dyadic family. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private def Bridge (m α β n row : Nat) : Prop :=
  signature m row=α ∧ act tables m row α=β ∧ act tables m row β=n

private theorem transport_bridge {m α β n row : Nat} (h : Bridge m α β n row) (z : Nat) :
    Bridge m (act tables m z α) (act tables m z β) (act tables m z n) ((tables m).mul z row) := by
  obtain ⟨sig,first,last⟩ := h
  refine ⟨(signature_mul tables m z row).trans (congrArg (act tables m z) sig),?_,?_⟩
  · exact (act_application tables m z row α).trans (congrArg (act tables m z) first)
  · exact (act_application tables m z row β).trans (congrArg (act tables m z) last)

theorem dyadic_interval {n r : Nat} (k : Nat) (start : n-2^(k+1)<r) (stop : r<n) :
    ∃ i, i≤k ∧ n-2^(i+1)<r ∧ r≤n-2^i := by
  induction k with
  | zero => exact ⟨0,Nat.le_refl _,start,by omega⟩
  | succ k ih =>
    by_cases before : r≤n-2^(k+1)
    · exact ⟨k+1,Nat.le_refl _,start,before⟩
    · obtain ⟨i,ik,l,u⟩ := ih (by omega)
      exact ⟨i,by omega,l,u⟩

private theorem wide_bridges {m r : Nat} (room : 272≤m) (hom : SixteenRowData)
    (four : act tables m 14 4=16) (lo : 16<r) (hi : r<256) :
    ∃ α β row, 16≤α ∧ α<r ∧ r≤β ∧ Bridge m α β 256 row := by
  have stretched (i : Nat) (bound : i<17) : act tables m 65534 i=i*16 :=
    hom.action room bound
  have f1 : act tables m 14 1=4 := act_from_low tables m 14 1 _ 4 (by omega) (LowProducts.v14_2 _) (by decide) (by decide)
  have f2 : act tables m 14 2=8 := act_from_low tables m 14 2 _ 8 (by omega) (LowProducts.v14_4 _) (by decide) (by decide)
  by_cases left : r≤64
  · have sig : signature m 14=1 := signature_lift (by omega : 2≤m) (by decide : signature 2 14<2)
    have h := transport_bridge (show Bridge m 1 4 16 14 from ⟨sig,f1,four⟩) 65534
    rw [stretched 1 (by decide),stretched 4 (by decide),stretched 16 (by decide)] at h
    exact ⟨16,64,_,Nat.le_refl _,lo,left,h⟩
  by_cases mid : r≤128
  · have sig : signature m 2=1 := signature_pow m 1 (by omega)
    have b1 := act_from_low tables m 2 1 _ 2 (by omega) (LowProducts.v2_2 _) (by decide) (by decide)
    have b2 := act_from_low tables m 2 2 _ 4 (by omega) (LowProducts.v2_4 _) (by decide) (by decide)
    have h := transport_bridge (show Bridge m 1 2 4 2 from ⟨sig,b1,b2⟩) 14
    rw [f1,f2,four] at h
    have g := transport_bridge h 65534
    rw [stretched 4 (by decide),stretched 8 (by decide),stretched 16 (by decide)] at g
    exact ⟨64,128,_,by decide,by omega,mid,g⟩
  · obtain ⟨i,limI,l,u⟩ := dyadic_interval (n:=256) 6 (by omega : 256-2^(6+1)<r) hi
    obtain ⟨row,shape⟩ := dyadic_anchors tables 8 m (by omega) i (by omega)
    have bound := Nat.pow_le_pow_right (by decide : 0<2) (show i+1≤7 by omega)
    exact ⟨_,_,row,show 16≤256-2^(i+1) by omega,l,u,shape⟩

theorem critical_sixteen_to_255 {m : Nat} (room : 272≤m) (stretch : SixteenRowData)
    (four : act tables m 14 4=16)
    (base : ∀ row, signature m row=16 → 256≤act tables m row 16 → act tables m row 256=m)
    (r row : Nat) (lo : 16≤r) (hi : r<256) (sig : signature m row=r)
    (jump : 256≤act tables m row r) : act tables m row 256=m := by
  induction r using Nat.strongRecOn generalizing row with
  | ind r ih =>
    by_cases eqv : r=16
    · rw [eqv] at sig jump; exact base row sig jump
    obtain ⟨α,β,c,amin,left,right,br⟩ := wide_bridges room stretch four (by omega) hi
    have h := transport_bridge br row
    have fixed := fixes_below_signature tables m row α (sig ▸ left)
    rw [fixed] at h
    have high := Nat.le_trans jump (act_mono tables m row right)
    obtain ⟨s,f,l⟩ := h
    have sat := ih α left _ amin (by omega) s (f.symm ▸ high)
    have up := act_mono tables m ((tables m).mul row c) high
    rw [sat,l] at up
    exact Nat.le_antisymm (act_le ..) up

#print axioms critical_sixteen_to_255

theorem least_bounded_hit {P : Nat → Prop} (n : Nat) (hit : P n) :
    ∃ r, r≤n ∧ P r ∧ ∀ i, i<r → ¬P i := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases prior : ∃ r, r<n ∧ P r
    · obtain ⟨r,rn,found⟩ := prior
      obtain ⟨i,ir,pi,least⟩ := ih r rn found
      exact ⟨i,Nat.le_trans ir (Nat.le_of_lt rn),pi,least⟩
    · exact ⟨n,Nat.le_refl _,hit,fun i h hi => prior ⟨i,h,hi⟩⟩

/-- The wide crossing for Appendix E. At the two low starting
positions the right endpoint is determined, which is needed to
separate the two possible exceptional rows. -/
theorem cross_256 {m a : Nat} (room : 272≤m) (hom : SixteenRowData)
    (four : act tables m 14 4=16) (lo : 0<a%2^256) (hi : a%2^256<2^256-2) :
    ∃ α β row, signature m row=α ∧ act tables m row α=β ∧ act tables m row β=256 ∧
      (α=0 → β=1) ∧ (α=1 → β=16) ∧ 0<act tables m a α ∧ act tables m a α<256 ∧
      256≤act tables m a β := by
  let f := act tables m a
  have zero : f 0<256 := act_zero_lt_of_residue tables m a 256 (by omega) (by omega)
  have high : 256≤f 255 := by
    apply Nat.le_of_not_gt
    intro low
    have vis : f 255<m := Nat.lt_trans low (by omega)
    have dist := act_distance tables m a (by decide : 0≤255) vis
    change f 0 + (255-0) ≤ f 255 at dist
    have z : f 0=0 := by omega
    have e : f 255=255 := by omega
    have h := consecutive_residue_lt tables (by decide : 0≤255) vis (show f 255=f 0+(255-0) by omega)
    change a%2^(f 255+1)<2^(f 0) at h
    rw [e,z] at h; omega
  obtain ⟨r,bound,hit,before⟩ := least_bounded_hit (P:=fun i => 256≤f i) 255 high
  have rp : 0<r := by
    rcases Nat.eq_zero_or_pos r with h|h
    · rw [h] at hit; omega
    · exact h
  have pick : ∃ α β c, α<r ∧ r≤β ∧ Bridge m α β 256 c ∧ (α=0 → β=1) ∧
      (α=1 → β=16) ∧ 0<f α := by
    by_cases atOne : r≤1
    · have r1 : r=1 := by omega
      rw [r1] at hit
      have pos : 0<f 0 := by
        apply Nat.pos_of_ne_zero
        intro x
        have eqv := first_two_cut tables (by omega : 256≤m) (by decide : 0<256) x hit
        omega
      let c := 2^256-3
      have sig : signature m c=0 := signature_lift (by omega : 1≤m) (by decide : signature 1 (2^256-3)<1)
      have f0 : act tables m c 0=1 := by
        apply act_of_lower_entry tables (by omega)
        exact ((tables 2).mul_one c).trans (by decide : (2^256-3+1)%4=2)
      have f1 := act_of_lower_entry tables (a:=c) (x:=1) (k:=256) (by omega : 256+1≤m)
        (row_minus_three_at_two tables 256 (by decide))
      exact ⟨0,1,c,rp,atOne,⟨sig,f0,f1⟩,fun _ => rfl,by omega,pos⟩
    by_cases atSixteen : r≤16
    · have sig : signature m 65534=1 := signature_lift (by omega : 2≤m) (by decide : signature 2 65534<2)
      have step (i : Nat) (b : i<17) : act tables m 65534 i=i*16 := hom.action room b
      exact ⟨1,16,65534,by omega,atSixteen,⟨sig,step 1 (by decide),step 16 (by decide)⟩,
        by omega,fun _ => rfl,le_act tables m a 1 (by omega)⟩
    · obtain ⟨α,β,c,begin,left,right,shape⟩ := wide_bridges room hom four (by omega) (by omega : r<256)
      have leq := le_act tables m a α (by omega)
      exact ⟨α,β,c,left,right,shape,by omega,by omega,Nat.lt_of_lt_of_le (by omega) leq⟩
  obtain ⟨α,β,c,l,u,⟨s,w,v⟩,base,first,pos⟩ := pick
  exact ⟨α,β,c,s,w,v,base,first,pos,Nat.lt_of_not_ge (before α l),Nat.le_trans hit (act_mono tables m a u)⟩

#print axioms cross_256

def UpperBridges (F : BinaryFamily) (m n : Nat) : Prop := ∀ r, 1<r → r<n →
  ∃ α β row, 1≤α ∧ α<r ∧ r≤β ∧ signature m row=α ∧ act F m row α=β ∧ act F m row β=n

theorem upper_bridges_16 {m : Nat} (room : 20≤m) (four : act tables m 14 4=16) : UpperBridges tables m 16 := by
  intro r lo hi
  by_cases early : r≤4
  · have sig : signature m 14=1 := signature_lift (by omega : 2≤m) (by decide : signature 2 14<2)
    have first := act_from_low tables m 14 1 _ 4 (by omega) (LowProducts.v14_2 _) (by decide) (by decide)
    exact ⟨1,4,14,Nat.le_refl _,lo,early,sig,first,four⟩
  · obtain ⟨α,β,c,amin,left,right,h⟩ := bridges_above_four room (Nat.lt_of_not_ge early) hi four
    exact ⟨α,β,c,by omega,left,right,h⟩

theorem upper_bridges_256 {m : Nat} (room : 272≤m) (hom : SixteenRowData)
    (four : act tables m 14 4=16) : UpperBridges tables m 256 := by
  intro r lo hi
  by_cases early : r≤16
  · have sig : signature m 65534=1 := signature_lift (by omega : 2≤m) (by decide : signature 2 65534<2)
    have step (i : Nat) (b : i<17) : act tables m 65534 i=i*16 := hom.action room b
    exact ⟨1,16,65534,Nat.le_refl _,lo,early,sig,step 1 (by decide),step 16 (by decide)⟩
  · obtain ⟨α,β,c,amin,left,right,h⟩ := wide_bridges room hom four (Nat.lt_of_not_ge early) hi
    exact ⟨α,β,c,by omega,left,right,h⟩
end Gamma11
