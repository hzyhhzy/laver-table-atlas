import MixedDigits
import FourthJump

/-! The high aligned rows and the critical-2/3 branch of the
mixed-block induction in Appendix D.2. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

def MixedAt (m h : Nat) : Prop := ∀ a, Incomplete16 a → 1≤a%65536 → a%65536≤65534 →
  h≤act tables m a 16

private theorem add_at_cut {m A : Nat} (aligned : 2^16 ∣ A)
    (sat : ∀ i, 1≤i → i≤65534 → act tables m (A+i) 16=m) (j : Nat) (lo : 1≤j) (top : j≤65535) :
    (tables m).mul A j=(A+j)%2^m := by
  have first : (A+1)%2^16=1 := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd aligned,Nat.zero_add,Nat.mod_mod]
  cases j with
  | zero => omega
  | succ i =>
    induction i with
    | zero => exact (tables m).mul_one A
    | succ i ih =>
      have zero := (le_act_iff tables m (A+(i+1)) 16 m (Nat.le_refl _)).mp
        (Nat.le_of_eq (sat (i+1) (by omega) (by omega)).symm)
      rw [(tables m).row_recurrence A (i+1),ih (by omega) (by omega),(tables m).mul_mod_left,
        (tables m).reduce_period zero (A+1),first,(tables m).mul_one,Nat.add_assoc]

private theorem residue_plus {A : Nat} (div : 2^16 ∣ A) {i : Nat} (small : i<65536) :
    (A+i)%65536=i := by
  have h := (aligned_add_residue (Nat.le_refl 16) div small).1
  rw [Nat.mod_eq_zero_of_dvd div,Nat.zero_add] at h
  exact h

private theorem dense_terminal_16 {m a : Nat} (room : 272≤m) (four : act tables m 14 4=16)
    (guard : ∀ r z, 16≤r → r<256 → signature m z=r → 256≤act tables m z r → act tables m z 256=m)
    (mixed : Incomplete16 a) (word : a%65536=65534) : act tables m a 16=m := by
  obtain ⟨sig,early⟩ := first_move_from_run tables (by decide : 1<16) (by omega : 16≤m) word
  have small : act tables m a 1<256 := by
    apply Nat.lt_of_not_ge; intro big
    have full := first_moved_low tables sig (by decide : 1<256) (by omega : 256≤m) big
    exact mixed.2 (show FullBitBlock a 16 256 by unfold FullBitBlock; rw [full]; decide)
  have read := dense_terminal tables (by decide : 2≤16) (by omega : 16*16≤m)
    (upper_bridges_16 (by omega) four) (fun r z lo hi s j => Nat.le_of_eq (guard r z lo hi s j).symm)
    word small mixed.1
  exact Nat.le_antisymm (act_le ..) read

private theorem aligned_high_16 {m A : Nat} (room : 272≤m) (native : NativePeriods16)
    (hom : SixteenRowData) (four : act tables m 14 4=16)
    (guard : ∀ r z, 16≤r → r<256 → signature m z=r → 256≤act tables m z r → act tables m z 256=m)
    (div : 2^16 ∣ A) (mixed : Incomplete16 A) : act tables m A 256=m := by
  let z := (tables m).mul A 65534
  have source := add_at_cut (m:=256) div (fun j lo hi => by
    have small := residue_plus div (by omega : j<65536)
    exact native (A+j) (by rw [small]; exact lo) (by rw [small]; exact hi)) 65534 (by decide) (by decide)
  have rep : z%2^256=(A+65534)%2^256 :=
    ((tables m).projection (tables 256) (Nat.pow_dvd_pow 2 (by omega : 256≤m)) A 65534).trans source
  have mz := (mixed_congr_256 rep).mpr ((mixed_aligned_add div (by decide : 65534<65536)).mpr mixed)
  have l := (residue_agree_lower rep (by decide : 16≤256)).trans (residue_plus div (by decide : 65534<65536))
  have reached := dense_terminal_16 room four guard mz l
  have high := act_mono tables m z (le_act tables m A 16 (by omega))
  have last := act_application tables m A 65534 16
  have endv : act tables m 65534 16=256 := hom.action room (by decide)
  rw [endv] at last
  rw [reached,last] at high
  exact Nat.le_antisymm (act_le ..) high

theorem mixed_small_critical {m h a : Nat} (room : 272≤m) (cut : h<m)
    (native : NativePeriods16) (hom : SixteenRowData) (four : act tables m 14 4=16)
    (guard : ∀ r z, 16≤r → r<256 → signature m z=r → 256≤act tables m z r → act tables m z 256=m)
    (prior : MixedAt m h) (mixed : Incomplete16 a) (low : 1≤a%65536)
    (crit : signature m a=2 ∨ signature m a=3) : h+1≤act tables m a 16 := by
  let i := a%65536
  let A := 65536*(a/65536)
  have div : 2^16 ∣ A := Nat.dvd_mul_right ..
  have eqv : A+i=a := Nat.div_add_mod a 65536
  have mi : i<65536 := Nat.mod_lt a (by decide : 0<65536)
  have mixedA := (mixed_aligned_add div mi).mp (eqv ▸ mixed)
  have endA := aligned_high_16 room native hom four guard div mixedA
  have per (j : Nat) (pos : 1≤j) (maxJ : j≤65534) : act tables h (A+j) 16=h := by
    have short : j<65536 := by omega
    have word := residue_plus div short
    have hit := prior (A+j) ((mixed_aligned_add div short).mpr mixedA)
      (by rw [word]; exact pos) (by rw [word]; exact maxJ)
    exact (act_at_smaller_degree tables (Nat.le_of_lt cut) (A+j) 16).trans (Nat.min_eq_left hit)
  have val := add_at_cut div per i low (Nat.le_of_lt_succ (by change i<65536; exact mi))
  rw [eqv] at val
  have compare : congruent m h ((tables m).mul A i) a := by
    unfold congruent; rw [Nat.min_eq_left (Nat.le_of_lt cut),(tables m).projection (tables h) (Nat.pow_dvd_pow 2 (Nat.le_of_lt cut)),val]
  have sig := signature_agree_below (a:=a) (b:=i) (r:=16) (by omega : 16≤m)
    (show a%2^16=i%2^16 from (Nat.mod_eq_of_lt mi).symm) (by omega)
  have small := unspecialized_fourth_image (k:=i) (by omega : 256≤m) (by rw [← sig]; exact crit)
  have critical := (le_signature m A 16 (by omega)).mpr (Nat.mod_eq_zero_of_dvd div)
  have f4 := fixes_below_signature tables m A 4 (by omega)
  have z4 := act_application tables m A i 4
  rw [f4] at z4
  have force := Nat.le_trans (Nat.le_of_eq endA.symm) (act_mono tables m A small)
  have lower4 := congruent_action_ge tables m compare (x:=4)
    (Nat.le_trans (Nat.le_of_lt cut) (Nat.le_trans force (Nat.le_of_eq z4.symm)))
  by_cases visible : act tables m a 16<m
  · have dist := act_distance tables m a (by decide : 4≤16) visible; omega
  · omega

#print axioms mixed_small_critical

private theorem sig_at_low {m a k s : Nat} (room : 16≤m) (low : a%65536=k)
    (fit : k<65536) (value : signature 16 k=s) (visible : s<16) : signature m a=s := by
  have sig := (signature_mod_eq (low.trans (Nat.mod_eq_of_lt fit).symm)).trans value
  exact (signature_lift room (sig ▸ visible)).trans sig

private theorem mixed_step {m h : Nat} (room : 272≤m) (cut : h<m) (scale : m-1≤256^256)
    (native : NativePeriods16) (hom : SixteenRowData) (four : act tables m 14 4=16)
    (atFour : ∀ k, signature m k=4 → 256≤act tables m k 4 → act tables m k 256=m)
    (guard : ∀ r z, 16≤r → r<256 → signature m z=r → 256≤act tables m z r → act tables m z 256=m)
    (prior : MixedAt m h) (a : Nat) (mixed : Incomplete16 a) (low : 1≤a%65536)
    (upper : a%65536≤65534) : h+1≤act tables m a 16 := by
  by_cases last : a%65536=65534
  · exact Nat.le_trans cut (Nat.le_of_eq (dense_terminal_16 room four guard mixed last).symm)
  obtain ⟨α,β,c,br,at0,at1,pos,small,up,increase,endRow⟩ :=
    cross_sixteen (by omega : 20≤m) low (by change a%65536≤65533; omega) four
  let z := (tables m).mul a c
  let f := act tables m a
  have zs : signature m z=f α := (signature_mul tables m a c).trans (congrArg f br.1)
  have z1 := act_application tables m a c α
  have z2 := act_application tables m a c β
  rw [br.2.1] at z1
  rw [br.2.2] at z2
  change act tables m z (f α)=f β at z1
  change act tables m z (f β)=f 16 at z2
  change a%65536<z%65536 at increase
  change z%65536≤65534 at endRow
  change 16≤f β at up
  change 0<f α at pos
  by_cases full : FullBitBlock z 16 256
  · have high' := full_block_jump tables (by decide : 16≤256) (by omega : 256≤m) full (z1.symm ▸ up)
    have high : 256≤f β := z1 ▸ high'
    have done (s : Nat) (leq : s≤f β) (sat : act tables m z s=m) : h+1≤f 16 := by
      have v := act_mono tables m z leq
      rw [sat,z2] at v
      exact Nat.le_trans cut v
    by_cases middle : z%65536=65520
    · have sig := sig_at_low (by omega : 16≤m) middle (by decide) (by decide : signature 16 65520=4) (by decide)
      have eqv := zs.symm.trans sig
      rw [eqv] at z1
      exact done 256 high (atFour z sig (z1.symm ▸ high))
    by_cases exceptional : z%65536=65534
    · have sig := sig_at_low (by omega : 16≤m) exceptional (by decide) (by decide : signature 16 65534=1) (by decide)
      have eqv : f α=1 := zs.symm.trans sig
      have lower : α≤1 := by
        by_cases lt : α≤m
        · exact eqv ▸ le_act tables m a α lt
        · have reach := Nat.le_trans (le_act tables m a m (Nat.le_refl _)) (act_mono tables m a (by omega : m≤α))
          change m≤f α at reach; omega
      rcases (show α=0 ∨ α=1 by omega) with first|second
      · rw [first] at eqv
        rw [at0 first] at high
        have wrong := first_two_cut tables (by omega : 256≤m) (by decide : 1<256) eqv high
        exact False.elim (mixed.2 (show FullBitBlock a 16 256 by unfold FullBitBlock; rw [wrong]; decide))
      · rw [second] at eqv
        rw [at1 second] at high
        have lb : 2≤signature m a := by
          apply Nat.le_of_not_gt; intro below
          have v := act_gt_input tables m a 1 (by omega) (by omega)
          change 1<f 1 at v; omega
        have ub : signature m a≤4 := by
          apply Nat.le_of_not_gt; intro above
          have fix := fixes_below_signature tables m a 4 above
          change f 4=4 at fix; omega
        have exc : signature m a≠4 := by
          intro is4
          have wrong := first_moved_low tables is4 (by decide : 4<256) (by omega : 256≤m) high
          exact mixed.2 (show FullBitBlock a 16 256 by unfold FullBitBlock; rw [wrong]; decide)
        exact mixed_small_critical room cut native hom four guard prior mixed low (by omega)
    have ev := (le_signature m z 1 (by omega)).mp (zs.symm ▸ pos)
    have evenWord : (z%65536)%2=0 := (Nat.mod_mod_of_dvd z (by decide : 2 ∣ 65536)).trans ev
    exact done 16 up (full_sixteen_periods (by omega) scale four atFour z full (by change 0<z%65536; omega)
      (by change z%65536≤65532; omega) middle)
  · have dense := dense16_inherited (by omega : 256≤m) mixed.1 (Nat.ne_of_gt (by change 0<z%65536; omega))
    have result := mixed_step room cut scale native hom four atFour guard prior z ⟨dense,full⟩ (by omega) endRow
    exact Nat.le_trans result (Nat.le_trans (act_mono tables m z up) (Nat.le_of_eq z2))
termination_by 65535-a%65536
decreasing_by omega

theorem mixed_to_cap {m : Nat} (room : 272≤m) (scale : m-1≤256^256)
    (native : NativePeriods16) (hom : SixteenRowData) (four : act tables m 14 4=16)
    (atFour : ∀ k, signature m k=4 → 256≤act tables m k 4 → act tables m k 256=m)
    (guard : ∀ r z, 16≤r → r<256 → signature m z=r → 256≤act tables m z r → act tables m z 256=m) :
    MixedAt m m := by
  suffices all : ∀ h, 256≤h → h≤m → MixedAt m h from all m (by omega) (Nat.le_refl _)
  intro h
  induction h with
  | zero => intro impossible; omega
  | succ h ih =>
    intro lo bound
    by_cases first : h+1=256
    · intro a _ pos upper
      have old := native a pos upper
      have pr := act_at_smaller_degree tables (by omega : 256≤m) a 16
      have reach := Nat.le_trans (Nat.le_of_eq (old.symm.trans pr)) (Nat.min_le_right ..)
      exact first ▸ reach
    · have pri := ih (by omega) (by omega)
      exact mixed_step room bound scale native hom four atFour guard pri

#print axioms mixed_to_cap
end Gamma11
