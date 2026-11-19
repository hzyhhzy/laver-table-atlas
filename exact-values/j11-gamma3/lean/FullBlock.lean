import SixteenCrossing

/-! Appendix A.2 at width sixteen and the full interval of one-bits in
B.3. Finite row growth suffices to carry the full block to a nonzero
product and prevents any critical image from lying inside the block. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

def FullBitBlock (a p n : Nat) : Prop := 2^n-2^p ≤ a%2^n

theorem full_block_inherited (F : BinaryFamily) {m p n a b : Nat} (nm : n≤m)
    (full : FullBitBlock a p n) (nz : (F m).mul a b % 2^n ≠ 0) : FullBitBlock ((F m).mul a b) p n :=
  Nat.le_trans full (Nat.le_of_lt (left_residue_lt F nm nz))

theorem full_block_jump (F : BinaryFamily) {m p n a x : Nat} (pn : p≤n) (nm : n≤m)
    (full : FullBitBlock a p n) (reach : p ≤ act F m a x) : n ≤ act F m a x := by
  let y := (F m).mul a (2^x)
  change p ≤ signature m y at reach
  change n ≤ signature m y
  apply (le_signature m y n nm).mpr
  by_cases zero : y%2^n=0
  · exact zero
  have gt := left_residue_lt F nm zero
  change a % 2^n < y%2^n at gt
  have even := (le_signature m y p (Nat.le_trans pn nm)).mp reach
  have dvd := Nat.pow_dvd_pow 2 pn
  have ydiv : 2^p ∣ y%2^n := Nat.dvd_of_mod_eq_zero ((Nat.mod_mod_of_dvd y dvd).trans even)
  have left := Nat.dvd_sub dvd ydiv
  have diff := Nat.sub_pos_of_lt (Nat.mod_lt y (Nat.two_pow_pos n))
  have width := Nat.le_of_dvd diff left
  unfold FullBitBlock at full
  omega

private theorem first_at {P : Nat → Prop} (n : Nat) (h : P n) :
    ∃ r, r≤n ∧ P r ∧ ∀ i, i<r → ¬ P i := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases earlier : ∃ s, s<n ∧ P s
    · obtain ⟨s,sn,found⟩ := earlier
      obtain ⟨r,rs,hit,least⟩ := ih s sn found
      exact ⟨r,Nat.le_trans rs (Nat.le_of_lt sn),hit,least⟩
    · exact ⟨n,Nat.le_refl _,h,fun i lt pi => earlier ⟨i,lt,pi⟩⟩

/-- A selected bridge has a positive first image below 16 and a second
image at least 16. Its application strictly increases the nonzero low
row and still has an even low row. -/
theorem cross_sixteen {m a : Nat} (room : 20 ≤ m) (pos : 0<a%2^16) (inside : a%2^16≤65533)
    (four : act tables m 14 4=16) :
    ∃ α β c, SixteenBridge m α β c ∧ (α=0 → β=1) ∧ (α=1 → β=4) ∧
      0 < act tables m a α ∧ act tables m a α < 16 ∧
      16 ≤ act tables m a β ∧ a%2^16 < (tables m).mul a c % 2^16 ∧
      (tables m).mul a c % 2^16 ≤ 65534 := by
  let f := act tables m a
  have beginSmall : f 0<16 := by
    apply Nat.lt_of_not_ge
    intro high
    have z := (le_act_iff tables m a 0 16 (by omega)).mp high
    change (tables 16).mul a 1=0 at z
    rw [← (tables 16).mul_mod_left a,(tables 16).mul_one,Nat.mod_eq_of_lt (by omega : a%2^16+1<2^16)] at z
    omega
  have endHigh : 16 ≤ f 15 := by
    apply Nat.le_of_not_gt
    intro low
    have visible : f 15<m := Nat.lt_trans low (by omega)
    have dist := act_distance tables m a (show 0≤15 by decide) visible
    change f 0+(15-0) ≤ f 15 at dist
    have eq0 : f 0=0 := by omega
    have eq15 : f 15=15 := by omega
    have bound := consecutive_residue_lt tables (show 0≤15 by decide) visible
      (show f 15=f 0+(15-0) by omega)
    change a % 2^(f 15+1) < 2^(f 0) at bound
    rw [eq15,eq0] at bound; omega
  obtain ⟨r,short,hit,before⟩ := first_at (P:=fun t => 16≤f t) 15 endHigh
  have rp : 0<r := by
    rcases Nat.eq_zero_or_pos r with z|h
    · rw [z] at hit; omega
    · exact h
  have pick : ∃ α β c, α<r ∧ r≤β ∧ SixteenBridge m α β c ∧ (α=0 → β=1) ∧ (α=1 → β=4) ∧ 0<f α := by
    by_cases first : r≤1
    · have e : r=1 := by omega
      rw [e] at hit
      have positive : 0 < f 0 := by
        apply Nat.pos_of_ne_zero
        intro zero
        have eqv := first_two_cut tables (by omega : 16≤m) (by decide : 0<16) zero hit
        omega
      have sig : signature m 65533=0 := signature_lift (by omega : 1≤m) (by decide : signature 1 65533<1)
      have next : act tables m 65533 0=1 := by
        apply act_of_lower_entry tables (by omega)
        change (tables 2).mul 65533 1=2
        rw [(tables 2).mul_one]
      have endv := act_of_lower_entry tables (a:=2^16-3) (x:=1) (k:=16)
        (by omega : 16+1≤m) (row_minus_three_at_two tables 16 (by decide))
      exact ⟨0,1,65533,rp,first,⟨sig,next,endv⟩,fun _ => rfl,by omega,positive⟩
    by_cases second : r≤4
    · have sig : signature m 14=1 := (signature_lift (by omega : 2≤m) (by decide : signature 2 14<2))
      have one := act_from_low tables m 14 1 _ 4 (by omega) (LowProducts.v14_2 _) (by decide) (by decide)
      exact ⟨1,4,14,by omega,second,⟨sig,one,four⟩,by omega,fun _ => rfl,le_act tables m a 1 (by omega)⟩
    · obtain ⟨α,β,c,start,lt,leq,tr⟩ := bridges_above_four (r:=r) room (by omega) (by omega) four
      exact ⟨α,β,c,lt,leq,tr,by omega,by omega,
        Nat.lt_of_lt_of_le (show 0<α by omega) (le_act tables m a α (by omega))⟩
  obtain ⟨α,β,c,lt,leq,tr,b0,b1,pα⟩ := pick
  have small : f α<16 := Nat.lt_of_not_ge (before α lt)
  have next := Nat.le_trans hit (act_mono tables m a leq)
  let y := (tables m).mul a c
  have sig : signature m y=f α := (signature_mul tables m a c).trans (congrArg f tr.1)
  have nz : y%2^16≠0 := fun z => (Nat.not_le_of_gt small) (sig ▸ (le_signature m y 16 (by omega)).mpr z)
  have even := (le_signature m y 1 (by omega)).mp (show 1≤signature m y by omega)
  have rem : (y%2^16)%2=0 := (Nat.mod_mod_of_dvd y (by decide : 2 ∣ 2^16)).trans even
  have bound := Nat.mod_lt y (Nat.two_pow_pos 16)
  exact ⟨α,β,c,tr,b0,b1,pα,small,next,left_residue_lt tables (by omega) nz,by change y%2^16≤65534; omega⟩

#print axioms full_block_jump
#print axioms cross_sixteen

private theorem signature_at_sixteen {m a z : Nat} (nm : 16≤m) (eqv : a%2^16=z)
    (fit : z<2^16) {s : Nat} (value : signature 16 z=s) (visible : s<16) : signature m a=s := by
  have hz : signature 16 a=s := (signature_mod_eq (eqv.trans (Nat.mod_eq_of_lt fit).symm)).trans value
  exact (signature_lift nm (hz ▸ visible)).trans hz

/-- The downward induction in B.3 on the sixteen-bit residue. Its two
exceptional leaves ask about the first jump of a row of critical point 4
and about the fourth image of a row fixing 1. -/
theorem saturated_full_rows {m : Nat} (room : 256≤m) (four : act tables m 14 4=16)
    (atFour : ∀ k, signature m k=4 → 256 ≤ act tables m k 4 → act tables m k 256=m)
    (fixOne : ∀ k, FullBitBlock k 16 256 → act tables m k 1=1 → 256 ≤ act tables m k 4 →
      k%2^16≠65520 → m-1 ≤ act tables m k 4)
    (a : Nat) (full : FullBitBlock a 16 256) (lo : 0<a%2^16) (hi : a%2^16≤65532)
    (different : a%2^16≠65520) : act tables m a 16=m := by
  obtain ⟨α,β,c,tr,b0,b1,positive,small,medium,inc,bound⟩ :=
    cross_sixteen (by omega) lo (by omega) four
  let y := (tables m).mul a c
  let f := act tables m a
  have high : 256≤f β := full_block_jump tables (by decide) room full medium
  have sig : signature m y=f α := (signature_mul tables m a c).trans (congrArg f tr.1)
  have first := act_application tables m a c α
  have last := act_application tables m a c β
  change act tables m y (f α)=f (act tables m c α) at first
  change act tables m y (f β)=f (act tables m c β) at last
  rw [tr.2.1] at first
  rw [tr.2.2] at last
  change a%2^16 < y%2^16 at inc
  change y%2^16 ≤ 65534 at bound
  have moved (n : Nat) (good : n≤f β) (sat : act tables m y n=m) : f 16=m := by
    have h := act_mono tables m y good
    rw [sat,last] at h
    exact Nat.le_antisymm (act_le ..) h
  by_cases base : y%2^16=65520
  · have sy : signature m y=4 := signature_at_sixteen (by omega) base (by decide) (by decide) (by decide)
    have q : f α=4 := sig.symm.trans sy
    rw [q] at first
    exact moved _ high (atFour _ sy (first.symm ▸ high))
  by_cases endRow : y%2^16=65534
  · have sy : signature m y=1 := signature_at_sixteen (by omega) endRow (by decide) (by decide) (by decide)
    have q : f α=1 := sig.symm.trans sy
    have below : α<m := by
      apply Nat.lt_of_not_ge
      intro h
      have cap := Nat.le_trans (le_act tables m a m (Nat.le_refl _)) (act_mono tables m a h)
      change m≤f α at cap; omega
    have αle : α ≤ 1 := q ▸ le_act tables m a α (Nat.le_of_lt below)
    rcases (show α=0 ∨ α=1 by omega) with e|e
    · rw [b0 e] at high
      rw [e] at q
      have impossible := first_two_cut tables (by omega : 16≤m) (by decide : 1<16) q (by change 16≤f 1; omega)
      omega
    · have eqb := b1 e
      rw [e] at q
      have far := fixOne a full q (eqb ▸ high) different
      rw [← eqb] at far
      change m-1 ≤ f β at far
      rw [e,q] at first
      apply Nat.le_antisymm (act_le ..)
      apply Nat.le_of_not_gt
      intro vis
      change f 16<m at vis
      have strict := act_strict_below_cap tables m y 1 (f β) (by omega) (last.symm ▸ vis)
      rw [first,last] at strict
      omega
  have valid : y%2^16≤65532 := by
    have even := (le_signature m y 1 (by omega)).mp (sig.symm ▸ positive)
    have rem : (y%2^16)%2=0 := (Nat.mod_mod_of_dvd y (by decide : 2 ∣ 2^16)).trans even
    omega
  have nonzero : y%2^256≠0 := by
    intro zero
    have h := (le_signature m y 256 room).mpr zero
    omega
  have inherited := full_block_inherited tables room full nonzero
  exact moved 16 (by omega)
    (saturated_full_rows room four atFour fixOne y inherited (by omega) valid base)
termination_by 65533 - a%2^16
decreasing_by omega

#print axioms saturated_full_rows
end Gamma11
