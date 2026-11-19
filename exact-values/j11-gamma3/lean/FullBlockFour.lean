import FullBlock

/-! The exceptional fourth-image estimate in Appendix B.3. All actions
are capped finite-table actions. In particular equality with the cap is
handled before applying an estimate that requires a visible image. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private def SmallCritical (m : Nat) : Prop := ∀ r a, 4≤r → r<16 →
  signature m a=r → 256 ≤ act tables m a r → act tables m a 256=m

private theorem keep_full {m a b : Nat} (room : 256≤m) (full : FullBitBlock a 16 256)
    (small : signature m ((tables m).mul a b)<256) : FullBitBlock ((tables m).mul a b) 16 256 :=
  full_block_inherited tables room full (fun z => (Nat.not_le_of_gt small) ((le_signature _ _ _ room).mpr z))

private theorem gen012 {m : Nat} (room : 256≤m) :
    act tables m 1 0=1 ∧ act tables m 1 1=2 ∧ act tables m 1 2=4 :=
  ⟨act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v1_1 _) (by decide) (by decide),
   act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v1_2 _) (by decide) (by decide),
   act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v1_4 _) (by decide) (by decide)⟩

private theorem three012 {m : Nat} (room : 256≤m) :
    act tables m 3 0=2 ∧ act tables m 3 1=3 ∧ act tables m 3 2=4 :=
  ⟨act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v3_1 _) (by decide) (by decide),
   act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v3_2 _) (by decide) (by decide),
   act_from_low tables _ _ _ _ _ (by omega) (LowProducts.v3_4 _) (by decide) (by decide)⟩

private theorem start_one {m c b : Nat} (room : 256≤m) (scale : m-1≤256^256) (guard : SmallCritical m)
    (full : FullBitBlock c 16 256) (zero : act tables m c 0=1) (one : act tables m c 1=b)
    (four : 4≤b) : m-1 ≤ act tables m c b := by
  by_cases high : 256≤b
  · apply Nat.le_trans _ (act_mono tables m c high)
    by_cases vis : act tables m c 256<m
    · have h := exponential_growth tables m c 256 zero vis
      rw [one] at h
      exact Nat.le_trans scale (Nat.le_trans (Nat.pow_le_pow_left high 256) h)
    · omega
  have below : b<16 := by
    apply Nat.lt_of_not_ge; intro reached
    exact high (one ▸ full_block_jump tables (by decide) room full (one.symm ▸ reached))
  have c2 : 16≤act tables m c 2 := by
    by_cases vis : act tables m c 2<m
    · have h := exponential_growth tables m c 2 zero vis
      rw [one] at h
      exact Nat.le_trans (Nat.pow_le_pow_left four 2) h
    · omega
  have large := full_block_jump tables (by decide) room full c2
  let h := (tables m).mul c 2
  have sig : signature m h=b := by
    have s : signature m 2=1 := dyadic_tail_signature m 2 1 (by decide) (by omega)
    exact (signature_mul tables m c 2).trans (s ▸ one)
  have read1 := act_application tables m c 2 1
  have read2 := act_application tables m c 2 2
  have b1 := act_from_low tables m 2 1 _ 2 (by omega) (LowProducts.v2_2 _) (by decide) (by decide)
  have b2 := act_from_low tables m 2 2 _ 4 (by omega) (LowProducts.v2_4 _) (by decide) (by decide)
  rw [b1,one] at read1
  rw [b2] at read2
  have endv := guard b h four below sig (read1.symm ▸ large)
  have up := act_mono tables m h large
  change act tables m h (act tables m c 2) = act tables m c 4 at read2
  rw [endv,read2] at up
  exact Nat.le_trans (Nat.sub_le m 1) (Nat.le_trans up (act_mono tables m c four))

private theorem start_two {m z b : Nat} (room : 256≤m) (scale : m-1≤256^256) (guard : SmallCritical m)
    (full : FullBitBlock z 16 256) (zero : act tables m z 0=2) (one : act tables m z 1=b)
    (four : 4≤b) : m-1 ≤ act tables m z 2 := by
  let s := (tables m).mul z 1
  let t := (tables m).mul s 1
  obtain ⟨j0,j1,j2⟩ := gen012 room
  have sig : signature m s=2 := zero
  have s0 := fixes_below_signature tables m s 0 (by omega)
  have s1 := fixes_below_signature tables m s 1 (by omega)
  have sf : FullBitBlock s 16 256 := keep_full room full (by change signature m s<256; omega)
  have tf : FullBitBlock t 16 256 := keep_full room sf (by change act tables m s 0<256; omega)
  have s2 := act_application tables m z 1 0
  rw [zero,j0,one] at s2
  have sb := act_application tables m z 1 1
  rw [j1,one] at sb
  have t0 := act_application tables m s 1 0
  rw [s0,j0,s1] at t0
  have t1 := act_application tables m s 1 1
  change act tables m s 2=b at s2
  rw [s1,j1,s2] at t1
  have tb := act_application tables m s 1 2
  rw [s2,j2] at tb
  have lower := start_one room scale guard tf t0 t1 four
  exact Nat.le_trans lower (Nat.le_trans (Nat.le_of_eq tb) (Nat.le_trans (act_mono tables m s four) (Nat.le_of_eq sb)))

private theorem at_three {m k : Nat} (room : 256≤m) (scale : m-1≤256^256) (guard : SmallCritical m)
    (full : FullBitBlock k 16 256) (crit : signature m k=3) : m-1 ≤ act tables m k 4 := by
  let a := (tables m).mul k 3
  have fixed {x : Nat} (lt : x<3) := fixes_below_signature tables m k x (crit ▸ lt)
  have k3 := act_gt_input tables m k 3 (Nat.le_of_eq crit) (by omega)
  obtain ⟨g0,g1,g2⟩ := three012 room
  have sg : signature m 3=0 := signature_lift (by omega : 1≤m) (by decide : signature 1 3<1)
  have sig : signature m ((tables m).mul k 3)=0 := by
    rw [signature_mul,sg,fixed (by decide : 0<3)]
  have f := keep_full room full (by rw [sig]; decide)
  have a0 := act_application tables m k 3 0
  have a1 := act_application tables m k 3 1
  have a2 := act_application tables m k 3 2
  rw [fixed (by decide : 0<3),g0,fixed (by decide : 2<3)] at a0
  rw [fixed (by decide : 1<3),g1] at a1
  rw [fixed (by decide : 2<3),g2] at a2
  exact Nat.le_trans (start_two room scale guard f a0 a1 k3) (Nat.le_of_eq a2)

private theorem fixes_one_bound {m k : Nat} (room : 256≤m) (scale : m-1≤256^256) (guard : SmallCritical m)
    (full : FullBitBlock k 16 256) (one : act tables m k 1=1) (high : 256≤act tables m k 4)
    (different : k%2^16≠65520) : m-1≤act tables m k 4 := by
  let s := signature m k
  have lo : 2≤s := by
    apply Nat.le_of_not_gt; intro small
    have h := act_gt_input tables m k 1 (by change s≤1; omega) (by omega)
    omega
  have hi : s≤4 := by
    apply Nat.le_of_not_gt; intro above
    have h := fixes_below_signature tables m k 4 above
    omega
  have notFour : s≠4 := by
    intro eqv
    exact different (first_moved_low tables eqv (by decide : 4<16) (by omega) (by omega))
  rcases (show s=2 ∨ s=3 by omega) with eqv|eqv
  · let b := act tables m k 2
    have kb := act_gt_input tables m k 2 (Nat.le_of_eq eqv) (by omega)
    have k0 := fixes_below_signature tables m k 0 (by change 0<s; omega)
    by_cases big : 4≤b
    · let c := (tables m).mul k 1
      obtain ⟨j0,j1,j2⟩ := gen012 room
      have f : FullBitBlock c 16 256 := keep_full room full (by change act tables m k 0<256; omega)
      have c0 := act_application tables m k 1 0
      have c1 := act_application tables m k 1 1
      have cb := act_application tables m k 1 2
      rw [k0,j0,one] at c0
      rw [one,j1] at c1
      rw [j2] at cb
      exact Nat.le_trans (start_one room scale guard f c0 c1 big) (Nat.le_of_eq cb)
    · have b3 : act tables m k 2=3 := by change ¬ 4≤act tables m k 2 at big; omega
      have k3 := act_gt_input tables m k 3 (by change s≤3; omega) (by omega)
      let a := (tables m).mul k 3
      let h := (tables m).mul a 1
      obtain ⟨g0,g1,g2⟩ := three012 room
      have sg : signature m 3=0 := signature_lift (by omega : 1≤m) (by decide : signature 1 3<1)
      have sig : signature m ((tables m).mul k 3)=0 := by rw [signature_mul,sg,k0]
      have fa : FullBitBlock a 16 256 := keep_full room full (by rw [sig]; decide)
      have a0 := act_application tables m k 3 0
      have a1 := act_application tables m k 3 1
      have a3 := act_application tables m k 3 2
      rw [k0,g0,b3] at a0
      rw [one,g1] at a1
      rw [b3,g2] at a3
      have hs : signature m h=3 := a0
      have fh : FullBitBlock h 16 256 := keep_full room fa (by change signature m h<256; omega)
      have mid := act_application tables m a 1 1
      rw [(gen012 room).2.1] at mid
      have a1hi : 4≤act tables m a 1 := a1.symm ▸ k3
      have up := Nat.le_trans (at_three room scale guard fh hs) (act_mono tables m h a1hi)
      exact Nat.le_trans up (Nat.le_trans (Nat.le_of_eq mid)
        (Nat.le_trans (act_mono tables m a (by decide : 2≤3)) (Nat.le_of_eq a3)))
  · exact at_three room scale guard full eqv

theorem full_sixteen_periods {m : Nat} (room : 256≤m) (scale : m-1≤256^256)
    (four : act tables m 14 4=16)
    (atFour : ∀ k, signature m k=4 → 256≤act tables m k 4 → act tables m k 256=m)
    (a : Nat) (full : FullBitBlock a 16 256) (lo : 0<a%2^16) (hi : a%2^16≤65532)
    (different : a%2^16≠65520) : act tables m a 16=m := by
  have guard : SmallCritical m := critical_four_to_fifteen (by omega) (by decide) four atFour
  exact saturated_full_rows room four atFour (fun _ => fixes_one_bound room scale guard) a full lo hi different

#print axioms full_sixteen_periods

/-- The full addition prefix in B.3. All 65,519 intermediate period
tests are consequences of the preceding descending induction. -/
theorem full_sixteen_prefix {m e : Nat} (room : 256≤m) (scale : m-1≤256^256)
    (four : act tables m 14 4=16)
    (atFour : ∀ k, signature m k=4 → 256≤act tables m k 4 → act tables m k 256=m)
    (fit : e<2^m) (crit : signature m e=16) (jump : 256≤act tables m e 16) :
    ∀ i, i<65520 → (tables m).mul e (i+1)=e+(i+1) := by
  have word := first_moved_low tables crit (by decide : 16<256) room jump
  have d : 2^16 ∣ e := Nat.dvd_of_mod_eq_zero ((le_signature m e 16 (by omega)).mp (Nat.le_of_eq crit.symm))
  have dn : 2^16 ∣ 2^m := Nat.pow_dvd_pow 2 (by omega)
  have bound (i : Nat) (hi : i<65536) : e+i<2^m := by
    have gap : 2^16 ≤ 2^m-e := Nat.le_of_dvd (Nat.sub_pos_of_lt fit) (Nat.dvd_sub dn d)
    omega
  have low (i : Nat) (hi : i<65536) : (e+i)%2^16=i := by
    rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd d,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hi]
  have full (i : Nat) (hi : i<65536) : FullBitBlock (e+i) 16 256 := by
    unfold FullBitBlock
    rw [Nat.add_mod,word,Nat.mod_eq_of_lt (by omega : i<2^256),
      Nat.mod_eq_of_lt (by omega : 2^256-2^16+i<2^256)]
    exact Nat.le_add_right ..
  have zero (i : Nat) (hp : 0<i) (hi : i<65520) : (tables m).mul (e+i) (2^16)=0 := by
    have val := low i (by omega)
    have sat := full_sixteen_periods room scale four atFour (e+i) (full i (by omega))
      (val.symm ▸ hp) (by omega) (by omega)
    exact (le_act_iff tables m (e+i) 16 m (Nat.le_refl _)).mp (Nat.le_of_eq sat.symm)
  intro i
  induction i with
  | zero => intro _; exact ((tables m).mul_one e).trans (Nat.mod_eq_of_lt (bound 1 (by decide)))
  | succ i ih =>
    intro hi
    rw [(tables m).row_recurrence e (i+1),ih (by omega),
      (tables m).reduce_period (zero (i+1) (by omega) hi) (e+1),low 1 (by decide),
      (tables m).mul_one,Nat.add_assoc,Nat.mod_eq_of_lt (bound _ (by omega))]

#print axioms full_sixteen_prefix
end Gamma11
