import FullBlockFour
import ShortPeriod

/-! The transfer used at critical position 16 in Appendix C. We can
choose a single representative t = 2^256 - 13 for every period of p:
the earlier estimate already shows that the period divides 2^256. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem periodic_arguments (F : BinaryFamily) {m a k x y : Nat}
    (cut : act F m a k=m) (same : x%2^k=y%2^k) : (F m).mul a x=(F m).mul a y := by
  have zero := (le_act_iff F m a k m (Nat.le_refl _)).mp (Nat.le_of_eq cut.symm)
  exact ((F m).reduce_period zero x).trans ((congrArg ((F m).mul a) same).trans
    ((F m).reduce_period zero y).symm)

theorem fixed_test_row {m : Nat} (room : 256≤m) :
    signature m (2^256-13)=0 ∧ act tables m (2^256-13) 0=2 ∧
    act tables m (2^256-13) 1=3 ∧ 256≤act tables m (2^256-13) 2 := by
  let t := 2^256-13
  have sig : signature m t=0 := signature_lift (by omega : 1≤m) (by decide : signature 1 (2^256-13)<1)
  have one : act tables m t 0=2 := by
    apply act_of_lower_entry tables (by omega)
    change (tables 3).mul t 1=4
    exact ((tables 3).mul_one t).trans (by decide : (2^256-13+1)%8=4)
  have two : act tables m t 1=3 := by
    have v := act_from_low tables m 3 1 8 3 (by omega) (LowProducts.v3_2 _) (by decide) (by decide)
    have h : congruent m 4 3 t := by
      unfold congruent; rw [Nat.min_eq_left (by omega : 4≤m)]; decide
    have small : act tables m 3 1<4 := by rw [v]; decide
    exact (congruent_read tables m h small).symm.trans v
  have h4 : 4≤act tables m t 2 := by
    by_cases vis : act tables m t 2<m
    · have h := act_distance tables m t (by decide : 1≤2) vis; omega
    · omega
  exact ⟨sig,one,two,full_block_jump tables (by decide : 4≤256) room
    (show FullBitBlock (2^256-13) 4 256 by unfold FullBitBlock; decide) h4⟩

/-- W=p*t, X=W*W. At period cutoff 256, X fixes the small positions
and sends its first moved position all the way to the ambient cap. -/
theorem constructed_square {m p : Nat} (room : 65536≤m)
    (start : act tables m p 0=1) (next : 256≤act tables m p 1)
    (cut : act tables m p 256=m) :
    let w := (tables m).mul p (2^256-13)
    let x := (tables m).mul w w
    let c := act tables m p 2
    65536≤c ∧ signature m x=c ∧ act tables m x c=m := by
  let t := 2^256-13
  let w := (tables m).mul p t
  let x := (tables m).mul w w
  let c := act tables m p 2
  obtain ⟨ts,t0,_,t2⟩ := fixed_test_row (by omega : 256≤m)
  have wcrit : signature m w=1 := (signature_mul tables m p t).trans (ts ▸ start)
  have w1 : act tables m w 1=c := by
    have h := act_application tables m p t 0
    rw [start,t0] at h; exact h
  have wc : act tables m w c=m := by
    have h := act_application tables m p t 2
    have up := act_mono tables m p t2
    rw [cut] at up
    exact Nat.le_antisymm (act_le ..) (Nat.le_trans up (Nat.le_of_eq h.symm))
  have large : 65536≤c := by
    by_cases vis : c<m
    · have grow := exponential_growth tables m p 2 start vis
      exact Nat.le_trans (Nat.pow_le_pow_left next 2) grow
    · omega
  have xs : signature m x=c := (signature_mul tables m w w).trans (wcrit ▸ w1)
  have xc := act_application tables m w w 1
  rw [w1,wc] at xc
  exact ⟨large,xs,xc⟩

/-- Transport the two small source products through a row already
saturated at 256. This identifies the particular square in the prefix. -/
theorem transport_square {m a : Nat} (room : 256≤m)
    (source : (tables 256).mul 13 3=65534)
    (sourceSq : (tables 256).mul 65534 65534=2^256-2^16)
    (aCut : act tables m a 256=m) (pCut : act tables m ((tables m).mul a 13) 256=m)
    (three : (tables m).mul a 3=a+3) (word : (a+3)%2^256=2^256-13) :
    let w := (tables m).mul ((tables m).mul a 13) (2^256-13)
    (tables m).mul a (2^256-2^16)=(tables m).mul w w := by
  let mul := (tables m).mul
  let p := mul a 13
  let w := mul p (2^256-13)
  have proj (b c : Nat) := (tables m).projection (tables 256) (Nat.pow_dvd_pow 2 room) b c
  have lowL := (proj 13 3).trans source
  have transferL : mul a 65534=mul a (mul 13 3) := periodic_arguments tables aCut
    ((show 65534%2^256=65534 by decide).trans lowL.symm)
  have lw : mul a 65534=w := by
    apply transferL.trans
    apply ((tables m).mul_distrib a 13 3).trans
    rw [three]
    exact periodic_arguments tables pCut (word.trans (Nat.mod_eq_of_lt (by decide : 2^256-13<2^256)).symm)
  have lowV := (proj 65534 65534).trans sourceSq
  have transferV : mul a (2^256-2^16)=mul a (mul 65534 65534) := periodic_arguments tables aCut
    ((show (2^256-2^16)%2^256=2^256-2^16 by decide).trans lowV.symm)
  change mul a (2^256-2^16)=mul w w
  exact transferV.trans (((tables m).mul_distrib a 65534 65534).trans (congrArg (fun z => mul z z) lw))

/-- The second source product is only read at 256. A single stretch
on A_17 suffices here, including its leading zero padding. -/
theorem small_source_square (hom : StretchHomAt 16 17) :
    (tables 256).mul 65534 65534=2^256-2^16 := by
  have h := stretch_row (by decide : 0<16) (by decide : 0<17) hom 65534 (by decide)
  have proj := (tables (17*16)).projection (tables 256) (Nat.pow_dvd_pow 2 (by decide : 256≤17*16)) 65534 65534
  change (tables (17*16)).mul 65534 65534=repeatBits 16 17 65534 at h
  rw [h] at proj
  exact proj.symm.trans (by decide)

#print axioms fixed_test_row
#print axioms constructed_square
#print axioms transport_square
#print axioms small_source_square

/-- A low word which is precisely a run of ones realizes the converse
of the first-moved-position test up to the top of that run. -/
theorem first_move_from_run (F : BinaryFamily) {m a s n : Nat} (sn : s<n) (room : n≤m)
    (word : a%2^n=2^n-2^s) : signature m a=s ∧ n≤act F m a s := by
  have pos := Nat.two_pow_pos s
  have below := Nat.pow_lt_pow_right (by decide : 1<2) sn
  have fit : 2^n-2^s<2^n := by omega
  have sig : signature n a=s := (signature_mod_eq (word.trans (Nat.mod_eq_of_lt fit).symm)).trans
    (dyadic_tail_signature n n s sn (Nat.le_refl _))
  have zero := (square_zero_iff F n (2^n-2^s) fit).mpr (Or.inr ⟨s,sn,rfl⟩)
  have sq := signature_mul F n (2^n-2^s) (2^n-2^s)
  rw [zero, signature_zero,dyadic_tail_signature n n s sn (Nat.le_refl _)] at sq
  have native : act F n a s=n := by
    unfold act
    rw [← (F n).mul_mod_left a,word]
    exact sq.symm
  have pr := act_at_smaller_degree F room a s
  exact ⟨(signature_lift room (sig ▸ sn)).trans sig,Nat.le_trans (Nat.le_of_eq (native.symm.trans pr)) (Nat.min_le_right ..)⟩

private theorem window_add {m e : Nat} (room : 256≤m) (fit : e<2^m)
    (word : e%2^256=2^256-2^16) (i : Nat) (hi : i<65536) :
    e+i<2^m ∧ (e+i)%2^256=2^256-2^16+i := by
  have low := Nat.mod_mod_of_dvd e (show 2^16 ∣ 2^256 from Nat.pow_dvd_pow 2 (by decide))
  rw [word] at low
  have dvd : 2^16 ∣ e := Nat.dvd_of_mod_eq_zero
    (low.symm.trans (by decide : (2^256-2^16)%2^16=0))
  have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt fit) (Nat.dvd_sub (Nat.pow_dvd_pow 2 (show 16≤m by omega)) dvd)
  constructor
  · omega
  · rw [Nat.add_mod, word, Nat.mod_eq_of_lt (by omega : i<2^256),
      Nat.mod_eq_of_lt (by omega : 2^256-2^16+i<2^256)]

private theorem small_add {a : Nat} (word : a%2^256=2^256-16) (i : Nat) (hi : i<16) :
    (a+i)%2^256=2^256-16+i := by
  rw [Nat.add_mod,word,Nat.mod_eq_of_lt (by omega : i<2^256),
    Nat.mod_eq_of_lt (by omega : 2^256-16+i<2^256)]

/-- The two rows a*13 and a+13 need agree only in the lower table.
This retains the true application a*13 in the degree under study. -/
private theorem old_thirteen {t a : Nat} (scale : t=256^256)
    (word : a%2^256=2^256-16) :
    congruent (t+1) t (a+13) ((tables (t+1)).mul a 13) := by
  have room : 256≤t := by rw [scale]; decide
  have power : 2^256≤2^t := Nat.pow_le_pow_right (by decide : 0<2) room
  let lo := a%2^t
  have fit : lo<2^t := Nat.mod_lt _ (Nat.two_pow_pos _)
  have same : lo%2^256=2^256-16 := (Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 room)).trans word
  have low := protected_block_thirteen tables (by omega : 9≤t) (by decide : 5≤256) room
    (Nat.le_of_eq scale) fit same
  have bound : lo+13<2^t := low ▸ (tables t).mul_lt lo 13
  unfold congruent
  rw [Nat.min_eq_left (Nat.le_succ t),(tables (t+1)).projection (tables t) (Nat.pow_dvd_pow 2 (Nat.le_succ t)),
    ← (tables t).mul_mod_left a 13,low,Nat.add_mod, Nat.mod_eq_of_lt (by omega : 13<2^t)]
  exact Nat.mod_eq_of_lt bound

/-- The exceptional thirteenth step. If q sends 4 exactly to or below
the penultimate cap, the exponential equality case and the old table
force c=65536, still below that cap. -/
theorem last_guard {t a x : Nat} (scale : t=256^256) (word : a%2^256=2^256-16)
    (qNext : (tables (t+1)).mul (a+12) 1=a+13)
    (fixFour : act tables (t+1) x 4=4)
    (jumpX : act tables (t+1) x (act tables (t+1) ((tables (t+1)).mul a 13) 2)=t+1) :
    act tables (t+1) ((tables (t+1)).mul x (a+12)) 4=t+1 := by
  let d := t+1
  let q := a+12
  let g := a+13
  let p := (tables d).mul a 13
  have tBig : 65536<t := by rw [scale]; decide
  obtain ⟨qs,q2⟩ := first_move_from_run tables (a:=q) (by decide : 2<256) (by change 256≤t+1; omega)
    ((small_add word 12 (by decide)).trans (by decide))
  change signature d q=2 at qs
  change 256≤act tables d q 2 at q2
  have q0 := fixes_below_signature tables d q 0 (by omega)
  have q1 := fixes_below_signature tables d q 1 (by omega)
  have j0 := act_from_low tables d 1 0 2 1 (by change 9≤t+1; omega) (LowProducts.v1_1 _) (by decide) (by decide)
  have j1 := act_from_low tables d 1 1 12 2 (by change 9≤t+1; omega) (LowProducts.v1_2 _) (by decide) (by decide)
  have j2 := act_from_low tables d 1 2 240 4 (by change 9≤t+1; omega) (LowProducts.v1_4 _) (by decide) (by decide)
  have ev (k : Nat) := act_application tables d q 1 k
  have g0 := ev 0
  have g1 := ev 1
  have g2 := ev 2
  change (tables d).mul q 1=g at qNext
  rw [qNext,q0,j0,q1] at g0
  rw [qNext,q1,j1] at g1
  rw [qNext,j2] at g2
  have move := act_application tables d x q 4
  rw [fixFour] at move
  apply move.trans
  by_cases visible : act tables d q 4<d
  · have link := Nat.le_trans (act_mono tables d g q2) (Nat.le_of_eq g2)
    have gv := Nat.lt_of_le_of_lt link visible
    obtain ⟨_,earlier⟩ := exponential_at_threshold tables scale (by decide : 0<256) g0 (g1.symm ▸ q2) gv
    have small := earlier 2 (by decide)
    have eqv : act tables d g 2=act tables d p 2 := congruent_read tables d (old_thirteen scale word)
      (small ▸ tBig)
    have reached := earlier 256 (Nat.le_refl _)
    have up : act tables d p 2≤act tables d q 4 := by
      rw [← eqv,small]; rw [reached,← scale] at link; omega
    have endv := act_mono tables d x up
    exact Nat.le_antisymm (act_le ..) (jumpX ▸ endv)
  · have z := Nat.le_antisymm (act_le tables d q 4) (Nat.le_of_not_gt visible)
    rw [z]
    exact Nat.le_antisymm (act_le ..) (le_act tables d x d (Nat.le_refl _))

#print axioms first_move_from_run
#print axioms last_guard

/-- A periodic right argument allows a whole finite tail to pass through x.
The result keeps the actual products a*i even on the exceptional last step. -/
private theorem carry_tail {m a e x : Nat}
    (first : (tables m).mul e (65520+1)=(tables m).mul x ((tables m).mul a 1))
    (same : (e+1)%16=(tables m).mul x (a+1)%16)
    (periods : ∀ i, 1≤i → i≤12 → act tables m ((tables m).mul x ((tables m).mul a i)) 4=m) :
    (tables m).mul e 65533=(tables m).mul x ((tables m).mul a 13) := by
  have all (i : Nat) (bound : i≤12) :
      (tables m).mul e (65520+(i+1))=(tables m).mul x ((tables m).mul a (i+1)) := by
    induction i with
    | zero => exact first
    | succ i ih =>
      rw [show 65520+(i+1+1)=65520+(i+1)+1 by omega,(tables m).row_recurrence e,
        ih (by omega),periodic_arguments tables (periods (i+1) (by omega) bound) same,
        ← (tables m).mul_distrib,← (tables m).row_recurrence]
  exact all 12 (Nat.le_refl _)

theorem critical_sixteen {t e : Nat} (scale : t=256^256) (hom : SixteenRowData)
    (source : (tables 256).mul 13 3=65534) (thirteen : act tables (t+1) 13 4≤256)
    (fit : e<2^(t+1)) (crit : signature (t+1) e=16) (jump : 256≤act tables (t+1) e 16)
    (addM : (tables (t+1)).mul e 65520=e+65520) : act tables (t+1) e 256=t+1 := by
  let d := t+1
  let a := e+65520
  let p := (tables d).mul a 13
  let w := (tables d).mul p (2^256-13)
  let x := (tables d).mul w w
  let c := act tables d p 2
  let v := 2^256-2^16
  have room : 65536<t := by rw [scale]; decide
  have nt : 256≤t := by omega
  have inD : 256≤d := by dsimp [d]; omega
  have ov : d≤256^256+1 := by dsimp [d]; omega
  have word := first_moved_low tables crit (by decide : 16<256) inD jump
  have step (i : Nat) (hi : i<65536) := window_add inD fit word i hi
  have sm := step 65520 (by decide)
  have fitA : a<2^d := sm.1
  have wordA : a%2^256=2^256-16 := sm.2.trans (by decide)
  obtain ⟨asig,a4⟩ := first_move_from_run tables (by decide : 4<256) inD wordA
  have fit1 : a+1<2^d := (step (65520+1) (by decide)).1
  have fit13 : a+13<2^d := (step (65520+13) (by decide)).1
  have aCut := critical_four_actor tables (by decide) (by omega) nt scale thirteen asig a4
  have pCut := critical_four_applied tables (by decide) (by omega) nt scale asig a4
  have a0 := fixes_below_signature tables d a 0 (by omega)
  have a1 := fixes_below_signature tables d a 1 (by omega)
  have g0 := act_from_low tables d 13 0 14 1 (by dsimp [d]; omega) (LowProducts.v13_1 _) (by decide) (by decide)
  have g1 := act_from_low tables d 13 1 496 4 (by dsimp [d]; omega) (LowProducts.v13_2 _) (by decide) (by decide)
  have p0 := act_application tables d a 13 0
  have p1 := act_application tables d a 13 1
  rw [a0,g0,a1] at p0
  rw [a1,g1] at p1
  obtain ⟨cb,xs,xc⟩ := constructed_square (by change 65536≤t+1; omega) p0 (p1.symm ▸ a4) pCut
  change 65536≤c at cb
  change signature d x=c at xs
  change act tables d x c=d at xc
  have x2 := fixes_below_signature tables d x 2 (by omega)
  have x4 := fixes_below_signature tables d x 4 (by omega)
  obtain ⟨periods,adds⟩ := protected_block_twelve tables (by dsimp [d]; omega) (by decide : 5≤256) inD ov fitA wordA
  have ax : (tables d).mul a v=x := transport_square inD source hom.square
    aCut pCut (adds 2 (by decide)) ((small_add wordA 3 (by decide)).trans (by decide))
  have ae : (e+1)%2^256=(v+1)%2^256 := (step 1 (by decide)).2.trans (by decide)
  have first : (tables d).mul e (65520+1)=(tables d).mul x ((tables d).mul a 1) := by
    rw [(tables d).row_recurrence e,addM,periodic_arguments tables aCut ae,(tables d).row_recurrence a v,ax,
      (tables d).mul_one a,Nat.mod_eq_of_lt fit1]
  have xlow := congruent_lower (app_critical tables d x (a+1)) (show 4≤signature d x by omega)
  unfold congruent at xlow
  rw [Nat.min_eq_left (by dsimp [d]; omega : 4≤d)] at xlow
  have same : (e+1)%16=(tables d).mul x (a+1)%16 := by
    change (tables d).mul x (a+1)%16=(a+1)%16 at xlow
    rw [xlow]; dsimp [a]; omega
  have qNext : (tables d).mul (a+12) 1=a+13 := ((tables d).mul_one _).trans (Nat.mod_eq_of_lt fit13)
  have last := last_guard scale wordA qNext x4 xc
  have eqv := carry_tail first same (by
    intro i hi ub
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
    rw [adds l (by omega)]
    by_cases endp : l+1=12
    · rw [endp]; exact last
    · have h := act_application tables d x (a+(l+1)) 4
      rw [x4,periods (l+1) hi (by omega)] at h
      exact h.trans (Nat.le_antisymm (act_le ..) (le_act tables d x d (Nat.le_refl _))))
  have end1 : act tables d 65533 1=16 := act_of_lower_entry tables (by dsimp [d]; omega)
    (row_minus_three_at_two tables 16 (by decide))
  have main : act tables d 65534 16=256 := hom.action (by dsimp [d]; omega) (by decide)
  have j1 := act_from_low tables d 1 1 12 2 (by dsimp [d]; omega) (LowProducts.v1_2 _) (by decide) (by decide)
  have ev := act_application tables d 65533 1 1
  have fitL : 65534<2^d := Nat.lt_of_lt_of_le (by decide : 65534<2^256) (Nat.pow_le_pow_right (by decide) inD)
  rw [(tables d).mul_one,Nat.mod_eq_of_lt fitL,end1,main,j1] at ev
  have e2 := fixes_below_signature tables d e 2 (crit ▸ (by decide : 2<16))
  have readE := act_application tables d e 65533 2
  have readX := act_application tables d x p 2
  rw [e2,← ev,eqv] at readE
  rw [x2,xc] at readX
  exact readE.symm.trans readX

#print axioms critical_sixteen
end Gamma11
