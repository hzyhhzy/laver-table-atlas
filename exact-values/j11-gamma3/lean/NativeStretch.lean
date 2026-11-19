import ShiftedPeriods

/-! Construct the native repeated-digit row up to the first new high
bit. Only the ordinary block law and the crossing triples are used. -/
set_option autoImplicit false
set_option exponentiation.threshold 512
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem even_digits (n k y : Nat) (e : y%2=0) :
    2^n ∣ repeatBits n (k+1) y ∧
      repeatBits n (k+1) (y+1)=repeatBits n (k+1) y+(2^n-1) := by
  have odd : (y+1)%2≠0 := by omega
  have half : (y+1)/2=y/2 := by omega
  simp only [repeatBits,if_pos e,if_neg odd,half,Nat.zero_add]
  exact ⟨Nat.dvd_mul_right ..,Nat.add_comm ..⟩

private theorem add_prefix {d n A : Nat} (room : n≤d) (fit : A<2^d) (align : 2^n ∣ A)
    (periodic : ∀ i, 1≤i → i<2^n-1 → act tables d (A+i) n=d) (i : Nat) (limit : i+1<2^n) :
    (tables d).mul A (i+1)=A+(i+1) := by
  have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt fit) (Nat.dvd_sub (Nat.pow_dvd_pow 2 room) align)
  have broad : 1<2^n := by omega
  have one : (A+1)%2^n=1 := by
    rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd align,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt broad]
  induction i with
  | zero => exact ((tables d).mul_one A).trans (Nat.mod_eq_of_lt (by omega))
  | succ i ih =>
    have hit := periodic (i+1) (by omega) (by omega)
    have zero := (le_act_iff tables d (A+(i+1)) n d (Nat.le_refl _)).mp (Nat.le_of_eq hit.symm)
    rw [(tables d).row_recurrence A (i+1),ih (by omega),(tables d).reduce_period zero (A+1),one,
      (tables d).mul_one,Nat.mod_eq_of_lt (by omega : A+(i+1)+1<2^d),Nat.add_assoc]

private theorem guard_one_degree {d n r a : Nat} (deg : d=n*n+1) (last : r<n*n)
    (move : n*n≤act tables d a r) : d≤act tables d a (n*n) := by
  apply Nat.le_of_not_gt; intro visible
  have dist := act_distance tables d a (Nat.le_of_lt last) visible
  omega

theorem native_stretch_prefix (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {n : Nat} (dyadic : IsDyadic n) (width : 2≤n) (bridges : UpperBridges tables (n*n+1) n)
    (i : Nat) (bound : i+1<2^n) :
    (tables (n*n+1)).mul (2^n-2) (i+1)=repeatBits n n (i+1) := by
  let d := n*n+1
  have power := Nat.two_pow_pos n
  have sq : n≤n*n := by have t := Nat.mul_le_mul_left n (show 1≤n by omega); rwa [Nat.mul_one] at t
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have room : n<d := by dsimp [d]; omega
  have size := Nat.pow_lt_pow_right (by decide : 1<2) room
  induction i with
  | zero =>
    rw [(tables _).mul_one,Nat.mod_eq_of_lt (by change 2^n-2+1<2^d; omega),repeatBits_one _ _ (by omega)]
    omega
  | succ i ih =>
    rw [(tables _).row_recurrence _ (i+1),ih (by omega)]
    have right : 2^n-2+1=2^n-1 := by omega
    rw [right]
    by_cases even : (i+1)%2=0
    · let A := repeatBits n n (i+1)
      have data := even_digits n (n-1) (i+1) even
      rw [Nat.sub_add_cancel (by omega : 1≤n)] at data
      obtain ⟨div,next⟩ := data
      have positive : 0<A := repeatBits_pos (by omega) (by omega) (by omega)
      have floor := Nat.le_of_dvd positive div
      have fit : A<2^(n*n) := repeatBits_lt n n _
      have per (j : Nat) (lo : 1≤j) (hi : j<2^n-1) : act tables d (A+j) n=d := by
        have small : j<2^n := by omega
        have low : (A+j)%2^n=j := by
          rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd div,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt small]
        have back := (aligned_add_residue sq div small).1
        rw [Nat.mod_eq_of_lt fit] at back
        have exactWord : (A+j)%2^(0+n)=2^0*j+(2^0-1) := by simpa using low
        have high (_ : 0+n*n<d) : 2^(0+n)≤(A+j)%2^(0+n*n) := by
          simp only [Nat.zero_add]; rw [back]; omega
        apply Nat.le_antisymm (act_le ..)
        exact shifted_period_bound H law width dyadic (Nat.dvd_zero _) (by omega : 0+n≤d) room
          (Nat.le_refl _) (by dsimp [d]; omega) bridges _ j lo (by omega) exactWord high
      have add := add_prefix (d:=d) (Nat.le_of_lt room) (Nat.lt_trans fit (Nat.pow_lt_pow_succ (by decide))) div
        per (2^n-2) (by omega)
      rw [right] at add
      exact add.trans next.symm
    · exact even_stretched_step H law dyadic width (Nat.le_succ _) bridges
        (fun _ _ _ last _ move => guard_one_degree rfl last move) even bound

private theorem upper_bit_row {k b : Nat} (odd : b%2=1) :
    (tables (k+1)).mul (2^k-1) b=2^k := by
  have pos := Nat.two_pow_pos k
  have fit := Nat.pow_lt_pow_succ (n:=k) (by decide : 1<2)
  have size : 2^(k+1)-2^k=2^k := by rw [Nat.pow_succ]; omega
  have square := (square_zero_iff tables (k+1) (2^k) fit).mpr (Or.inr ⟨k,Nat.lt_succ_self _,size.symm⟩)
  have first := (tables (k+1)).mul_one (2^k-1)
  rw [Nat.sub_add_cancel pos,Nat.mod_eq_of_lt fit] at first
  have zero : (tables (k+1)).mul (2^k-1) 2=0 := by
    rw [(tables _).row_recurrence _ 1,first,Nat.sub_add_cancel pos,square]
  rw [(tables _).reduce_period zero,odd,first]

theorem native_stretch_last (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {n : Nat} (dyadic : IsDyadic n) (width : 2≤n) (bridges : UpperBridges tables (n*n+1) n) :
    (tables (n*n+1)).mul (2^n-2) (2^n)=2^(n*n) := by
  have big : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<2) width
  have rowEnd := native_stretch_prefix H law dyadic width bridges (2^n-2) (by omega)
  have prev : 2^n-2+1=2^n-1 := by omega
  rw [prev,repeatBits_last] at rowEnd
  have step := (tables (n*n+1)).row_recurrence (2^n-2) (2^n-1)
  rw [Nat.sub_add_cancel (by omega : 1≤2^n),rowEnd,prev] at step
  apply step.trans
  apply upper_bit_row
  have eo := Nat.pow_succ 2 (n-1)
  rw [show (n-1).succ=n by omega] at eo; omega

theorem native_stretch_actions (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {n m i : Nat} (dyadic : IsDyadic n) (width : 2≤n) (bridges : UpperBridges tables (n*n+1) n)
    (room : n*n<m) (bound : i≤n) : act tables m (2^n-2) i=i*n := by
  by_cases last : i=n
  · subst i
    exact act_of_lower_entry tables room (native_stretch_last H law dyadic width bridges)
  have inside : i<n := by omega
  let d := n*n+1
  have p := Nat.two_pow_pos i
  have col := native_stretch_prefix H law dyadic width bridges (2^i-1)
    (by rw [Nat.sub_add_cancel p]; exact Nat.pow_lt_pow_right (by decide) inside)
  rw [Nat.sub_add_cancel p,repeatBits_single n n i inside] at col
  have inc : i*n<(i+1)*n := by rw [Nat.succ_mul]; omega
  have lim : (i+1)*n≤n*n := Nat.mul_le_mul_right n inside
  have atD : act tables d (2^n-2) i=i*n := by
    unfold act; rw [col]; exact dyadic_tail_signature _ _ _ inc (by dsimp [d]; omega)
  have pr := act_at_smaller_degree tables room (2^n-2) i
  change act tables d (2^n-2) i=min d (act tables m (2^n-2) i) at pr
  rw [atD] at pr
  have vis : i*n<d := Nat.lt_of_lt_of_le inc (Nat.le_trans lim (Nat.le_succ _))
  omega

#print axioms native_stretch_prefix
#print axioms native_stretch_last
#print axioms native_stretch_actions

/-- Projection of the native row gives the full binary-digit repetition
homomorphism for every source degree at most the repetition width. -/
theorem native_stretch_hom (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {n k : Nat} (dyadic : IsDyadic n) (width : 2≤n) (bridges : UpperBridges tables (n*n+1) n)
    (source : k≤n) : StretchHomAt n k := by
  let L := 2^n-2
  have deg : k*n≤n*n+1 := Nat.le_trans (Nat.mul_le_mul_right n source) (Nat.le_succ _)
  have kk : k≤k*n := by
    have t := Nat.mul_le_mul_left k (show 1≤n by omega); rwa [Nat.mul_one] at t
  have action := native_stretch_actions H law dyadic width bridges (Nat.lt_succ_self _) source
  have capped := act_at_smaller_degree tables deg L k
  change act tables (n*n+1) L k=k*n at action
  rw [action,Nat.min_self] at capped
  have zero := (le_act_iff tables (k*n) L k (k*n) (Nat.le_refl _)).mp (Nat.le_of_eq capped.symm)
  have row (y : Nat) (fit : y<2^k) : (tables (k*n)).mul L y=repeatBits n k y := by
    cases y with
    | zero => rw [(tables _).mul_zero,repeatBits_zero]
    | succ i =>
      have high := native_stretch_prefix H law dyadic width bridges i
        (Nat.lt_of_lt_of_le fit (Nat.pow_le_pow_right (by decide) source))
      change (tables (n*n+1)).mul L (i+1)=_ at high
      rw [repeatBits_padding n k n (i+1) source fit] at high
      have pr := (tables (n*n+1)).projection (tables (k*n)) (Nat.pow_dvd_pow 2 deg) L (i+1)
      rw [high,Nat.mod_eq_of_lt (repeatBits_lt n k _)] at pr
      exact pr.symm
  intro a b aa bb
  have pr := (tables (k*n)).projection (tables k) (Nat.pow_dvd_pow 2 kk) a b
  have read := (tables (k*n)).reduce_period zero ((tables (k*n)).mul a b)
  rw [pr,row _ ((tables k).mul_lt a b)] at read
  exact read.symm.trans (((tables (k*n)).mul_distrib L a b).trans
    (by rw [row a aa,row b bb]))

#print axioms native_stretch_hom

theorem sixteen_data_from_crossings (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    (four : act tables 257 14 4=16) : SixteenRowData := by
  have br := upper_bridges_16 (by decide : 20≤257) four
  have dy : IsDyadic 16 := ⟨4,rfl⟩
  refine ⟨fun room fit => native_stretch_actions H law dy (by decide) br (by omega) (by omega),?_⟩
  have value := native_stretch_prefix H law dy (by decide) br 65533 (by decide)
  have pr := (tables 257).projection (tables 256) (Nat.pow_dvd_pow 2 (by decide : 256≤257)) 65534 65534
  change (tables 257).mul 65534 65534=repeatBits 16 16 65534 at value
  rw [value] at pr
  exact pr.symm.trans (by decide)

#print axioms sixteen_data_from_crossings
end Gamma11
