import IndexRigidity
import NormalFormTest

/-! The short prefix preceding the critical-four obstruction. Large
    exponents remain symbolic throughout the computation. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- A first moved index r cannot jump past b unless the low word
    consists of a single run of ones from r to b-1. -/
theorem first_moved_low (F : BinaryFamily) {m a r b : Nat}
    (crit : signature m a = r) (rb : r < b) (bm : b ≤ m)
    (jump : b ≤ act F m a r) : a % 2^b = 2^b-2^r := by
  let z := a % 2^b
  have sz : signature b z = r := by
    have small : signature b a < b := by
      apply Nat.lt_of_not_ge
      intro hs
      have hz := (le_signature b a b (Nat.le_refl _)).mp hs
      have := (le_signature m a b bm).mpr hz
      omega
    have eqv : signature b z = signature b a :=
      signature_mod_eq (Nat.mod_mod _ _)
    exact eqv.trans ((signature_lift bm small).symm.trans crit)
  have atCut := act_at_smaller_degree F bm a r
  rw [Nat.min_eq_left jump] at atCut
  have sqSig := signature_mul F b z z
  rw [sz] at sqSig
  have same : act F b z r = act F b a r :=
    congrArg (signature b) ((F b).mul_mod_left a (2^r))
  rw [same, atCut] at sqSig
  have sq := (le_signature b ((F b).mul z z) b (Nat.le_refl _)).mp (Nat.le_of_eq sqSig.symm)
  rw [Nat.mod_eq_of_lt ((F b).mul_lt z z)] at sq
  rcases (square_zero_iff F b z (Nat.mod_lt _ (Nat.two_pow_pos _))).mp sq with hz | ⟨s, sb, eqv⟩
  · rw [hz, signature_zero] at sz; omega
  · rw [eqv, dyadic_tail_signature b b s sb (Nat.le_refl _)] at sz
    exact sz ▸ eqv

private theorem generator012 (F : BinaryFamily) {m : Nat} (hm : 9 ≤ m) :
    act F m 1 0 = 1 ∧ act F m 1 1 = 2 ∧ act F m 1 2 = 4 :=
  ⟨act_from_low F _ _ _ 2 _ hm (LowProducts.v1_1 (F 9)) (by decide) (by decide),
   act_from_low F _ _ _ 12 _ hm (LowProducts.v1_2 (F 9)) (by decide) (by decide),
   act_from_low F _ _ _ 240 _ hm (LowProducts.v1_4 (F 9)) (by decide) (by decide)⟩

/-- A row whose first two images are 2 and at least N has already
    saturated on input 2 at every cap up to N^N+1, for N ≥ 5. -/
theorem double_start_saturates (F : BinaryFamily) {m k N : Nat}
    (hm : 9 ≤ m) (large : 5 ≤ N) (upper : m ≤ N^N+1)
    (zero : act F m k 0 = 2) (one : N ≤ act F m k 1) : act F m k 2 = m := by
  apply Nat.le_antisymm (act_le F m k 2)
  apply Nat.le_of_not_gt
  intro visible
  let s := (F m).mul k 1
  let t := (F m).mul s 1
  let b := act F m k 1
  obtain ⟨j0,j1,j2⟩ := generator012 F hm
  have cr : signature m s = 2 := zero
  have s0 := fixes_below_signature F m s 0 (by omega)
  have s1 := fixes_below_signature F m s 1 (by omega)
  have s2 : act F m s 2 = b := by
    have h := act_application F m k 1 0
    rw [zero, j0] at h; exact h
  have sb : act F m s b = act F m k 2 := by
    have h := act_application F m k 1 1
    rw [j1] at h; exact h
  have t0 : act F m t 0 = 1 := by
    have h := act_application F m s 1 0
    rw [s0,j0,s1] at h; exact h
  have t1 : act F m t 1 = b := by
    have h := act_application F m s 1 1
    rw [s1,j1,s2] at h; exact h
  have tb : act F m t b = act F m s 4 := by
    have h := act_application F m s 1 2
    rw [s2,j2] at h; exact h
  have hNb : N ≤ b := one
  have strict := act_strict_below_cap F m s 4 b (by omega) (sb ▸ visible)
  have leq := act_mono F m t hNb
  rw [tb] at leq
  have tVis : act F m t N < m := by omega
  have growth := exponential_growth F m t N t0 tVis
  rw [t1] at growth
  have pow := Nat.pow_le_pow_left hNb N
  omega

private theorem aligned_mod_small {u : Nat} (align : 16 ∣ u) (r : Nat) (hr : r ≤ 4) (i : Nat) :
    (u+i) % 2^r = i % 2^r := by
  have hd : 2^r ∣ u := Nat.dvd_trans (Nat.pow_dvd_pow 2 hr) align
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.zero_add, Nat.mod_mod]

private theorem last_sixteen {m N u : Nat} (large : 5≤N) (nm : N≤m)
    (fit : u<2^m) (word : u%2^N=2^N-16) :
    16 ∣ u ∧ (∀ i, i<16 → u+i<2^m) ∧ ∀ i, i<16 → (u+i)%2^N=2^N-16+i := by
  have dN : 16 ∣ 2^N := Nat.pow_dvd_pow 2 (show 4≤N by omega)
  have big : 16 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0<2) (show 4≤N by omega)
  have align : 16 ∣ u := Nat.dvd_of_mod_eq_zero (by
    rw [← Nat.mod_mod_of_dvd u dN,word,Nat.mod_eq_zero_of_dvd (Nat.dvd_sub dN (Nat.dvd_refl 16))])
  refine ⟨align,?_,?_⟩
  · intro i hi
    obtain ⟨k,hk⟩ := align
    obtain ⟨v,hv⟩ := (show 16 ∣ 2^m from Nat.dvd_trans dN (Nat.pow_dvd_pow 2 nm))
    omega
  · intro i hi
    rw [Nat.add_mod,word,Nat.mod_eq_of_lt (by omega : i<2^N),Nat.mod_eq_of_lt (by omega : 2^N-16+i<2^N)]

/-- Appendix B.1. The first twelve additions survive any higher bits
when the low N digits have ones precisely at positions 4 through N-1. -/
theorem protected_block_twelve (F : BinaryFamily) {m N u : Nat}
    (hm : 9 ≤ m) (large : 5 ≤ N) (nm : N ≤ m) (upper : m ≤ N^N+1)
    (fit : u<2^m) (word : u%2^N=2^N-16) :
    (∀ i, 1 ≤ i → i ≤ 11 → act F m (u+i) 4 = m) ∧
      ∀ i, i ≤ 11 → (F m).mul u (i+1) = u+(i+1) := by
  have h4 : 4 ≤ N := by omega
  have big : 16 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0 < 2) h4
  obtain ⟨align,bound,lowAdd⟩ := last_sixteen large nm fit word
  have shadow (r i x : Nat) (hr : r ≤ 4) (test : entry r i (2^x) = 0) :
      r ≤ act F m (u+i) x := by
    apply (le_act_iff F m _ x r (by omega)).mpr
    rw [← (F r).mul_mod_left (u+i), aligned_mod_small align r hr, (F r).mul_mod_left,
      ← entry_eq_mul, test]
  have seed0 : act F m (u+11) 0 = 2 := by
    apply act_of_lower_entry F (by omega)
    change (F 3).mul (u+11) 1 = 4
    rw [← (F 3).mul_mod_left (u+11), aligned_mod_small align 3 (by decide), (F 3).mul_mod_left,
      (F 3).mul_one]
  have seed1 : N ≤ act F m (u+11) 1 := by
    apply (le_act_iff F m _ 1 N nm).mpr
    change (F N).mul (u+11) 2 = 0
    have tail : (u+11)%2^N=2^N-5 := (lowAdd 11 (by decide)).trans (by omega)
    have low : 2^N-5+1 < 2^N := by omega
    rw [← (F N).mul_mod_left (u+11),tail,(F N).row_recurrence (2^N-5) 1,(F N).mul_one,Nat.mod_eq_of_lt low]
    exact (square_zero_iff F N _ low).mpr (Or.inr ⟨2,by omega,by omega⟩)
  obtain ⟨_,j1,j2⟩ := generator012 F hm
  have pass (i x y z : Nat) (hi : i ≤ 10) (gen : act F m 1 x = y)
      (threshold : z ≤ act F m (u+i) x) (next : act F m (u+(i+1)) z = m) :
      act F m (u+i) y = m := by
    have h := act_application F m (u+i) 1 x
    rw [(F m).mul_one, Nat.add_assoc, Nat.mod_eq_of_lt (bound _ (by omega)), gen] at h
    have up := act_mono F m (u+(i+1)) threshold
    rw [next, h] at up
    exact Nat.le_antisymm (act_le ..) up
  have up2 (i : Nat) (h : act F m (u+i) 2 = m) : act F m (u+i) 4 = m := by
    apply Nat.le_antisymm (act_le ..)
    have le := act_mono F m (u+i) (by decide : 2 ≤ 4)
    rwa [h] at le
  have test4 {a x v : Nat} (h : (F 9).mul a (2^x) = v) (res : v % 16 = 0) :
      entry 4 a (2^x) = 0 := by
    rw [entry_eq_mul 4 (F 4), ← (F 9).projection (F 4) (Nat.pow_dvd_pow 2 (by decide : 4 ≤ 9)), h]
    exact res
  have h11 := double_start_saturates F hm large upper seed0 seed1
  have h10 := pass 10 1 2 2 (by decide) j1 (shadow 2 10 1 (by decide) (by decide)) h11
  have h9 := pass 9 1 2 2 (by decide) j1 (shadow 2 9 1 (by decide) (by decide)) h10
  have h8 := pass 8 2 4 2 (by decide) j2 (le_act F m (u+8) 2 (by omega)) h9
  have h7 := pass 7 1 2 4 (by decide) j1
    (shadow 4 7 1 (by decide) (test4 (LowProducts.v7_2 (F 9)) (by decide))) h8
  have h6 := pass 6 1 2 2 (by decide) j1 (shadow 2 6 1 (by decide) (by decide)) h7
  have h5 := pass 5 1 2 2 (by decide) j1 (shadow 2 5 1 (by decide) (by decide)) h6
  have h4row := pass 4 2 4 2 (by decide) j2 (le_act F m (u+4) 2 (by omega)) h5
  have h3 := pass 3 2 4 4 (by decide) j2
    (shadow 4 3 2 (by decide) (test4 (LowProducts.v3_4 (F 9)) (by decide))) h4row
  have h2 := pass 2 2 4 4 (by decide) j2
    (shadow 4 2 2 (by decide) (test4 (LowProducts.v2_4 (F 9)) (by decide))) h3
  have h1 := pass 1 2 4 4 (by decide) j2
    (shadow 4 1 2 (by decide) (test4 (LowProducts.v1_4 (F 9)) (by decide))) h2
  have caps (i : Nat) (lo : 1 ≤ i) (hi : i ≤ 11) : act F m (u+i) 4 = m := by
    rcases (show i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11
        from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact up2 _ (by assumption)
  have zeros (i : Nat) (lo : 1 ≤ i) (hi : i ≤ 11) : (F m).mul (u+i) 16 = 0 :=
    (le_act_iff F m (u+i) 4 m (Nat.le_refl _)).mp (Nat.le_of_eq (caps i lo hi).symm)
  have modOne : (u+1) % 16 = 1 := aligned_mod_small align 4 (by decide) 1
  have prefixAt (i : Nat) (hi : i ≤ 11) : (F m).mul u (i+1) = u+(i+1) := by
    induction i with
    | zero => exact ((F m).mul_one u).trans (Nat.mod_eq_of_lt (bound 1 (by decide)))
    | succ i ih =>
      rw [(F m).row_recurrence u (i+1), ih (by omega),
        (F m).reduce_period (zeros (i+1) (by omega) (by omega)), modOne, (F m).mul_one,
        Nat.add_assoc, Nat.mod_eq_of_lt (bound _ (by omega))]
  exact ⟨caps,prefixAt⟩

/-- At the old degree the twelfth following row also has period at most
16, which preserves one more column of the prefix. -/
theorem protected_block_thirteen (F : BinaryFamily) {m N u : Nat}
    (hm : 9≤m) (large : 5≤N) (nm : N≤m) (upper : m ≤ N^N)
    (fit : u<2^m) (word : u%2^N=2^N-16) : (F m).mul u 13=u+13 := by
  obtain ⟨align,bound,lowAdd⟩ := last_sixteen large nm fit word
  have big : 16 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0<2) (show 4≤N by omega)
  have a12 : (u+12)%2^N=2^N-2^2 := (lowAdd 12 (by decide)).trans (by omega)
  have a13 : (u+13)%2^N=2^N-3 := (lowAdd 13 (by decide)).trans (by omega)
  have fit12 : 2^N-2^2<2^N := by omega
  have sq := (square_zero_iff F N _ fit12).mpr (Or.inr ⟨2,by omega,rfl⟩)
  have jump12 : N ≤ act F m (u+12) 2 := by
    have h := signature_mul F N (2^N-2^2) (2^N-2^2)
    rw [sq,signature_zero,dyadic_tail_signature N N 2 (by omega) (Nat.le_refl _)] at h
    have low := act_at_smaller_degree F nm (u+12) 2
    have rep : act F N (u+12) 2 = act F N (2^N-2^2) 2 := by
      unfold act; rw [← (F N).mul_mod_left (u+12),a12]
    omega
  have j0 : act F m (u+13) 0=1 := by
    apply act_of_lower_entry F (by omega)
    change (F 2).mul (u+13) 1=2
    rw [← (F 2).mul_mod_left (u+13),aligned_mod_small align 2 (by decide),(F 2).mul_one]
  have j1 : N ≤ act F m (u+13) 1 := by
    apply (le_act_iff F m _ _ _ nm).mpr
    change (F N).mul (u+13) 2=0
    have f : 2^N-3+1<2^N := by omega
    rw [← (F N).mul_mod_left (u+13),a13,(F N).row_recurrence (2^N-3) 1,
      (F N).mul_one,Nat.mod_eq_of_lt f]
    exact (square_zero_iff F N _ f).mpr (Or.inr ⟨1,by omega,by omega⟩)
  have sat : act F m (u+13) N=m := by
    apply Nat.le_antisymm (act_le ..)
    apply Nat.le_of_not_gt
    intro visible
    have lower := exponential_growth F m (u+13) N j0 visible
    have pow := Nat.pow_le_pow_left j1 N
    omega
  have move := act_application F m (u+12) 1 2
  have j2 := (generator012 F hm).2.2
  rw [(F m).mul_one,Nat.mod_eq_of_lt (bound 13 (by decide)),j2] at move
  have monotone := act_mono F m (u+13) jump12
  rw [sat,move] at monotone
  have zero := (le_act_iff F m (u+12) 4 m (Nat.le_refl _)).mp monotone
  have prefixAt := (protected_block_twelve F hm large nm (by omega) fit word).2 11 (Nat.le_refl 11)
  rw [(F m).row_recurrence u 12,prefixAt,(F m).reduce_period zero (u+1),
    aligned_mod_small align 4 (by decide) 1,(F m).mul_one,Nat.mod_eq_of_lt (bound 13 (by decide))]

theorem protected_prefix_twelve (F : BinaryFamily) {m N : Nat}
    (hm : 9 ≤ m) (large : 5 ≤ N) (nm : N ≤ m) (upper : m ≤ N^N+1) :
    (F m).mul (2^N-16) 12 = 2^N-4 := by
  have big : 16 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0<2) (show 4 ≤ N by omega)
  have low : 2^N-16<2^N := by omega
  have fit := Nat.lt_of_lt_of_le low (Nat.pow_le_pow_right (by decide : 0<2) nm)
  have h := (protected_block_twelve F hm large nm upper fit (Nat.mod_eq_of_lt low)).2 11 (Nat.le_refl _)
  exact h.trans (by omega)

/-- Critical point four, first half of (R+) in the boundary normal form:
    if r first moves 4 to at least N, then r*13 sends N beyond N^N. -/
theorem critical_four_applied (F : BinaryFamily) {a N t : Nat}
    (large : 5 ≤ N) (degree : 9 ≤ t+1) (nt : N ≤ t) (scale : t = N^N)
    (crit : signature (t+1) a = 4) (jump : N ≤ act F (t+1) a 4) :
    act F (t+1) ((F (t+1)).mul a 13) N = t+1 := by
  let d := t+1
  let p := (F d).mul a 13
  let b := act F d a 4
  change act F d p N = d
  have h0 := fixes_below_signature F d a 0 (by change 0 < signature (t+1) a; omega)
  have h1 := fixes_below_signature F d a 1 (by change 1 < signature (t+1) a; omega)
  have c0 := act_from_low F d 13 0 14 1 degree (LowProducts.v13_1 (F 9)) (by decide) (by decide)
  have c1 := act_from_low F d 13 1 496 4 degree (LowProducts.v13_2 (F 9)) (by decide) (by decide)
  have p0 : act F d p 0 = 1 := by
    have h := act_application F d a 13 0; rw [h0,c0,h1] at h; exact h
  have p1 : act F d p 1 = b := by
    have h := act_application F d a 13 1; rw [h1,c1] at h; exact h
  have Nb : N ≤ b := jump
  apply Nat.le_antisymm (act_le ..)
  apply Nat.le_of_not_gt
  intro visible
  obtain ⟨rigid,earlier⟩ := exponential_at_threshold F scale (by omega : 0 < N)
    p0 (p1.symm ▸ Nb) visible
  have tight := earlier N (Nat.le_refl _)
  have below : p < 2^d := (F d).mul_lt a 13
  have pg : p = 2^N-3 := (Nat.mod_eq_of_lt below).symm.trans rigid
  have dv : 2^N ≤ 2^d := Nat.pow_le_pow_right (by decide) (show N ≤ d by dsimp [d]; omega)
  have big : 16 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ N by omega)
  have pnz : (F d).mul a 13 % 2^d ≠ 0 := by
    change p % 2^d ≠ 0; rw [Nat.mod_eq_of_lt below, pg]; omega
  have left := left_residue_lt F (Nat.le_refl d) pnz
  change a % 2^d < p % 2^d at left
  rw [Nat.mod_eq_of_lt below, pg] at left
  have cut := first_moved_low F crit (show 4 < N by omega) (show N ≤ d by dsimp [d]; omega) jump
  have aa : a % 2^d = 2^N-16 := by
    have proj := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (show N ≤ d by dsimp [d]; omega))
    rw [Nat.mod_eq_of_lt (by omega : a % 2^d < 2^N), cut] at proj
    exact proj
  have prefixAt := protected_prefix_twelve F degree large (show N ≤ d by dsimp [d]; omega)
    (show d ≤ N^N+1 by dsimp [d]; omega)
  have geom : act F d (2^N-3) N = t := by rw [← pg, tight, ← scale]
  apply critical_four_contradiction F large degree nt prefixAt geom
  rw [← aa, (F d).mul_mod_left]
  exact pg

/-- The same strict estimate for the acting row itself if 13 maps 4
    below N. Only that one lower-degree fact is required for this transfer. -/
theorem critical_four_actor (F : BinaryFamily) {a N t : Nat}
    (large : 5 ≤ N) (degree : 9 ≤ t+1) (nt : N ≤ t) (scale : t = N^N)
    (thirteen : act F (t+1) 13 4 ≤ N)
    (crit : signature (t+1) a = 4) (jump : N ≤ act F (t+1) a 4) :
    act F (t+1) a N = t+1 := by
  have h := critical_four_applied F large degree nt scale crit jump
  have up := act_mono F (t+1) ((F (t+1)).mul a 13) jump
  rw [h, act_application] at up
  exact Nat.le_antisymm (act_le ..) (Nat.le_trans up (act_mono F (t+1) a thirteen))

#print axioms protected_block_twelve
#print axioms protected_block_thirteen
#print axioms protected_prefix_twelve
#print axioms critical_four_applied
#print axioms critical_four_actor
end Gamma11
