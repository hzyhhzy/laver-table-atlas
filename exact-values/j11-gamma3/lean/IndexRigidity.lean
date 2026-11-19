import EndpointGrowth
import LaverLowerBounds.DyadicBasics

/-! Equality in the linear and exponential lower estimates. The arguments
use only ordinary finite tables. Throughout, m is a cap above the last
image under consideration, so no equality is inferred from saturation. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem act_at_smaller_degree (F : BinaryFamily) {d m : Nat} (hm : d ≤ m) (a x : Nat) :
    act F d a x = min d (act F m a x) := by
  have hd := act_le F d a x
  have compare (k : Nat) (hk : k ≤ d) : k ≤ act F d a x ↔ k ≤ act F m a x :=
    (le_act_iff F d a x k hk).trans (le_act_iff F m a x k (Nat.le_trans hk hm)).symm
  have up := (compare _ hd).mp (Nat.le_refl _)
  exact Nat.le_antisymm (Nat.le_min.mpr ⟨hd, up⟩)
    ((compare _ (Nat.min_le_left ..)).mpr (Nat.min_le_right ..))

private theorem input_below (F : BinaryFamily) {m a x : Nat} (visible : act F m a x < m) : x < m := by
  apply Nat.lt_of_not_ge; intro h
  have := Nat.le_trans (le_act F m a m (Nat.le_refl _)) (act_mono F m a h)
  omega

/-- A nonzero output at any lower degree is larger than the left input
at that very degree, even when the upper-degree operands are not native. -/
theorem left_residue_lt (F : BinaryFamily) {d m a b : Nat} (dm : d ≤ m)
    (nz : (F m).mul a b % 2^d ≠ 0) : a % 2^d < (F m).mul a b % 2^d := by
  have proj := (F m).projection (F d) (Nat.pow_dvd_pow 2 dm) a b
  rw [← (F d).mul_mod_left a] at proj
  rcases (F d).row_grows (a % 2^d) b (Nat.mod_lt _ (Nat.two_pow_pos _)) with zero | lt
  · exact False.elim (nz (proj.trans zero))
  · exact proj.symm ▸ lt

theorem nonzero_of_moves (F : BinaryFamily) {d m a x : Nat} (dm : d ≤ m)
    (xd : x < d) (move : x < act F m a x) : a % 2^d ≠ 0 := by
  intro z
  have cut := (le_act_iff F m a x (x+1) (by omega)).mp move
  have sub := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (show x+1 ≤ d by omega))
  rw [z, Nat.zero_mod] at sub
  rw [← (F (x+1)).mul_mod_left a, ← sub, (F (x+1)).zero_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_succ (by decide))] at cut
  exact Nat.ne_of_gt (Nat.two_pow_pos _) cut

/-- An interval with no skipped image cannot contain a set bit of the
actor. Taking its highest possible set bit suffices. -/
theorem consecutive_residue_lt (F : BinaryFamily) {m a u v : Nat} (uv : u ≤ v)
    (visible : act F m a v < m)
    (tight : act F m a v = act F m a u + (v-u)) :
    a % 2^(act F m a v + 1) < 2^(act F m a u) := by
  let y := act F m a v
  let x := act F m a u
  let c := a % 2^(y+1)
  change c < 2^x
  apply Nat.lt_of_not_ge; intro high
  have nz : c ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) high)
  have lc := (Nat.le_log2 nz).mpr high
  have hc : c.log2 < y+1 := (Nat.log2_lt nz).mpr (Nat.mod_lt _ (Nat.two_pow_pos _))
  let i := u + (c.log2-x)
  change y = x + (v-u) at tight
  have ui : u ≤ i := Nat.le_add_right ..
  have iv : i ≤ v := by dsimp [i]; omega
  have lower := act_distance F m a ui (Nat.lt_of_le_of_lt (act_mono F m a iv) visible)
  have upper := act_distance F m a iv visible
  change x + (i-u) ≤ act F m a i at lower
  change act F m a i + (v-i) ≤ y at upper
  have count : i = u + (c.log2-x) := rfl
  have hit : act F m a i = c.log2 := by omega
  have clear := act_residue_lt F m a i (Nat.lt_of_le_of_lt (act_mono F m a iv) visible)
  rw [hit] at clear
  have proj : c % 2^(c.log2+1) = a % 2^(c.log2+1) :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  rw [← proj, Nat.mod_eq_of_lt Nat.lt_log2_self] at clear
  exact Nat.not_lt_of_le (Nat.log2_self_le nz) clear

private theorem adjacent_action (F : BinaryFamily) {m a k : Nat} (visible : act F m a (k+1) < m) :
    let w := (F m).mul a (2^k-1)
    act F m w (act F m a 0) = act F m a k ∧ act F m w (act F m a 1) = act F m a (k+1) := by
  have hm := input_below F visible
  obtain ⟨first, second⟩ := adjacent_pair F m k (by omega)
  exact ⟨(act_application F m a _ 0).trans (congrArg (act F m a) first),
    (act_application F m a _ 1).trans (congrArg (act F m a) second)⟩

private theorem recover_lower_residue {a d b k : Nat} (bd : b ≤ d)
    (small : a % 2^d < 2^b) (already : a % 2^b < 2^k) : a % 2^d < 2^k := by
  have h := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 bd)
  rw [Nat.mod_eq_of_lt small] at h
  exact h ▸ already

/-- Equality case of Dougherty II, Lemma 7.1, for any finite family. -/
theorem linear_equality_residue (F : BinaryFamily) {m a : Nat} (n : Nat) (positive : 0 < n)
    (visible : act F m a n < m)
    (tight : act F m a n = act F m a 0 + (act F m a 1-act F m a 0)*n) :
    a % 2^(act F m a n+1) < 2^(act F m a 1) := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases kz : k = 0
    · subst k; exact act_residue_lt F m a 1 visible
    let f := act F m a
    let w := (F m).mul a (2^k-1)
    have mono := act_mono F m a (Nat.le_succ k)
    have vk := Nat.lt_of_le_of_lt mono visible
    obtain ⟨l, r⟩ := adjacent_action F visible
    change act F m w (f 0) = f k at l
    change act F m w (f 1) = f (k+1) at r
    have inputOrder : f 0 ≤ f 1 := act_mono F m a (by decide)
    have wvis : act F m w (f 1) < m := r ▸ visible
    have gap := act_distance F m w inputOrder wvis
    rw [l, r] at gap
    have prec := linear_growth F m a k vk
    change f 0 + (f 1 - f 0) * k ≤ f k at prec
    change f (k+1) = f 0 + (f 1-f 0)*(k+1) at tight
    rw [Nat.mul_succ] at tight
    have prevTight : f k = f 0 + (f 1-f 0)*k := by omega
    have localTight : act F m w (f 1) = act F m w (f 0)+(f 1-f 0) := by rw [l,r]; omega
    have loW := consecutive_residue_lt F inputOrder wvis localTight
    rw [l,r] at loW
    have move : f 0 < act F m w (f 0) := l ▸ (act_strict_below_cap F m a 0 k (by omega) vk)
    have hleft := left_residue_lt F (a := a) (b := 2^k-1) (d := f (k+1)+1)
      (show f (k+1)+1 ≤ m from visible)
      (nonzero_of_moves F (a := w) (x := f 0) visible (by change _ < f (k+1)+1; have := act_mono F m a (Nat.zero_le (k+1)); omega) move)
    change a % 2^(f (k+1)+1) < w % 2^(f (k+1)+1) at hleft
    exact recover_lower_residue (Nat.succ_le_succ mono)
      (Nat.lt_trans (Nat.lt_trans hleft loW) (Nat.pow_lt_pow_succ (by decide)))
      (ih (by omega) vk prevTight)

/-- At any cut above the first image and at most the second image, the
first output squares to zero. The argument also covers a saturated second image. -/
theorem first_two_cut (F : BinaryFamily) {m a b r : Nat} (bd : b≤m) (rb : r<b)
    (zero : act F m a 0=r) (hit : b ≤ act F m a 1) :
    a % 2^b = 2^b - 2^r - 1 := by
  let z := (F b).mul a 1
  have valZ : signature b z = r := by
    have eqv := act_at_smaller_degree F bd a 0
    rw [zero, Nat.min_eq_right (Nat.le_of_lt rb)] at eqv
    exact eqv
  have nz : z ≠ 0 := by intro h; rw [h, signature_zero] at valZ; omega
  have back := (le_act_iff F m a 1 b bd).mp hit
  change (F b).mul a 2 = 0 at back
  have sq : (F b).mul z z = 0 := by
    change (F b).mul ((F b).mul a 1) ((F b).mul a 1) = 0
    rw [← (F b).mul_distrib, (F b).mul_one 1, (F b).mul_mod_right]; exact back
  rcases (square_zero_iff F b z ((F b).mul_lt a 1)).mp sq with hz | ⟨s, sb, hs⟩
  · exact False.elim (nz hz)
  have valS := dyadic_tail_signature b b s sb (Nat.le_refl _)
  rw [hs, valS] at valZ
  obtain rfl := valZ
  have rep : z = (a % 2^b + 1) % 2^b := by
    change (F b).mul a 1 = _
    rw [← (F b).mul_mod_left a, (F b).mul_one]
  have low := Nat.mod_lt a (Nat.two_pow_pos b)
  have noWrap : a % 2^b + 1 < 2^b := by
    apply Nat.lt_of_not_ge; intro h
    rw [show a % 2^b + 1 = 2^b by omega, Nat.mod_self] at rep
    exact nz rep
  rw [Nat.mod_eq_of_lt noWrap] at rep
  omega

theorem first_two_residue (F : BinaryFamily) {m a b r : Nat}
    (zero : act F m a 0 = r) (one : act F m a 1 = b) (visible : b < m) :
    a % 2^b = 2^b - 2^r - 1 := by
  have rb : r < b := zero ▸ one ▸ act_strict_below_cap F m a 0 1 (by decide) (one ▸ visible)
  exact first_two_cut F (Nat.le_of_lt visible) rb zero (Nat.le_of_eq one.symm)

private theorem even_app_at_zero (F : BinaryFamily) {m a : Nat} (hm : 0 < m)
    (a0 : act F m a 0 = 1) (y : Nat) : act F m ((F m).mul a y) 0 = 0 := by
  have first := (le_act_iff F m a 0 1 hm).mp (Nat.le_of_eq a0.symm)
  change (F 1).mul a 1 = 0 at first
  have allzero : (F 1).mul a y = 0 := by rw [(F 1).reduce_period first y, Nat.mod_one, (F 1).mul_zero]
  have low := ((F m).projection (F 1) (Nat.pow_dvd_pow 2 hm) a y).trans allzero
  apply act_of_lower_entry F (k := 0) hm
  change (F 1).mul ((F m).mul a y) 1 = 1
  rw [← (F 1).mul_mod_left, low, (F 1).zero_mul]

/-- If the exponential estimate is sharp, the actor has no nonzero high
digits through the attained endpoint, and every earlier estimate is sharp. -/
theorem exponential_equality (F : BinaryFamily) {m a b n : Nat}
    (start : act F m a 0 = 1) (base : act F m a 1 = b) (positive : 0 < n)
    (visible : b^n < m) (tight : act F m a n = b^n) :
    a % 2^(b^n+1) = 2^b-3 ∧ ∀ k, k ≤ n → act F m a k = b^k := by
  induction n with
  | zero => omega
  | succ k ih =>
    let f := act F m a
    change f (k+1) = b^(k+1) at tight
    have endVis : f (k+1) < m := tight ▸ visible
    have hbVis : f 1 < m := Nat.lt_of_le_of_lt (act_mono F m a (by omega : 1 ≤ k+1)) endVis
    have bbig : 1 < b := start ▸ base ▸ act_strict_below_cap F m a 0 1 (by decide) hbVis
    have low := first_two_residue F start base (base ▸ hbVis)
    change a % 2^b = 2^b - 2 - 1 at low
    by_cases kz : k = 0
    · subst k
      rw [Nat.zero_add, Nat.pow_one]
      constructor
      · have smaller := act_residue_lt F m a 1 hbVis
        rw [base] at smaller
        have eqv := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (Nat.le_succ b))
        rw [Nat.mod_eq_of_lt smaller] at eqv
        omega
      · intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | h
        · simpa only [Nat.pow_one] using base
        · have : i = 0 := by omega
          subst i; simpa only [Nat.pow_zero] using start
    let w := (F m).mul a (2^k-1)
    have mono := act_mono F m a (Nat.le_succ k)
    have vk : f k < m := Nat.lt_of_le_of_lt mono endVis
    obtain ⟨l,r⟩ := adjacent_action F endVis
    rw [start] at l
    rw [base] at r
    change act F m w 1 = f k at l
    change act F m w b = f (k+1) at r
    have w0 := even_app_at_zero F (by omega : 0 < m) start (2^k-1)
    change act F m w 0 = 0 at w0
    have wvis : act F m w b < m := r ▸ endVis
    have mult := linear_growth F m w b wvis
    rw [w0,l,r,Nat.sub_zero,Nat.zero_add] at mult
    have prior := exponential_growth F m a k start vk
    rw [base] at prior
    change b^k ≤ f k at prior
    have endValue : f (k+1) = b^k*b := tight.trans (Nat.pow_succ ..)
    have upper : f k*b ≤ b^k*b := Nat.le_trans mult (Nat.le_of_eq endValue)
    have exactK := Nat.le_antisymm (Nat.le_of_mul_le_mul_right upper (by omega)) prior
    have wTight : act F m w b = act F m w 0 + (act F m w 1 - act F m w 0)*b := by
      rw [w0,l,r,exactK,endValue,Nat.sub_zero,Nat.zero_add]
    have small := linear_equality_residue F b (by omega) wvis wTight
    rw [r,l,exactK,tight] at small
    have move : 1 < act F m w 1 := by
      have hkb : f 1 ≤ f k := act_mono F m a (by omega)
      rw [l]; change f 1 = b at base; omega
    have dvis : b^(k+1)+1 ≤ m := visible
    have bnd : 1 < b^(k+1)+1 := by
      have h := Nat.pow_pos (by omega : 0 < b) (n := k+1)
      omega
    have wlow := nonzero_of_moves F dvis bnd move
    have left := left_residue_lt F (a := a) (b := 2^k-1) dvis wlow
    change a % 2^(b^(k+1)+1) < w % 2^(b^(k+1)+1) at left
    have prevVis : b^k < m := exactK ▸ vk
    obtain ⟨prev, earlier⟩ := ih (by omega) prevVis exactK
    have pk := Nat.pow_le_pow_right (n := b) (by omega) (Nat.le_succ k)
    have proj := Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 (Nat.succ_le_succ pk))
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_trans left small) (Nat.pow_lt_pow_succ (by decide)))] at proj
    refine ⟨proj.trans prev, ?_⟩
    intro v hv
    rcases Nat.eq_or_lt_of_le hv with rfl | h
    · exact tight
    · exact earlier v (by omega)

#print axioms linear_equality_residue
#print axioms exponential_equality
/-- At degree b^n+1, even an a priori lower bound on the second image
    suffices: a visible n-th image forces the entire equality case. -/
theorem exponential_at_threshold (F : BinaryFamily) {a b n t : Nat}
    (scale : t = b^n) (positive : 0 < n)
    (start : act F (t+1) a 0 = 1) (base : b ≤ act F (t+1) a 1)
    (visible : act F (t+1) a n < t+1) :
    a % 2^(t+1) = 2^b-3 ∧ ∀ k, k ≤ n → act F (t+1) a k = b^k := by
  have upper := Nat.le_of_lt_succ visible
  have grow := exponential_growth F (t+1) a n start visible
  have exactBase : act F (t+1) a 1 = b := by
    apply Nat.le_antisymm _ base
    apply Nat.le_of_not_gt
    intro larger
    have strict := Nat.pow_lt_pow_left larger (by omega : n ≠ 0)
    omega
  rw [exactBase] at grow
  have tight : act F (t+1) a n = b^n := by omega
  have h := exponential_equality F start exactBase positive (tight ▸ visible) tight
  rwa [← scale] at h

end Gamma11
