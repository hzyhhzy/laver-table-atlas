import OddDiagonal

/-! The old odd-row slice descriptors are constructed from two endpoints
    and the licensed bit-stretch in a smaller table. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- Repeat each of the lowest n binary digits of x exactly w times. -/
def repeatBits (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x =>
    (if x%2=0 then 0 else 2^w-1) + 2^w * repeatBits w n (x/2)

theorem repeatBits_lt (w n x : Nat) : repeatBits w n x < 2^(n*w) := by
  induction n generalizing x with
  | zero => simp [repeatBits]
  | succ n ih =>
    let Q := 2^w
    have pos : 0 < Q := Nat.two_pow_pos _
    have bigger := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt (ih (x/2)))
    rw [Nat.mul_succ] at bigger
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm (2^(n*w))]
    change (if x%2=0 then 0 else Q-1) + Q * repeatBits w n (x/2) < Q * 2^(n*w)
    split <;> omega

theorem repeatBits_pos {w n x : Nat} (pw : 0 < w) (px : 0 < x) (below : x < 2^n) :
    0 < repeatBits w n x := by
  induction n generalizing x with
  | zero => simp at below; omega
  | succ n ih =>
    rw [repeatBits]
    split
    next even =>
      have half : 0 < x/2 := by omega
      rw [Nat.pow_succ] at below
      rw [Nat.zero_add]
      exact Nat.mul_pos (Nat.two_pow_pos _) (ih half (by omega))
    next _ =>
      have big : 2 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) pw
      omega

/-- In two adjacent stretched integers only the block at the carry and
    the trailing ones change. B contains all higher digits. -/
theorem repeatBits_carry (w n x : Nat) (fits : x+1 < 2^n) :
    ∃ B p, w ∣ p ∧ p+w ≤ n*w ∧ 2^(p+w) ∣ B ∧
      repeatBits w n x = B+2^p-1 ∧
      repeatBits w n (x+1) = B+2^p*(2^w-1) := by
  induction n generalizing x with
  | zero => simp at fits
  | succ n ih =>
    let Q := 2^w
    let q := x/2
    have Qpos : 0 < Q := Nat.two_pow_pos _
    by_cases even : x%2=0
    · refine ⟨Q*repeatBits w n q, 0, Nat.dvd_zero _, ?_, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simp only [Nat.zero_add]; exact Nat.dvd_mul_right _ _
      · rw [repeatBits, if_pos even, Nat.zero_add, Nat.pow_zero, Nat.add_sub_cancel]
      · have odd : (x+1)%2≠0 := by omega
        have same : (x+1)/2=q := by dsimp [q]; omega
        rw [repeatBits, if_neg odd, same, Nat.pow_zero, Nat.one_mul, Nat.add_comm]
    · rw [Nat.pow_succ] at fits
      obtain ⟨B,p,wp,pn,div,old,newVal⟩ := ih q (by dsimp [q]; omega)
      refine ⟨Q*B, w+p, Nat.dvd_add (Nat.dvd_refl w) wp, ?_, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [Nat.add_assoc, Nat.pow_add]; exact Nat.mul_dvd_mul_left Q div
      · rw [repeatBits, if_neg even, show x/2=q from rfl, old, Nat.pow_add]
        change Q-1 + Q*(B+2^p-1) = Q*B + Q*2^p-1
        have pos : 0 < B+2^p := Nat.lt_of_lt_of_le (Nat.two_pow_pos p) (Nat.le_add_left ..)
        have distribute := congrArg (fun a => Q*a) (Nat.sub_add_cancel pos)
        change Q*(B+2^p-1+1) = Q*(B+2^p) at distribute
        rw [Nat.mul_succ, Nat.mul_add] at distribute
        omega
      · have eo : (x+1)%2=0 := by omega
        have next : (x+1)/2=q+1 := by dsimp [q]; omega
        rw [repeatBits, if_pos eo, Nat.zero_add, next, newVal, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]

/-- When the smaller table has no zero before e, the actual outputs in
    the larger table are ordered. Two bounds place the complete prefix
    in a single aligned interval, so its small-degree residues suffice. -/
theorem prefix_in_aligned_interval (F : BinaryFamily) {s t A D e : Nat} (st : s ≤ t)
    (align : 2^s ∣ D) (start : D ≤ (F t).mul A 1)
    (stop : (F t).mul A e < D+2^s)
    (nonzero : ∀ i, 1 ≤ i → i ≤ e → (F s).mul A i ≠ 0)
    {i : Nat} (ip : 1 ≤ i) (ie : i ≤ e) : (F t).mul A i = D+(F s).mul A i := by
  obtain ⟨period,hp⟩ := (F t).exists_firstZero A
  have whole : e < period := by
    apply Nat.lt_of_not_ge
    intro early
    have proj := (F t).projection (F s) (Nat.pow_dvd_pow 2 st) A period
    rw [hp.2.1, Nat.zero_mod] at proj
    exact nonzero period hp.1 early proj.symm
  have mono {x y : Nat} (hx : 1 ≤ x) (xy : x ≤ y) (ye : y ≤ e) :
      (F t).mul A x ≤ (F t).mul A y := by
    rcases Nat.eq_or_lt_of_le xy with rfl | lt
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((F t).firstZero_strict hp hx lt (Nat.lt_of_le_of_lt ye whole))
  have lower := Nat.le_trans start (mono (Nat.le_refl 1) ip ie)
  have upper := Nat.lt_of_le_of_lt (mono ip ie (Nat.le_refl _)) stop
  let z := (F t).mul A i-D
  have val : (F t).mul A i = D+z := by dsimp [z]; omega
  have small : z < 2^s := by dsimp [z]; omega
  have proj := (F t).projection (F s) (Nat.pow_dvd_pow 2 st) A i
  rw [val, Nat.add_mod, Nat.mod_eq_zero_of_dvd align, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt small] at proj
  rw [← proj]; exact val

/-- Homomorphism at an explicitly specified source degree, for the
    usual finite products and the concrete digit-repetition map. -/
def StretchHomAt (w n : Nat) : Prop := ∀ a b, a < 2^n → b < 2^n →
  repeatBits w n ((tables n).mul a b) =
    (tables (n*w)).mul (repeatBits w n a) (repeatBits w n b)

theorem repeatBits_zero (w n : Nat) : repeatBits w n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatBits, ih]

theorem repeatBits_one (w n : Nat) (pn : 0 < n) : repeatBits w n 1 = 2^w-1 := by
  cases n with
  | zero => omega
  | succ n => simp [repeatBits, repeatBits_zero]

theorem stretch_row {w n : Nat} (pw : 0 < w) (pn : 0 < n) (hom : StretchHomAt w n)
    (y : Nat) (fits : y < 2^n) : (tables (n*w)).mul (2^w-2) y = repeatBits w n y := by
  have size : 2 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) pw
  have source : 2 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < 2) pn
  induction y with
  | zero => rw [(tables _).mul_zero, repeatBits_zero]
  | succ y ih =>
    have he := hom y 1 (by omega) (by omega)
    rw [(tables n).mul_one, Nat.mod_eq_of_lt fits, repeatBits_one w n pn] at he
    rw [(tables _).row_recurrence, ih (by omega), show 2^w-2+1 = 2^w-1 by omega, ← he]

/-- This coarser old-diagonal input contains two values per odd column
    and a block alignment. It makes no assertions about its inner row. -/
structure OddColumnEndpoints (t r : Nat) where
  m : Nat
  positive : 0 < m
  D : Nat
  window : 256 * 256^m ≤ t
  aligned : 2^(256 * 256^m) ∣ D
  start : oldEntry t geometricRow r = D+(2^(256^m)-2)
  finish : oldEntry t geometricRow (r+1) = D + repeatBits (256^m) 256 (geometricRow+1)

theorem corners_of_endpoints {t r : Nat} (ends : OddColumnEndpoints t r)
    (stretch : ∀ m, 0 < m → StretchHomAt (256^m) 256) (i : Nat)
    (ipos : 1 ≤ i) (ibound : i ≤ geometricRow) :
    ∃ c : SliceCorners t 256 (oldEntry t geometricRow r) i, c.p+c.w ≤ t ∧
      ∃ m, 0 < m ∧ c.w=256^m := by
  let w := 256^ends.m
  let D := ends.D
  let A := oldEntry t geometricRow r
  let s := 256*w
  let e := geometricRow+1
  have pw : 0 < w := Nat.pow_pos (by decide : 0 < 256)
  have wge : 256 ≤ w := calc
    256 = 256^1 := by decide
    _ ≤ w := Nat.pow_le_pow_right (by decide) ends.positive
  have st : s ≤ t := ends.window
  have aligned : 2^s ∣ D := ends.aligned
  have beginRow : A = D+(2^w-2) := ends.start
  have ep : e < 2^256 := by dsimp [e,geometricRow]; omega
  have hi : i+1 ≤ e := Nat.succ_le_succ ibound
  have tailPos : 2 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) pw
  have sm : (2^w-2)+1 < 2^s :=
    Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_mul_of_pos_left w (by decide : 0 < 256)))
  have lowRow (y : Nat) (fit : y ≤ e) : (tables s).mul A y = repeatBits w 256 y := by
    rw [beginRow, ← (tables s).mul_mod_left, Nat.add_mod, Nat.mod_eq_zero_of_dvd aligned,
      Nat.zero_add, Nat.mod_mod, (tables s).mul_mod_left]
    exact stretch_row pw (by decide) (stretch _ ends.positive) y (Nat.lt_of_le_of_lt fit ep)
  have stopVal : (tables t).mul A e = D+repeatBits w 256 e :=
    ((tables t).row_recurrence geometricRow r).symm.trans ends.finish
  have stop : (tables t).mul A e < D+2^s := by
    rw [stopVal]
    exact Nat.add_lt_add_left (repeatBits_lt w 256 e) D
  have ab : A < 2^t := (tables t).mul_lt geometricRow r
  have dsmall : D < 2^t := by omega
  have room : D+2^s ≤ 2^t := by
    obtain ⟨j,hj⟩ := aligned
    obtain ⟨k,hk⟩ := Nat.pow_dvd_pow 2 st
    rw [hj,hk] at dsmall ⊢
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (2^s) (Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left dsmall))
  have start : D ≤ (tables t).mul A 1 := by rw [(tables t).mul_one, beginRow, Nat.mod_eq_of_lt (by omega)]; omega
  have nz (y : Nat) (yp : 1 ≤ y) (ye : y ≤ e) : (tables s).mul A y ≠ 0 := by
    rw [lowRow y ye]
    exact Nat.ne_of_gt (repeatBits_pos pw yp (Nat.lt_of_le_of_lt ye ep))
  have row (y : Nat) (yp : 1 ≤ y) (ye : y ≤ e) : oldEntry t A y = D+repeatBits w 256 y :=
    (prefix_in_aligned_interval tables st aligned start stop nz yp ye).trans (congrArg (D+·) (lowRow y ye))
  obtain ⟨B,p,wp,window,divB,prev,next⟩ := repeatBits_carry w 256 i (Nat.lt_of_le_of_lt hi ep)
  have pow : w = 2^(8*ends.m) := (Nat.pow_mul 2 8 ends.m).symm
  have divD : 2^(p+w) ∣ D := Nat.dvd_trans (Nat.pow_dvd_pow 2 window) aligned
  let c : SliceCorners t 256 A i := {
    w := w, p := p, background := D+B, offset := D, width := ⟨8*ends.m,pow⟩,
    width_ge := wge, width_two := by omega, aligned := wp, block_dvd := Nat.dvd_add divD divB,
    offset_dvd := aligned, argument := by rw [beginRow]; omega,
    start := by rw [row i ipos (by omega),prev]; have := Nat.two_pow_pos p; omega,
    finish := by rw [row (i+1) (by omega) hi,next, Nat.add_assoc] }
  exact ⟨c, Nat.le_trans window st, ends.m, ends.positive, rfl⟩

#print axioms corners_of_endpoints

end Gamma11
