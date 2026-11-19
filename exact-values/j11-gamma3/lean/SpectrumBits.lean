import BlockPrefix

/-! A bit set in the native row omits its position from the image. This
turns the all-ones shift used in block lifting into a consequence of the
single block-boundary lemma. It also supplies the outer guard at index 254. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds TableElement

theorem high_bit_clear_at_image (H : FirstRowUnbounded) (a x : Nat) :
    let t := image H a x; a % 2 ^ (t + 1) < 2 ^ t := by
  let t := image H a x
  change a % 2 ^ (t + 1) < 2 ^ t
  apply Nat.lt_of_not_ge; intro high
  let b := a % 2 ^ (t + 1)
  have bbound : b < 2 ^ t * 2 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have low : b % 2 ^ t = a % 2 ^ t := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ t))
  change 2 ^ t ≤ b at high
  rw [Nat.mod_eq_sub_mod high, Nat.mod_eq_of_lt (by omega)] at low
  have old := (numeral_zero_iff H a t x).mpr (Nat.le_refl _)
  have zero : (tables t).mul (a % 2 ^ t) (2 ^ x) = 0 := by rw [(tables t).mul_mod_left, canonical_mul, old]
  have up := upper_copy (n := 2 ^ t) (tables (t + 1)) (tables t) (Nat.mod_lt a (Nat.two_pow_pos t)) (2 ^ x)
  rw [if_pos zero] at up
  have hz : entry (t + 1) a (2 ^ x) = 0 := by
    rw [← canonical_mul, ← (tables (t + 1)).mul_mod_left a]
    change (tables (t + 1)).mul b (2 ^ x) = 0
    rwa [show b = 2 ^ t + a % 2 ^ t by omega]
  exact Nat.not_succ_le_self t ((numeral_zero_iff H a (t+1) x).mp hz)

theorem image_distance (H : FirstRowUnbounded) (a x k : Nat) :
    image H a x + k ≤ image H a (x + k) := by
  induction k with
  | zero => simp
  | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih ((numeral a).index_strict (numeral_total H a) (Nat.lt_succ_self (x + k))))

theorem extra_bit_after_ones (H : FirstRowUnbounded) {p w a : Nat}
    (ones : 2 ^ p ∣ a + 1) (above : 2 ^ p ≤ a) (below : a < 2 ^ (p+w+1)) :
    p + w < image H a w := by
  have nz : a ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos p) above)
  have start : p ≤ image H a 0 := by
    apply (numeral_zero_iff H a p 0).mp
    rw [Nat.pow_zero, ← canonical_mul, (tables p).mul_one, Nat.mod_eq_zero_of_dvd ones]
  let i := a.log2 - p
  have lo := (Nat.le_log2 nz).mpr above
  have hi := (Nat.log2_lt nz).mpr below
  have z : p + i = a.log2 := by dsimp [i]; omega
  have iw : i ≤ w := by omega
  have first := image_distance H a 0 i
  rw [Nat.zero_add] at first
  have last := image_distance H a i (w-i)
  rw [show i + (w-i) = w by omega] at last
  apply Nat.lt_of_not_ge; intro bad
  have eqv : image H a i = a.log2 := by omega
  have clear := high_bit_clear_at_image H a i
  change a % 2 ^ (image H a i + 1) < 2 ^ image H a i at clear
  rw [eqv, Nat.mod_eq_of_lt Nat.lt_log2_self] at clear
  exact Nat.not_lt_of_le (Nat.log2_self_le nz) clear

theorem image_eq_of_exact_entry (H : FirstRowUnbounded) {a x t : Nat}
    (he : (tables (t + 1)).mul a (2 ^ x) = 2 ^ t) : image H a x = t := by
  have fc := (exact_iff_firstChange tables a x t).mp ((canonical_mul _ _ _).symm.trans he)
  have below := (numeral_zero_iff H a t x).mp (fc.1 t (Nat.le_refl _))
  have above : ¬ t+1 ≤ image H a x := fun hi => fc.2 ((numeral_zero_iff H a (t+1) x).mpr hi)
  change t ≤ image H a x at below
  omega

theorem ones_shift_of_boundary (H : FirstRowUnbounded) (boundary : BlockBoundary H) : OnesRowShift H := by
  intro w p dyadic aligned
  let d := p + w + 1
  let q := 2 ^ p
  let P := 2 ^ w
  have qpos : 0 < q := Nat.two_pow_pos p
  have size : q * P = 2 ^ (p + w) := (Nat.pow_add 2 p w).symm
  have cap : q * P < 2 ^ d := size ▸ Nat.pow_lt_pow_succ (by decide)
  have succQ : q - 1 + 1 = q := by omega
  have rowValue (v : Nat) (pv : 1 ≤ v) (ve : v ≤ P) : (tables d).mul (q - 1) v = q * v := by
    induction v with
    | zero => omega
    | succ v ih =>
      have small := Nat.mul_le_mul_left q ve
      cases v with
      | zero =>
        have bound : q < 2 ^ d := by
          have hq := Nat.mul_le_mul_left q (Nat.two_pow_pos w)
          rw [Nat.mul_one] at hq
          exact Nat.lt_of_le_of_lt hq cap
        rw [(tables d).mul_one, succQ, Nat.mul_one, Nat.mod_eq_of_lt bound]
      | succ v =>
        let X := q * (v + 1)
        let Z := X + q - 1
        have next : X + q = q * (v + 2) := (Nat.mul_succ q _).symm
        have zsucc : Z + 1 = X + q := by dsimp [Z]; omega
        have qdiv : q ∣ Z + 1 := by rw [zsucc, next]; exact Nat.dvd_mul_right ..
        have qx : q ≤ X := by dsimp [X]; simpa only [Nat.mul_one] using Nat.mul_le_mul_left q (show 1 ≤ v+1 by omega)
        have zb : q ≤ Z := by omega
        have za : Z < 2 ^ (p + w + 1) := calc
          Z < X + q := zsucc ▸ Nat.lt_succ_self _
          _ = q * (v + 2) := next
          _ < 2 ^ d := Nat.lt_of_le_of_lt small cap
        have prot := extra_bit_after_ones H qdiv zb za
        obtain ⟨hit, _⟩ := boundary (d := d) dyadic aligned (show 2 ^ p ∣ X from Nat.dvd_mul_right ..) prot
        rw [(tables d).row_recurrence, ih (by omega) (by omega), succQ]
        exact hit.trans ((congrArg (fun z => z % 2 ^ d) next).trans (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt small cap)))
  exact image_eq_of_exact_entry H ((rowValue P (Nat.two_pow_pos _) (Nat.le_refl _)).trans size)

theorem odd_outer_floor (H : FirstRowUnbounded) {r : Nat} (positive : 0 < r)
    (odd : r % 2 = 1) (short : r < 2 ^ 255) :
    targetIndex ≤ image H (2 ^ 256 - 3) (image H r 254) := by
  have enough : 256 ≤ image H r 254 := by
    by_cases one : r = 1
    · subst r
      have hz : image H 1 2 = 4 := by
        apply image_eq_of_exact_entry
        change (tables 5).mul 1 4 = 16
        have cert : (tables 9).mul 1 4 = 240 := FiniteTable.LowProducts.v1_4 (tables 9)
        calc
          (tables 5).mul 1 4 = (tables 9).mul 1 4 % 2 ^ 5 :=
            ((tables 9).projection (tables 5) (Nat.pow_dvd_pow 2 (by decide : 5 ≤ 9)) 1 4).symm
          _ = 240 % (2 ^ 5) := congrArg (fun z : Nat => z % 2 ^ 5) cert
          _ = 16 := by decide
      have later := image_distance H 1 2 252
      rw [hz] at later
      exact later
    · have hdiv : 2 ^ 1 ∣ r + 1 := Nat.dvd_of_mod_eq_zero (by change (r+1) % 2 = 0; omega)
      have floor := extra_bit_after_ones H (p := 1) (w := 254) hdiv (by change 2 ≤ r; omega)
        (Nat.lt_trans short (Nat.pow_lt_pow_succ (by decide : 1 < 2)))
      exact floor
  have exceeds : 257 ≤ targetIndex := Nat.le_trans (by decide : 257 ≤ 2 ^ 9)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 9 ≤ 2048))
  have zero := geometric_row_zero tables targetIndex 256 256 (by decide) exceeds (Nat.le_of_eq targetIndex_eq)
  have prior := (numeral_zero_iff H (2 ^ 256 - 3) targetIndex 256).mp ((canonical_mul _ _ _).symm.trans zero)
  exact Nat.le_trans prior (index_mono (numeral_total H _) enough)

#print axioms ones_shift_of_boundary
#print axioms odd_outer_floor
end Gamma11
