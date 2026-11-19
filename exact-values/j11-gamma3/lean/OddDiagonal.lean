import EndpointAssembly

/-! Only the corner decompositions of the odd old columns need to be
    supplied. The even-column residues and additions, the absence of a
    wrap at the old degree, and positivity at the midpoint are derived. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

/-- Projection of the entire geometric row to degree N. -/
theorem geometric_parity (F : BinaryFamily) {N t : Nat} (two : 2 ≤ N) (within : N ≤ t) (r : Nat) :
    (F t).mul (2^N-3) r % 2^N = if r%2=0 then 0 else 2^N-2 := by
  let g := 2^N-3
  have big : 4 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0 < 2) two
  have zero : (F N).mul g 2 = 0 := by
    have proj := (F (N+1)).projection (F N) (Nat.pow_dvd_pow 2 (Nat.le_succ N)) g 2
    change (F (N+1)).mul (2^N-3) 2 % 2^N = _ at proj
    rwa [row_minus_three_at_two F N two, Nat.mod_self, eq_comm] at proj
  change (F t).mul g r % 2^N = _
  rw [(F t).projection (F N) (Nat.pow_dvd_pow 2 within), (F N).reduce_period zero]
  by_cases even : r%2=0
  · rw [even, if_pos rfl, (F N).mul_zero]
  · have odd : r%2=1 := by omega
    rw [if_neg even, odd, (F N).mul_one, Nat.mod_eq_of_lt (by dsimp [g]; omega)]
    dsimp [g]; omega

private theorem aligned_room {q a cap : Nat} (divA : q ∣ a) (divCap : q ∣ cap)
    (below : a < cap) : a+q ≤ cap := by
  obtain ⟨i,rfl⟩ := divA
  obtain ⟨j,rfl⟩ := divCap
  have lt := Nat.lt_of_mul_lt_mul_left below
  simpa only [Nat.mul_succ] using Nat.mul_le_mul_left q (Nat.succ_le_of_lt lt)

/-- The data of two successive corners at the old degree, only for odd
    r; the midpoint itself need not occur in the inputs. -/
def OddCornersAt (t : Nat) : Prop := ∀ r, 1 ≤ r → r < midpointColumn → r%2=1 →
  ∀ i, 1 ≤ i → i ≤ geometricRow →
    ∃ c : SliceCorners t 256 (oldEntry t geometricRow r) i,
      c.p+c.w ≤ t ∧ ∃ m : Nat, 0 < m ∧ c.w=256^m

abbrev OddDiagonalCorners : Prop := OddCornersAt targetIndex

theorem old_diagonal_at_of_odd_corners {t : Nat} (Nle : 256 ≤ t)
    (H : FirstRowUnbounded) (boundary : BlockBoundary H)
    (guard : ∀ A, 0 < A → A < 2^t → 2^256 ∣ A → ∀ b, 1 ≤ b → b ≤ geometricRow → t < image H (A+b) 256)
    (corners : OddCornersAt t) : OldDiagonalAt t := by
  let g := geometricRow
  let P := 2^256
  let col := oldEntry t g
  have divCap : P ∣ 2^t := Nat.pow_dvd_pow 2 Nle
  have pbig : 4 ≤ P := Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 2 ≤ 256)
  have gval : g=P-3 := rfl
  have gpos : 1 ≤ g := by omega
  have below (r : Nat) : col r < 2^t := (tables t).mul_lt g r
  have shadow (r : Nat) : col r % P = if r%2=0 then 0 else P-2 :=
    geometric_parity tables (by decide) Nle r
  have ones : OnesRowShift H := ones_shift_of_boundary H boundary
  have evenStep (r : Nat) (even : r%2=0) (pos : 0 < col r) :
      P ∣ col r ∧ col (r+1) = col r + (g+1) := by
    have div := Nat.dvd_of_mod_eq_zero ((shadow r).trans (if_pos even))
    have room := aligned_room div divCap (below r)
    have protect (v : Nat) (lo : 2 ≤ v) (hi : v ≤ g+1) :
        t ≤ image H (col r + 2^0*v-1) 256 := by
      rw [show col r + 2^0*v-1 = col r+(v-1) by simp; omega]
      exact Nat.le_of_lt (guard (col r) pos (below r) div (v-1) (by omega) (by omega))
    have h := aligned_block_prefix H boundary ones (d := t) (p := 0)
      (show IsDyadic 256 from ⟨8, by decide⟩) (Nat.dvd_zero 256)
      (show 2^(0+256) ∣ col r from div) (Nat.zero_lt_succ g) protect
    have small : col r + (g+1) < 2^t := by omega
    have value : (tables t).mul (col r) (g+1) = col r+(g+1) := by
      simpa only [Nat.pow_zero, Nat.one_mul, Nat.add_one_sub_one, Nat.mod_eq_of_lt small] using h
    exact ⟨div, ((tables t).row_recurrence g r).trans value⟩
  have oddSmall (r : Nat) (odd : r%2=1) : col r+1 < 2^t := by
    have low := shadow r
    rw [if_neg (by omega : r%2≠0)] at low
    have h := below r
    apply Nat.lt_of_not_ge
    intro full
    have m := congrArg (fun v => v % P) (show col r+1=2^t by omega)
    change (col r+1)%P = (2^t)%P at m
    rw [Nat.add_mod, low, Nat.mod_eq_of_lt (by omega : 1 < P),
      Nat.mod_eq_of_lt (by omega : P-2+1 < P), Nat.mod_eq_zero_of_dvd divCap] at m
    omega
  have positive (r : Nat) (lo : 1 ≤ r) (hi : r ≤ midpointColumn) : 0 < col r := by
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases zero : r=0
      · subst r
        have room : P ≤ 2^t := Nat.pow_le_pow_right (by decide : 0 < 2) Nle
        change 0 < (tables t).mul g 1
        rw [(tables t).mul_one, Nat.mod_eq_of_lt (by omega)]
        omega
      · have prev := ih (by omega) (by omega)
        by_cases even : r%2=0
        · rw [(evenStep r even prev).2]; omega
        · have odd : r%2=1 := by omega
          obtain ⟨c,_,_⟩ := corners r (by omega) (by omega) odd g gpos (Nat.le_refl _)
          change 0 < (tables t).mul g (r+1)
          rw [(tables t).row_recurrence]
          change 0 < oldEntry t (col r) (g+1)
          rw [c.finish]
          have width : 4 ≤ 2^c.w := Nat.pow_le_pow_right (by decide : 0 < 2) c.width_two
          exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos c.p) (by omega)) (Nat.le_add_left ..)
  refine ⟨positive midpointColumn (Nat.two_pow_pos _) (Nat.le_refl _), ?_⟩
  intro r lo hi
  have prev := positive r lo (Nat.le_of_lt hi)
  by_cases even : r%2=0
  · exact Or.inl ⟨prev,evenStep r even prev⟩
  · have odd : r%2=1 := by omega
    exact Or.inr ⟨oddSmall r odd,odd,corners r lo hi odd⟩

theorem old_diagonal_of_odd_corners (H : FirstRowUnbounded) (boundary : BlockBoundary H)
    (est : WidthEstimates H) (corners : OddDiagonalCorners) : OldDiagonal :=
  old_diagonal_at_of_odd_corners (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 8 ≤ 2048))
    H boundary est.background corners

theorem target_of_odd_corners (H : FirstRowUnbounded) (blocks : FiniteBlockLaw)
    (est : WidthEstimates H) (corners : OddDiagonalCorners)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow) : Target := by
  have boundary : BlockBoundary H := (finite_block_iff_boundary H).mp blocks
  exact target_of_old_diagonal H boundary (old_diagonal_of_odd_corners H boundary est corners) est nf

#print axioms old_diagonal_of_odd_corners
#print axioms target_of_odd_corners
end Gamma11
