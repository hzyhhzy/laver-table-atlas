import CarryProtection

/-! Dougherty II, Lemma 6.7, derived from the right endpoint of Lemma 6.3
and the one index of the all-ones row in Lemma 6.2. All products are ordinary
finite Laver-table products. There is no large finite computation. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds TableElement

def IsDyadic (w : Nat) : Prop := ∃ b : Nat, w = 2 ^ b

/-- The two local identities of Lemma 6.3, only at its right endpoint. -/
def BlockBoundary (H : FirstRowUnbounded) : Prop := ∀ {w p X d : Nat},
  IsDyadic w → w ∣ p → 2 ^ p ∣ X → d ≤ image H (X + 2 ^ p - 1) w →
    (tables d).mul X (2 ^ p) = (X + 2 ^ p) % 2 ^ d ∧
    ((numeral X).comp (numeral (2 ^ p - 1))).rep d = (X + 2 ^ p - 1) % 2 ^ d

/-- A single, purely finite version of the right endpoint in Lemma 6.3.
    Both the composition identity and the reading of the critical index
    can be recovered from this one ordinary multiplication identity. -/
def FiniteBlockLaw : Prop := ∀ {w p X d : Nat},
  IsDyadic w → w ∣ p → 2^p ∣ X → entry d (X+2^p-1) (2^w) = 0 →
    (tables d).mul X (2^p) = (X+2^p) % 2^d

theorem finite_block_iff_boundary (H : FirstRowUnbounded) : FiniteBlockLaw ↔ BlockBoundary H := by
  constructor
  · intro law w p X d dyadic aligned divX within
    have zero := (numeral_zero_iff H (X+2^p-1) d w).mpr within
    have last := law dyadic aligned divX zero
    refine ⟨last, ?_⟩
    change (tables d).comp (X % _) ((2^p-1) % _) = _
    rw [(tables d).comp_mod_left, (tables d).comp_mod_right]
    have pp := Nat.two_pow_pos p
    have succP : 2^p-1+1 = 2^p := by omega
    have prev : X+2^p = (X+2^p-1)+1 := by omega
    rw [FiniteTable.comp, succP, last]
    have h := (tables d).predecessor_successor (X+2^p-1)
    rwa [← prev] at h
  · intro boundary w p X d dyadic aligned divX zero
    exact (boundary dyadic aligned divX ((numeral_zero_iff H _ d w).mp zero)).1

/-- The case m = w in Dougherty II, Lemma 6.2. -/
def OnesRowShift (H : FirstRowUnbounded) : Prop := ∀ {w p : Nat},
  IsDyadic w → w ∣ p → image H (2 ^ p - 1) w = p + w

theorem add_period_background {d X p B y : Nat} (divides : 2 ^ p ∣ B)
    (zero : (tables d).mul X (2 ^ p) = 0) :
    (tables d).mul X (B + y) = (tables d).mul X y := by
  obtain ⟨k, rfl⟩ := divides
  exact (tables d).periodic_multiple zero k y

/-- Truncated Lemma 6.7. Only the native rows of the intermediate values
are tested; the endpoint to be lifted does not occur among the assumptions. -/
theorem aligned_block_prefix (H : FirstRowUnbounded) (boundary : BlockBoundary H)
    (ones : OnesRowShift H) {d w p B y : Nat} (hw : IsDyadic w) (aligned : w ∣ p)
    (background : 2 ^ (p + w) ∣ B) (hy : 0 < y)
    (protectedRows : ∀ v, 2 ≤ v → v ≤ y → d ≤ image H (B + 2 ^ p * v - 1) w) :
    (tables d).mul (B + 2 ^ p - 1) y = (B + 2 ^ p * y) % 2 ^ d := by
  have positive := Nat.two_pow_pos p
  have succRow : B + 2 ^ p - 1 + 1 = B + 2 ^ p := by omega
  induction y with
  | zero => omega
  | succ v ih =>
    cases v with
    | zero => rw [(tables d).mul_one, succRow, Nat.mul_one]
    | succ v =>
      let X := B + 2 ^ p * (v + 1)
      have addX : X + 2 ^ p = B + 2 ^ p * (v + 2) := by simp only [X, Nat.mul_succ, Nat.add_assoc]
      have hdiv : 2 ^ p ∣ X := Nat.dvd_add
        (Nat.dvd_trans (Nat.pow_dvd_pow 2 (show p ≤ p + w by omega)) background) (Nat.dvd_mul_right ..)
      have high : d ≤ image H (X + 2 ^ p - 1) w := by rw [addX]; exact protectedRows _ (by omega) (Nat.le_refl _)
      obtain ⟨right, composition⟩ := boundary hw aligned hdiv high
      have rd := ((numeral X).comp (numeral (2 ^ p - 1))).finite_read (numeral (X + 2 ^ p - 1))
        (total_comp (numeral_total H X) (numeral_total H _)) (numeral_total H _) d w composition
      rw [index_comp (numeral_total H X) (numeral_total H _)] at rd
      change min d (image H X (image H (2 ^ p - 1) w)) = min d (image H (X + 2 ^ p - 1) w) at rd
      rw [ones hw aligned, Nat.min_eq_left high] at rd
      have hz : (tables d).mul X (2 ^ (p + w)) = 0 := by
        rw [canonical_mul]
        apply (numeral_zero_iff H _ _ _).mpr
        change d ≤ image H X (p + w)
        omega
      have prev := ih (by omega) (fun n hlo hhi => protectedRows n hlo (by omega))
      rw [(tables d).row_recurrence, prev, (tables d).mul_mod_left, succRow]
      exact (add_period_background background hz).trans (addX ▸ right)

#print axioms aligned_block_prefix
end Gamma11
