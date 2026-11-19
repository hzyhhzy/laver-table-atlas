import DiagonalHom

/-! Induction over the widths 256^m in the period estimate. Uniform
    blocks descend to a smaller exponent, with the exact range of the
    auxiliary stretch recorded. -/

set_option autoImplicit false
set_option exponentiation.threshold 512
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem repeatBits_padding (v n h x : Nat) (nh : n ≤ h) (fits : x < 2^n) :
    repeatBits v h x = repeatBits v n x := by
  induction n generalizing h x with
  | zero =>
    have e : x=0 := by simp at fits; omega
    rw [e,repeatBits_zero,repeatBits_zero]
  | succ n ih =>
    cases h with
    | zero => omega
    | succ h =>
      simp only [repeatBits]
      rw [ih h (x/2) (by omega) (by rw [Nat.pow_succ] at fits; omega)]

/-- A zero at 2^x in the source gives a zero at 2^(vx) in the
    stretched table. Its image argument itself has valuation vx. -/
theorem stretch_period_zero {v n u x : Nat} (vp : 0<v) (hom : StretchHomAt v n)
    (fit : u<2^n) (xn : x<n) (z : entry n u (2^x)=0) :
    entry (n*v) (repeatBits v n u) (2^(x*v))=0 := by
  have hx : 2^x < 2^n := Nat.pow_lt_pow_right (by decide) xn
  have h := hom u (2^x) fit hx
  rw [canonical_mul,z, repeatBits_zero] at h
  have ls : x*v < (x+1)*v := by rw [Nat.succ_mul]; omega
  have sn : (x+1)*v ≤ n*v := Nat.mul_le_mul_right _ xn
  have sig : signature (n*v) (repeatBits v n (2^x))=x*v := by
    rw [repeatBits_single _ _ _ xn]; exact dyadic_tail_signature _ _ _ ls sn
  have action := signature_mul tables (n*v) (repeatBits v n u) (repeatBits v n (2^x))
  rw [← h, signature_zero,sig] at action
  rw [← canonical_mul]
  exact (le_act_iff tables _ _ (x*v) _ (Nat.le_refl _)).mp (Nat.le_of_eq action)

/-- Only the source degrees bounded by the repeated block width are
    needed in the homogeneous branch. The exponent b is a power of two. -/
def AuxiliaryStretches : Prop := ∀ b, IsDyadic b → ∀ n, n ≤ 256^b → StretchHomAt (256^b) n

/-- The outstanding case is a word with at least one mixed v-bit block.
    A word made entirely of zero or full blocks is exactly a repeated
    word of the form in the negated existential. -/
def MixedShortPeriods : Prop := ∀ m, 0<m →
  let b := 2^m.log2
  let v := 256^b
  let k := 256^(m-b)
  ∀ x, 1 ≤ x → x < 2^(256^m)-2 →
    (¬ ∃ u, u<2^k ∧ x=repeatBits v k u) →
    entry (256*256^m) x (2^(256^m))=0

/-- Include the penultimate small row for use by the descent. Its
    value follows from the ordinary licensed stretch at degree 257. -/
theorem short_period_induction_with_last (aux : AuxiliaryStretches) (mixed : MixedShortPeriods)
    (finalRow : ∀ m, 0<m → entry (256*256^m) (2^(256^m)-2) (2^(256^m))=0) :
    ∀ m, 0<m → ∀ x, 1 ≤ x → x ≤ 2^(256^m)-2 →
    entry (256*256^m) x (2^(256^m))=0 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro mp x positive upper
    let b := 2^m.log2
    let v := 256^b
    let k := 256^(m-b)
    let w := 256^m
    have bpos : 0<b := Nat.two_pow_pos _
    have bm : b ≤ m := Nat.log2_self_le (by omega)
    have small := Nat.lt_log2_self (n := m)
    rw [Nat.pow_succ] at small
    change m < b*2 at small
    have width : k*v=w := by
      dsimp [k,v,w]; rw [← Nat.pow_add, Nat.sub_add_cancel bm]
    have degree : (256*k)*v = 256*w := by rw [Nat.mul_assoc,width]
    have vpos : 0<v := Nat.pow_pos (by decide : 0<256)
    have kp : 0<k := Nat.pow_pos (by decide : 0<256)
    by_cases last : x=2^w-2
    · subst x
      exact finalRow m mp
    · have interior : x < 2^w-2 := by change x≤2^w-2 at upper; omega
      by_cases uniform : ∃ u, u < 2^k ∧ x=repeatBits v k u
      · obtain ⟨u,fit,rfl⟩ := uniform
        have up : 1 ≤ u := by
          apply Nat.le_of_not_gt
          intro fail
          have eqv : u=0 := by omega
          rw [eqv,repeatBits_zero] at positive
          omega
        have uBound : u ≤ 2^k-2 := by
          apply Nat.le_of_not_gt
          intro larger
          have pos := Nat.two_pow_pos k
          have eqv : u=2^k-1 := by omega
          rw [eqv,repeatBits_last,width] at interior
          omega
        have mb : 0 < m-b := by
          apply Nat.lt_of_not_ge
          intro no
          have eqv : m-b=0 := by omega
          have one : k=1 := by dsimp [k]; rw [eqv]
          rw [one] at uBound
          omega
        have smaller : m-b < m := by omega
        have previous := ih (m-b) smaller mb u up uBound
        have permitted : 256*k ≤ v := by
          change 256*256^(m-b) ≤ 256^b
          rw [Nat.mul_comm,← Nat.pow_succ]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        have nk : k < 256*k := by omega
        have good := stretch_period_zero vpos (aux b ⟨m.log2,rfl⟩ (256*k) permitted)
          (Nat.lt_trans fit (Nat.pow_lt_pow_right (by decide) nk)) nk previous
        rw [repeatBits_padding v k (256*k) u (Nat.le_of_lt nk) fit,degree,width] at good
        exact good
      · exact mixed m mp x positive interior uniform

theorem short_period_induction (aux : AuxiliaryStretches) (mixed : MixedShortPeriods)
    (licensed : LicensedStretches) : ∀ m, 0<m → ∀ x, 1 ≤ x → x ≤ 2^(256^m)-2 →
    entry (256*256^m) x (2^(256^m))=0 := by
  apply short_period_induction_with_last aux mixed
  intro m mp
  let w := 256^m
  have wp : 0<w := Nat.pow_pos (by decide : 0<256)
  have tableRow := stretch_row wp (by decide : 0<257) (licensed m mp 257 (Or.inr rfl))
    (2^256) (Nat.pow_lt_pow_succ (by decide))
  rw [repeatBits_single _ _ _ (by decide : 256<257)] at tableRow
  have strict : 256*w < 257*w := by omega
  have sig := dyadic_tail_signature (257*w) (257*w) (256*w) strict (Nat.le_refl _)
  have actVal : act tables (257*w) (2^w-2) 256 = 256*w := by
    unfold act; rw [tableRow]; exact sig
  have wge : 256 ≤ w := calc
    256 = 256^1 := by decide
    _ ≤ w := Nat.pow_le_pow_right (by decide) mp
  have zeroAtDegree := (le_act_iff tables (257*w) (2^w-2) w (256*w) (Nat.le_of_lt strict)).mp
    (Nat.le_trans (Nat.le_of_eq actVal.symm) (act_mono tables _ _ wge))
  exact (canonical_mul _ _ _).symm.trans zeroAtDegree

#print axioms short_period_induction
/-- An alternative constructor for the three guards: only the mixed
    interior rows remain to be established in the short-period argument. -/
theorem period_guards_of_mixed
    (native : ∀ b, 1 ≤ b → b < geometricRow → entry targetIndex b (2^256)=0)
    (background : ∀ A, 0<A → A<2^targetIndex → 2^256 ∣ A → ∀ b,
      1 ≤ b → b < geometricRow → entry (targetIndex+1) (A+b) (2^256)=0)
    (aux : AuxiliaryStretches) (mixed : MixedShortPeriods) (licensed : LicensedStretches) : PeriodGuards where
  native := native
  background := background
  short m hm b lo hi := short_period_induction aux mixed licensed m hm b lo (Nat.le_of_lt hi)

#print axioms period_guards_of_mixed
end Gamma11
