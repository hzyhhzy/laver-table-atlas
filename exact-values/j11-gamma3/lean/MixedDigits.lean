import NativeSixteen

/-! High binary digits in the width-16 mixed-block induction. Changing
the low sixteen bits leaves this condition invariant. A nonzero product
in that low window retains every higher one-bit of the acting row. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

def Dense16 (a : Nat) : Prop := zeroDigits a 256≤zeroDigits a 16+224
def Incomplete16 (a : Nat) : Prop := Dense16 a ∧ ¬FullBitBlock a 16 256

private theorem compare_zeros {p n a b : Nat} (pn : p≤n)
    (cover : ∀ i, p≤i → i<n → b%2^(i+1)<2^i → a%2^(i+1)<2^i) :
    zeroDigits b n+zeroDigits a p≤zeroDigits a n+zeroDigits b p := by
  induction n with
  | zero => have eqv : p=0 := by omega
            subst p; omega
  | succ n ih =>
    by_cases start : p=n+1
    · subst p; omega
    · have prev := ih (by omega) (fun i lo hi => cover i lo (by omega))
      simp only [zeroDigits]
      by_cases bz : b%2^(n+1)<2^n
      · rw [if_pos bz,if_pos (cover n (by omega) (Nat.lt_succ_self n) bz)]; omega
      · rw [if_neg bz]; split <;> omega

theorem dense16_inherited {m a b : Nat} (room : 256≤m) (dense : Dense16 a)
    (nz : (tables m).mul a b%2^16≠0) : Dense16 ((tables m).mul a b) := by
  let z := (tables m).mul a b
  have cover (i : Nat) (low : 16≤i) (hi : i<256) (zero : z%2^(i+1)<2^i) : a%2^(i+1)<2^i := by
    have ne : z%2^(i+1)≠0 := by
      intro h
      have p := Nat.mod_mod_of_dvd z (Nat.pow_dvd_pow 2 (show 16≤i+1 by omega))
      rw [h,Nat.zero_mod] at p; exact nz p.symm
    exact Nat.lt_trans (left_residue_lt tables (a:=a) (b:=b) (by omega : i+1≤m) ne) zero
  have h := compare_zeros (by decide : 16≤256) cover
  change zeroDigits z 256≤zeroDigits z 16+224
  unfold Dense16 at dense; omega

private theorem aligned_lt_add {x y u b : Nat} (dx : u ∣ x) (dy : u ∣ y) (small : b<u) :
    x+b<y ↔ x<y := by
  constructor
  · omega
  · intro less
    have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt less) (Nat.dvd_sub dy dx)
    omega

theorem aligned_add_residue {a p n b : Nat} (pn : p≤n) (div : 2^p ∣ a) (small : b<2^p) :
    (a+b)%2^n=a%2^n+b ∧ 2^p ∣ a%2^n := by
  have span := Nat.pow_dvd_pow 2 pn
  have rem : 2^p ∣ a%2^n := Nat.dvd_of_mod_eq_zero ((Nat.mod_mod_of_dvd a span).trans (Nat.mod_eq_zero_of_dvd div))
  have fits := (aligned_lt_add rem span small).2 (Nat.mod_lt a (Nat.two_pow_pos _))
  have narrow := Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0<2) pn)
  exact ⟨by rw [Nat.add_mod,Nat.mod_eq_of_lt narrow,Nat.mod_eq_of_lt fits],rem⟩

private theorem dense_of_cover {a b : Nat}
    (cover : ∀ i, 16≤i → i<256 → b%2^(i+1)<2^i → a%2^(i+1)<2^i)
    (h : Dense16 a) : Dense16 b := by
  have cmp := compare_zeros (by decide : 16≤256) cover
  unfold Dense16 at h ⊢; omega

theorem mixed_aligned_add {a i : Nat} (align : 2^16 ∣ a) (small : i<65536) :
    Incomplete16 (a+i) ↔ Incomplete16 a := by
  have same (j : Nat) (low : 16≤j) : (a+i)%2^(j+1)<2^j ↔ a%2^(j+1)<2^j := by
    obtain ⟨eqv,div⟩ := aligned_add_residue (by omega : 16≤j+1) align small
    rw [eqv]; exact aligned_lt_add div (Nat.pow_dvd_pow 2 low) small
  have missing : (¬FullBitBlock (a+i) 16 256) ↔ ¬FullBitBlock a 16 256 := by
    obtain ⟨eqv,div⟩ := aligned_add_residue (by decide : 16≤256) align small
    have target : 2^16 ∣ 2^256-2^16 := Nat.dvd_sub (Nat.pow_dvd_pow 2 (by decide : 16≤256)) (Nat.dvd_refl _)
    unfold FullBitBlock
    rw [eqv]
    have c := aligned_lt_add div target small
    omega
  constructor
  · intro ⟨dense,notFull⟩
    exact ⟨dense_of_cover (fun j lb _ => (same j lb).mpr) dense,missing.mp notFull⟩
  · intro ⟨dense,notFull⟩
    exact ⟨dense_of_cover (fun j lb _ => (same j lb).mp) dense,missing.mpr notFull⟩

theorem mixed_congr_256 {a b : Nat} (same : a%2^256=b%2^256) :
    Incomplete16 a ↔ Incomplete16 b := by
  have eqv (i : Nat) (hi : i<256) := residue_agree_lower same (show i+1≤256 by omega)
  have missing : (¬FullBitBlock a 16 256) ↔ ¬FullBitBlock b 16 256 := by
    unfold FullBitBlock; rw [same]
  exact ⟨fun ⟨h,n⟩ => ⟨dense_of_cover (fun i _ hi v => (eqv i hi).symm ▸ v) h,missing.mp n⟩,
    fun ⟨h,n⟩ => ⟨dense_of_cover (fun i _ hi v => (eqv i hi) ▸ v) h,missing.mpr n⟩⟩

#print axioms dense16_inherited
#print axioms mixed_aligned_add
#print axioms mixed_congr_256
end Gamma11
