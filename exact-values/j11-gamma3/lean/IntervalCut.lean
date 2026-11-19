import DiagonalDigits

/-! Cutting an interval word at its kth marked position discards
exactly the source digits numbered k and higher. -/
set_option autoImplicit false
namespace Gamma11

private theorem intervalWord_decompose {f : Nat → Nat} (mono : ∀ i j, i≤j → f i≤f j)
    (k s n x : Nat) (kn : k≤n) : ∃ z,
    intervalWord f s n x = intervalWord f s k (x%2^k) + 2^(f (s+k))*z := by
  induction k generalizing s n x with
  | zero =>
    obtain ⟨z,hz⟩ := intervalWord_dvd f mono s n x
    exact ⟨z,by simpa only [intervalWord,Nat.zero_add,Nat.add_zero] using hz⟩
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨z,hz⟩ := ih (s+1) n (x/2) (by omega)
      have same : (x%2^(k+1))%2=x%2 := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 1≤k+1 by omega))
      have half : (x%2^(k+1))/2=(x/2)%2^k := by rw [Nat.pow_succ,Nat.mod_mul_left_div_self]
      refine ⟨z,?_⟩
      rw [intervalWord,intervalWord,half,same,hz,show s+(k+1)=s+1+k by omega]
      exact (Nat.add_assoc ..).symm

theorem intervalWord_cut {f : Nat → Nat} (mono : ∀ i j, i≤j → f i≤f j)
    (s k n x : Nat) (kn : k≤n) :
    intervalWord f s n x % 2^(f (s+k)) = intervalWord f s k (x%2^k) := by
  obtain ⟨z,hz⟩ := intervalWord_decompose mono k s n x kn
  have bound := intervalWord_bound mono s k (x%2^k)
  have pos := Nat.two_pow_pos (f s)
  rw [hz,Nat.add_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt (show intervalWord f s k (x%2^k)<2^(f (s+k)) by omega)]

end Gamma11
