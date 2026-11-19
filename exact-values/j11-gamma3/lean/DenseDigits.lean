import WideCrossing

/-! The counting step of Appendix D.1 for any width. A transported
row produces b distinct zero digits in each gap. Counting all these
gaps at once avoids separating digits below and above the final image. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- Number of zero digits among binary positions 0 through n-1,
including leading zeros. -/
def zeroDigits (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => zeroDigits a n + if a%2^(n+1)<2^n then 1 else 0

private theorem zeros_mono (a : Nat) {i j : Nat} (leq : i≤j) : zeroDigits a i≤zeroDigits a j := by
  induction j with
  | zero =>
    have h : i=0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases stop : i=j+1
    · rw [stop]; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right ..)

private theorem gap_zeros (F : BinaryFamily) {m a i b : Nat} (pos : 0<i)
    (zero : act F m a 0=0) (one : act F m a 1=b) (visible : act F m a (i+1)<m) :
    zeroDigits a (act F m a i)+b ≤ zeroDigits a (act F m a (i+1)) := by
  let c := 2^i-1
  let w := (F m).mul a c
  have ii : i+1<m := by
    apply Nat.lt_of_not_ge
    intro above
    have k := Nat.le_trans (le_act F m a m (Nat.le_refl _)) (act_mono F m a above)
    omega
  obtain ⟨c0,c1⟩ := adjacent_pair F m i (by omega)
  have cs : signature m c=0 := dyadic_tail_signature m i 0 pos (by omega)
  have ws : signature m w=0 := (signature_mul F m a c).trans (cs ▸ zero)
  have w0 := act_application F m a c 0
  have wb := act_application F m a c 1
  rw [zero,c0] at w0
  rw [one,c1] at wb
  change act F m w 0=act F m a i at w0
  change act F m w b=act F m a (i+1) at wb
  have wbvis : act F m w b<m := Nat.lt_of_le_of_lt (Nat.le_of_eq wb) visible
  have count (k : Nat) (kb : k≤b) : zeroDigits a (act F m w 0)+k≤zeroDigits a (act F m w k) := by
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      let y := act F m w k
      have vk := Nat.lt_of_le_of_lt (act_mono F m w (show k≤b by omega)) wbvis
      have vn := Nat.lt_of_le_of_lt (act_mono F m w kb) wbvis
      have past := act_strict_below_cap F m w k (k+1) (Nat.lt_succ_self _) vn
      have cut : y+1≤m := vk
      have nz : w%2^(y+1)≠0 := by
        intro bad
        have hs := (le_signature m w (y+1) cut).mpr bad
        rw [ws] at hs; omega
      have domination := left_residue_lt F (a:=a) (b:=c) cut nz
      have position := Nat.lt_trans domination (act_residue_lt F m w k vk)
      change a%2^(y+1)<2^y at position
      have step := zeros_mono a (show y+1 ≤ act F m w (k+1) from past)
      rw [zeroDigits,if_pos position] at step
      exact Nat.le_trans (Nat.succ_le_succ (ih (by omega))) step
  have result := count b (Nat.le_refl _)
  rwa [w0,wb] at result

theorem accumulated_zeros (F : BinaryFamily) {m a b : Nat}
    (zero : act F m a 0=0) (one : act F m a 1=b) (i : Nat) (positive : 1≤i)
    (visible : act F m a i<m) :
    zeroDigits a b+(i-1)*b ≤ zeroDigits a (act F m a i) := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases first : i=0
    · subst i; simpa only [one,Nat.sub_self,Nat.zero_mul,Nat.add_zero] using Nat.le_refl (zeroDigits a b)
    · have bound := ih (by omega) (Nat.lt_of_le_of_lt (act_mono F m a (Nat.le_succ _)) visible)
      have gap := gap_zeros F (by omega : 0<i) zero one visible
      have eqv : (i+1-1)*b=(i-1)*b+b := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [eqv,← Nat.add_assoc]
      exact Nat.le_trans (Nat.add_le_add_right bound b) gap

/-- If at least n of the digits in [n,n²) are ones, a row fixing
position 0 and sending 1 to at least n must send n-1 to at least n².
The right side of the density assumption is the number of positions
left for zero digits after accounting for n required ones. -/
theorem dense_last_image (F : BinaryFamily) {m a n b : Nat} (width : 2≤n) (room : n*n≤m)
    (zero : act F m a 0=0) (one : act F m a 1=b) (large : n≤b)
    (dense : zeroDigits a (n*n)≤zeroDigits a n+(n-2)*n) : n*n≤act F m a (n-1) := by
  apply Nat.le_of_not_gt
  intro low
  let x := act F m a (n-1)
  have visible := Nat.lt_of_lt_of_le low room
  have count := accumulated_zeros F zero one (n-1) (by omega) visible
  have bit := act_residue_lt F m a (n-1) visible
  change a%2^(x+1)<2^x at bit
  have extra := zeros_mono a (show x+1≤n*n from low)
  rw [zeroDigits,if_pos bit] at extra
  have zlo := zeros_mono a large
  have blo := Nat.mul_le_mul_left (n-2) large
  rw [show n-1-1=n-2 by omega] at count
  change zeroDigits a b+(n-2)*b≤zeroDigits a x at count
  omega

#print axioms accumulated_zeros
#print axioms dense_last_image

/-- The dense terminal estimate in D.1, independent of the subsequent
downward induction on row residues and of the size of the target cap. -/
theorem dense_terminal (F : BinaryFamily) {m n a h : Nat} (width : 2≤n) (room : n*n≤m)
    (bridges : UpperBridges F m n)
    (guard : ∀ r z, n≤r → r<n*n → signature m z=r → n*n≤act F m z r → h≤act F m z (n*n))
    (word : a%2^n=2^n-2) (small : act F m a 1<n*n)
    (dense : zeroDigits a (n*n)≤zeroDigits a n+(n-2)*n) : h≤act F m a n := by
  let f := act F m a
  have nw : n≤n*n := by
    have cmp := Nat.mul_le_mul_left n (show 1≤n by omega)
    rwa [Nat.mul_one] at cmp
  obtain ⟨sig,jump⟩ := first_move_from_run F (s:=1) (by omega : 1<n) (Nat.le_trans nw room) word
  have zero := fixes_below_signature F m a 0 (by omega)
  have endp := dense_last_image F width room zero rfl jump dense
  obtain ⟨r,short,hit,before⟩ := least_bounded_hit (P:=fun i => n*n≤f i) (n-1) endp
  have rp : 1<r := by
    apply Nat.lt_of_not_ge; intro r1
    have low := act_mono F m a r1
    change f r≤f 1 at low
    change f 1<n*n at small; omega
  obtain ⟨α,β,c,positive,left,right,cs,c1,c2⟩ := bridges r rp (by omega)
  let z := (F m).mul a c
  have hz : signature m z=f α := (signature_mul F m a c).trans (congrArg f cs)
  have z1 := act_application F m a c α
  have z2 := act_application F m a c β
  rw [c1] at z1
  rw [c2] at z2
  have low := Nat.le_trans jump (act_mono F m a positive)
  have high := Nat.le_trans hit (act_mono F m a right)
  have bound := guard (f α) z low (Nat.lt_of_not_ge (before α left)) hz (z1.symm ▸ high)
  exact Nat.le_trans bound (Nat.le_trans (act_mono F m z high) (Nat.le_of_eq z2))

#print axioms dense_terminal
end Gamma11
