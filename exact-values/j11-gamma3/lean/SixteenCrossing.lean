import DiagonalHom
import LaverLowerBounds.StandardLine

/-! The critical-point-four estimate propagates through every position
up to 15. The first bridge (4,8,16) needs the fourth image of row 14;
the other three are the already-proved dyadic anchors. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem stretch_action_at_degree {w n i m : Nat} (wp : 0<w) (inside : i<n) (room : n*w ≤ m)
    (hom : StretchHomAt w n) : act tables m (2^w-2) i = i*w := by
  have small : i*w < (i+1)*w := by rw [Nat.succ_mul]; omega
  have fits : (i+1)*w ≤ n*w := Nat.mul_le_mul_right w inside
  have strict := Nat.lt_of_lt_of_le small fits
  have row := stretch_row wp (show 0<n by omega) hom (2^i) (Nat.pow_lt_pow_right (by decide) inside)
  rw [repeatBits_single _ _ _ inside] at row
  have action : act tables (n*w) (2^w-2) i = i*w :=
    (congrArg (signature (n*w)) row).trans (dyadic_tail_signature _ _ _ small fits)
  have projected := act_at_smaller_degree tables room (2^w-2) i
  rw [action] at projected
  omega

def SixteenBridge (m α β c : Nat) : Prop :=
  signature m c=α ∧ act tables m c α=β ∧ act tables m c β=16

/-- The only two observations about row 65534 used in the target
normal form. They can be proved at degrees 256 and 257. -/
structure SixteenRowData : Prop where
  action : ∀ {m i : Nat}, 272≤m → i<17 → act tables m 65534 i=i*16
  square : (tables 256).mul 65534 65534=2^256-2^16

theorem bridges_above_four {m r : Nat} (room : 20 ≤ m) (lo : 4<r) (hi : r<16) (four : act tables m 14 4=16) :
    ∃ α β c, 4≤α ∧ α<r ∧ r≤β ∧ SixteenBridge m α β c := by
  have anchors := dyadic_anchors tables 4 m (by omega)
  by_cases first : r≤8
  · have one := act_from_low tables m 14 1 _ 4 (by omega) (LowProducts.v14_2 _) (by decide) (by decide)
    have two := act_from_low tables m 14 2 _ 8 (by omega) (LowProducts.v14_4 _) (by decide) (by decide)
    have b1 := act_from_low tables m 2 1 _ 2 (by omega) (LowProducts.v2_2 _) (by decide) (by decide)
    have b2 := act_from_low tables m 2 2 _ 4 (by omega) (LowProducts.v2_4 _) (by decide) (by decide)
    have sig2 : signature m 2=1 := dyadic_tail_signature m 2 1 (by decide) (by omega)
    have sig := signature_mul tables m 14 2
    have a := act_application tables m 14 2 1
    have b := act_application tables m 14 2 2
    rw [sig2,one] at sig
    rw [one,b1,two] at a
    rw [two,b2,four] at b
    exact ⟨4,8,_,Nat.le_refl _,lo,first,sig,a,b⟩
  by_cases second : r≤12
  · obtain ⟨c,h⟩ := anchors 2 (by decide)
    exact ⟨8,12,c,by decide,by omega,second,h⟩
  by_cases third : r≤14
  · obtain ⟨c,h⟩ := anchors 1 (by decide)
    exact ⟨12,14,c,by decide,by omega,third,h⟩
  · obtain ⟨c,h⟩ := anchors 0 (by decide)
    exact ⟨14,15,c,by decide,by omega,by omega,h⟩

/-- The second conclusion of Appendix B.2 at a fixed finite degree. -/
theorem critical_four_to_fifteen {m N : Nat} (room : 20 ≤ m) (large : 16≤N)
    (four_image : act tables m 14 4=16)
    (atFour : ∀ a, signature m a=4 → N ≤ act tables m a 4 → act tables m a N=m)
    (r a : Nat) (lower : 4≤r) (upper : r<16) (critical : signature m a=r)
    (jump : N ≤ act tables m a r) : act tables m a N=m := by
  induction r using Nat.strongRecOn generalizing a with
  | ind r ih =>
    by_cases four : r=4
    · rw [four] at critical jump
      exact atFour a critical jump
    obtain ⟨α,β,c,start,before,after,sig,first,last⟩ := bridges_above_four room (by omega) upper four_image
    let z := (tables m).mul a c
    have fixed := fixes_below_signature tables m a α (critical ▸ before)
    have zsig : signature m z=α := (signature_mul tables m a c).trans (sig ▸ fixed)
    have z0 := act_application tables m a c α
    have z1 := act_application tables m a c β
    rw [fixed,first] at z0
    rw [last] at z1
    have high := Nat.le_trans jump (act_mono tables m a after)
    have saturated := ih α before z start (by omega) zsig (z0.symm ▸ high)
    have moved := act_mono tables m z high
    rw [saturated] at moved
    have lower16 : m ≤ act tables m a 16 := Nat.le_trans moved (Nat.le_of_eq z1)
    exact Nat.le_antisymm (act_le ..) (Nat.le_trans lower16 (act_mono tables m a large))

#print axioms critical_four_to_fifteen
end Gamma11
