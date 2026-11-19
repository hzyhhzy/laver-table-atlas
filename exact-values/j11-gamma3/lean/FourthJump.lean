import FullBlockFour

/-! The unrestricted fourth-image bound from Appendix B.3. At critical
positions 2 and 3 there is no condition on the high binary digits. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem one_four {m c b : Nat} (room : 256≤m) (start : act tables m c 0=1)
    (one : act tables m c 1=b) (large : 4≤b) : 256≤act tables m c b := by
  apply Nat.le_trans _ (act_mono tables m c large)
  by_cases visible : act tables m c 4<m
  · have h := exponential_growth tables m c 4 start visible
    rw [one] at h
    exact Nat.le_trans (Nat.pow_le_pow_left large 4) h
  · omega

private theorem two_four {m z b : Nat} (room : 256≤m) (z0 : act tables m z 0=2)
    (z1 : act tables m z 1=b) (large : 4≤b) : 256≤act tables m z 2 := by
  let s := (tables m).mul z 1
  let t := (tables m).mul s 1
  have j0 := act_from_low tables m 1 0 _ 1 (by omega) (LowProducts.v1_1 _) (by decide) (by decide)
  have j1 := act_from_low tables m 1 1 _ 2 (by omega) (LowProducts.v1_2 _) (by decide) (by decide)
  have j2 := act_from_low tables m 1 2 _ 4 (by omega) (LowProducts.v1_4 _) (by decide) (by decide)
  have sig : signature m s=2 := z0
  have s0 := fixes_below_signature tables m s 0 (by omega)
  have s1 := fixes_below_signature tables m s 1 (by omega)
  have s2 := act_application tables m z 1 0
  have sb := act_application tables m z 1 1
  rw [z0,j0,z1] at s2
  rw [z1,j1] at sb
  change act tables m s 2=b at s2
  change act tables m s b=act tables m z 2 at sb
  have t0 := act_application tables m s 1 0
  have t1 := act_application tables m s 1 1
  have tb := act_application tables m s 1 2
  rw [s0,j0,s1] at t0
  rw [s1,j1,s2] at t1
  rw [s2,j2] at tb
  exact Nat.le_trans (one_four room t0 t1 large) (Nat.le_trans (Nat.le_of_eq tb)
    (Nat.le_trans (act_mono tables m s large) (Nat.le_of_eq sb)))

private theorem at_three {m k : Nat} (room : 256≤m)
    (sig : signature m k=3) : 256≤act tables m k 4 := by
  have fix {i : Nat} (h : i<3) := fixes_below_signature tables m k i (sig ▸ h)
  have k3 := act_gt_input tables m k 3 (Nat.le_of_eq sig) (by omega)
  have g0 := act_from_low tables m 3 0 _ 2 (by omega) (LowProducts.v3_1 _) (by decide) (by decide)
  have g1 := act_from_low tables m 3 1 _ 3 (by omega) (LowProducts.v3_2 _) (by decide) (by decide)
  have g2 := act_from_low tables m 3 2 _ 4 (by omega) (LowProducts.v3_4 _) (by decide) (by decide)
  have a0 := act_application tables m k 3 0
  have a1 := act_application tables m k 3 1
  have a2 := act_application tables m k 3 2
  rw [fix (by decide : 0<3),g0,fix (by decide : 2<3)] at a0
  rw [fix (by decide : 1<3),g1] at a1
  rw [fix (by decide : 2<3),g2] at a2
  exact Nat.le_trans (two_four room a0 a1 k3) (Nat.le_of_eq a2)

theorem unspecialized_fourth_image {m k : Nat} (room : 256≤m)
    (crit : signature m k=2 ∨ signature m k=3) : 256≤act tables m k 4 := by
  rcases crit with sig|sig
  · have fix {i : Nat} (h : i<2) := fixes_below_signature tables m k i (sig ▸ h)
    have k2 := act_gt_input tables m k 2 (Nat.le_of_eq sig) (by omega)
    have j1 := act_from_low tables m 1 1 _ 2 (by omega) (LowProducts.v1_2 _) (by decide) (by decide)
    by_cases large : 4≤act tables m k 2
    · have j0 := act_from_low tables m 1 0 _ 1 (by omega) (LowProducts.v1_1 _) (by decide) (by decide)
      have j2 := act_from_low tables m 1 2 _ 4 (by omega) (LowProducts.v1_4 _) (by decide) (by decide)
      have a0 := act_application tables m k 1 0
      have a1 := act_application tables m k 1 1
      have a2 := act_application tables m k 1 2
      rw [fix (by decide : 0<2),j0,fix (by decide : 1<2)] at a0
      rw [fix (by decide : 1<2),j1] at a1
      rw [j2] at a2
      exact Nat.le_trans (one_four room a0 a1 large) (Nat.le_of_eq a2)
    · have b3 : act tables m k 2=3 := by omega
      have k3 := act_gt_input tables m k 3 (by omega) (by omega)
      let a := (tables m).mul k 3
      have g0 := act_from_low tables m 3 0 _ 2 (by omega) (LowProducts.v3_1 _) (by decide) (by decide)
      have g1 := act_from_low tables m 3 1 _ 3 (by omega) (LowProducts.v3_2 _) (by decide) (by decide)
      have g2 := act_from_low tables m 3 2 _ 4 (by omega) (LowProducts.v3_4 _) (by decide) (by decide)
      have a0 := act_application tables m k 3 0
      have a1 := act_application tables m k 3 1
      have a3 := act_application tables m k 3 2
      rw [fix (by decide : 0<2),g0,b3] at a0
      rw [fix (by decide : 1<2),g1] at a1
      rw [b3,g2] at a3
      have sigH : signature m ((tables m).mul a 1)=3 := a0
      have mid := act_application tables m a 1 1
      rw [j1] at mid
      have up := act_mono tables m ((tables m).mul a 1) (show 4≤act tables m a 1 from a1.symm ▸ k3)
      exact Nat.le_trans (at_three room sigH) (Nat.le_trans up (Nat.le_trans (Nat.le_of_eq mid)
        (Nat.le_trans (act_mono tables m a (by decide : 2≤3)) (Nat.le_of_eq a3))))
  · exact at_three room sig

#print axioms unspecialized_fourth_image
end Gamma11
