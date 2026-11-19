import DiagonalInduction

/-! Propagate the geometric row from degree 256^3+1 up to the old
target degree by ordinary natural-number induction. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def seedDegree : Nat := 256^3+1

theorem geometric_degree_step (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) {t : Nat}
    (start : seedDegree≤t) (stop : t<targetIndex) (old : GeometricAt t) : GeometricAt (t+1) := by
  have cap : t≤256^256 := targetIndex_eq ▸ Nat.le_of_lt stop
  obtain ⟨h,hMax,endAt,least⟩ := least_bounded_hit (P:=fun i => t≤256^i) 256 cap
  have beforeStart : 256^3<t := start
  have hMin : 4≤h := by
    apply Nat.le_of_not_gt; intro small
    have cmp := Nat.pow_le_pow_right (by decide : 0<256) (show h≤3 by omega); omega
  have previous : 256^(h-1)<t := Nat.lt_of_not_ge (least (h-1) (by omega))
  have hPrev : h-1+1=h := Nat.sub_add_cancel (by omega)
  have degree : 257≤t := Nat.le_trans (by decide : 257≤seedDegree) start
  have kr : h-1≤t := by omega
  have first := prior_geometric_period H old degree (k:=h-1) (by omega) previous (by rwa [hPrev])
  rcases Nat.eq_or_lt_of_le endAt with edge|interior
  · have middle := Nat.pow_lt_pow_right (by decide : 1<2) (show h-1<h by omega)
    have same := protect_geometric_prefix H wide old degree (Nat.le_of_lt stop) hMin hMax previous endAt
      hMax (Nat.le_of_eq edge.symm) (2^(h-1)) middle (Nat.le_refl _)
    have nz := first.2.2 (2^(h-1)) (Nat.two_pow_pos _) (Nat.pow_lt_pow_succ (by decide))
    have half : 0<(tables (t+1)).mul geometricRow (2^(h-1)) ∧ (tables (t+1)).mul geometricRow (2^(h-1))<2^t := by
      rw [same]; exact ⟨Nat.pos_of_ne_zero nz,(tables t).mul_lt ..⟩
    have up := doubled_period_lift tables kr first half
    rw [hPrev] at up
    have room : h<256 := by
      apply Nat.lt_of_not_ge; intro big
      have eqv : h=256 := by omega
      rw [eqv,←targetIndex_eq] at edge; omega
    apply geometric_step_from_bit old up room (Nat.le_of_eq edge.symm)
    rw [edge]; exact Nat.pow_lt_pow_succ (by decide)
  · have zero := geometric_row_zero tables (t+1) 256 h (by decide) (by omega) interior
    have lifts := stable_period_lift tables kr first (hPrev.symm ▸ zero) (by
      intro j small
      have same := protect_geometric_prefix H wide old degree (Nat.le_of_lt stop) hMin hMax previous endAt
        (k:=h-1) (by omega) (Nat.le_of_lt previous) j small (Nat.le_of_lt small)
      rw [same]; exact (tables t).mul_lt ..)
    apply geometric_step_from_bit old lifts (by omega) (Nat.le_of_lt previous)
    rwa [hPrev]

private theorem at_old_from_cubic_seed (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex)
    (seed : GeometricAt seedDegree) : GeometricAt targetIndex := by
  have walk (n : Nat) (room : seedDegree+n≤targetIndex) : GeometricAt (seedDegree+n) := by
    induction n with
    | zero => exact seed
    | succ n ih =>
      change seedDegree+n+1≤targetIndex at room
      exact geometric_degree_step (t:=seedDegree+n) H wide (Nat.le_add_right ..) room (ih (Nat.le_of_succ_le room))
  have reaches : seedDegree≤targetIndex := by
    rw [targetIndex_eq]; exact Nat.pow_lt_pow_right (by decide) (by decide : 3<256)
  have current := walk (targetIndex-seedDegree) (by omega)
  rwa [Nat.add_sub_of_le reaches] at current

private theorem diagram_at_scale {N t : Nat} (np : 0<N) (within : N≤t) (cap : N^N≤t)
    (old : ∀ y, (tables t).mul (2^N-3) y=diagonalWord N (y%2^N)%2^t) : DiagonalHomAt N t := by
  apply diagonal_hom_of_row within
  intro y
  have b := intervalWord_bound (f:=fun i : Nat => N^i) (fun _ _ => Nat.pow_le_pow_right np) 0 N (y%2^N)
  simp only [Nat.zero_add,Nat.pow_zero,Nat.pow_one] at b
  change diagonalWord N (y%2^N)+2≤2^(N^N) at b
  have bound := Nat.pow_le_pow_right (by decide : 0<2) cap
  exact (old y).trans (Nat.mod_eq_of_lt (by omega))

theorem diagonal_from_cubic_seed (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex)
    (seed : GeometricAt seedDegree) : DiagonalHomAt 256 targetIndex := by
  have within : 256≤targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 8≤2048)
  exact diagram_at_scale (by decide : 0<256) within (Nat.le_of_eq targetIndex_eq.symm)
    (at_old_from_cubic_seed H wide seed)

#print axioms geometric_degree_step
#print axioms diagonal_from_cubic_seed
end Gamma11
