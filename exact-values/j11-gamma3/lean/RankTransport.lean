import RankFiniteClasses
import TwelveCut

/-! Changes of cut used in Appendix A.3. All comparisons are between
actual ordinals in V_height. A strict comparison with the T-th critical
point gives the (T+1)-st cut whenever the upper point is generated.
For the finite source data the exact cutoff is read at one finite degree.
-/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

theorem next_cut_of_generated {j : Emb height} (hj : IsWitness j) {α : Below height} {m : Nat}
    (generated : ∃ A, Generated j A ∧ IsCritical A α)
    (above : dyadicPoint hj m < α) : dyadicPoint hj (m+1) ≤ α := by
  apply le_of_not_gt
  intro inside
  obtain ⟨k,hk,rfl⟩ := (initial_critical_points hj (m+1) α).mp ⟨generated,inside⟩
  have := (dyadicPoint_strict hj).lt_iff_lt.mp above
  omega

theorem word_image_generated {j : Emb height} (hj : IsWitness j) (w : Word) (x : Nat) :
    ∃ A, Generated j A ∧ IsCritical A (ordinalImage (w.embedding hj.1 j) (dyadicPoint hj x)) := by
  let p := Word.power (2^x-1)
  refine ⟨(w.app p).realize j,(w.app p).generated j,?_⟩
  rw [Word.realize_eq_graph hj.1]
  change IsCritical (graphOf (applyEmb _ _ (p.embedding _ _))) _
  rw [show p.embedding hj.1 j = powerEmb hj.1 j (2^x) from positive_power_word hj.1 j (Nat.two_pow_pos x)]
  exact applyEmb_critical hj.1 _ _ (dyadicPoint_critical hj x)

theorem native_read_act {j : Emb height} (hj : IsWitness j) {a x y m : Nat}
    (pos : 0 < a) (value : act tables m a x = y) (visible : y < m) :
    ordinalImage (powerEmb hj.1 j a) (dyadicPoint hj x) = dyadicPoint hj y := by
  have lo : entry y a (2^x) = 0 := by
    rw [← canonical_mul]
    exact (le_act_iff tables m a x y visible.le).mp value.ge
  have hi : entry (y+1) a (2^x) ≠ 0 := by
    rw [← canonical_mul]
    intro hz
    have upper := (le_act_iff tables m a x (y+1) visible).mpr hz
    omega
  have found := (native_exact hj pos x y).mpr ⟨lo,hi⟩
  rw [← powerEmb_graph hj.1] at found
  exact point_injective ((ordinalImage_spec _ _).symm.trans found)

theorem generator_two {j : Emb height} (hj : IsWitness j) :
    ordinalImage j (dyadicPoint hj 2) = dyadicPoint hj 4 :=
  native_read_act hj (a:=1) (m:=9) (by decide)
    (act_from_low tables 9 1 2 240 4 le_rfl (LowProducts.v1_4 (tables 9)) (by decide) (by decide))
    (by decide)

/-- B(K(delta_2)) = K(delta_4) clears the entire upper test cut d=T+1,
even before identifying the exact finite index of K(delta_2). -/
theorem fourth_above_target {j : Emb height} (hj : IsWitness j) :
    dyadicPoint hj (targetIndex+1) ≤ ordinalImage (powerEmb hj.1 j 12)
      (ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2)) := by
  let K := powerEmb hj.1 j 11
  have same : ordinalImage (powerEmb hj.1 j 12) (ordinalImage K (dyadicPoint hj 2)) =
      ordinalImage K (dyadicPoint hj 4) :=
    (ordinalImage_commutes hj.1 K j _).trans (congrArg (ordinalImage K) (generator_two hj))
  rw [same]
  exact next_cut_of_generated hj (word_image_generated hj (Word.power 10) 4)
    ((actual_lower_bound hj).trans_lt ((ordinalImage_strictMono K) ((dyadicPoint_strict hj) (by decide : 3<4))))

/-- A source equality at degree n transports to every degree m reached
by the outer word's image of the n-th critical point. -/
theorem lift_residue {j : Emb height} (hj : IsWitness j) (w a b : Word) {n m : Nat}
    (source : a.residue n = b.residue n)
    (reach : dyadicPoint hj m ≤ ordinalImage (w.embedding hj.1 j) (dyadicPoint hj n)) :
    (w.app a).residue m = (w.app b).residue m := by
  apply (trace_iff_residue hj m _ _).mp
  exact (((trace_iff_residue hj n _ _).mpr source).map_right hj.1 (w.embedding hj.1 j)).mono reach

/-- A.3 uses a rank restriction for the source J12. The B-side change
of cut needs just the upper bound on the earlier second image of J11. -/
theorem twelve_reaches_target {j : Emb height} (hj : IsWitness j)
    (small : ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2) ≤ dyadicPoint hj 256) :
    dyadicPoint hj (targetIndex+1) ≤ ordinalImage (powerEmb hj.1 j 12) (dyadicPoint hj 256) :=
  (fourth_above_target hj).trans ((ordinalImage_strictMono _).monotone small)

/-- The source μ for both restriction identities of Dougherty II, §8.
Tracking it as C(delta_4) avoids needing its numerical index here. -/
theorem restriction_source {j : Emb height} (hj : IsWitness j) :
    ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) =
      ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2) := by
  have j1 : ordinalImage j (dyadicPoint hj 1) = dyadicPoint hj 2 :=
    native_read_act hj (a:=1) (m:=9) (by decide)
      (act_from_low tables _ _ _ _ _ le_rfl (LowProducts.v1_2 _) (by decide) (by decide)) (by decide)
  have k1 : ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 1) = dyadicPoint hj 4 :=
    native_read_act hj (m:=9) (by decide)
      (act_from_low tables _ _ _ _ _ le_rfl (LowProducts.v11_2 _) (by decide) (by decide)) (by decide)
  have b2 : ordinalImage (powerEmb hj.1 j 12) (dyadicPoint hj 2) = dyadicPoint hj 4 :=
    native_read_act hj (m:=9) (by decide)
      (act_from_low tables _ _ _ _ _ le_rfl (LowProducts.v12_4 _) (by decide) (by decide)) (by decide)
  have first := ordinalImage_commutes hj.1 (powerEmb hj.1 j 11) j (dyadicPoint hj 1)
  rw [k1,j1,apply_generator] at first
  have second := ordinalImage_commutes hj.1 (powerEmb hj.1 j 12) j (dyadicPoint hj 2)
  rw [b2,generator_two hj,apply_generator] at second
  exact second.trans first

theorem thirteen_above_target {j : Emb height} (hj : IsWitness j) :
    dyadicPoint hj (targetIndex+1) ≤ ordinalImage (powerEmb hj.1 j 13)
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)) := by
  let d := targetIndex+1
  let u := act tables d 11 2
  have big : 9 ≤ d := by
    have := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 4≤2048)
    change 2^4 ≤ targetIndex at this
    dsimp [d]; omega
  have uBound : u≤d := act_le .. 
  have source := (native_cut hj (by decide : 0<11) 2 u).mp
    (by rw [← canonical_mul]; exact (le_act_iff tables d 11 2 u uBound).mp (Nat.le_refl _))
  have cap : act tables d 13 u = d := (twelve_thirteen_reach tables d big le_rfl).2
  have lifted := (native_cut hj (by decide : 0<13) u d).mp (by
    rw [← canonical_mul]; exact (le_act_iff tables d 13 u d le_rfl).mp cap.ge)
  rw [restriction_source hj]
  exact lifted.trans ((ordinalImage_strictMono _).monotone source)

/-- The two remaining inputs for either of the R,D0 constants in (A3)
are a restriction on V_mu and a smaller argument carried beyond mu.
The target cut itself does not appear in either input. -/
theorem thirteen_restriction_at_cut {j : Emb height} (hj : IsWitness j) {a k d : Nat}
    (apos : 0<a) (kpos : 0<k) (fit : k<2^d)
    (reach : dyadicPoint hj d ≤ ordinalImage (powerEmb hj.1 j 13)
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)))
    (agree : ∀ x : Rank height, x.val.rank <
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)).val →
      applyEmb hj.1 (powerEmb hj.1 j 13) (powerEmb hj.1 j a) x = powerEmb hj.1 j k x)
    (cross : ∃ β : Below height, β < dyadicPoint hj 4 ∧
      ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) ≤ ordinalImage (powerEmb hj.1 j a) β) :
    entry d 13 a = k := by
  let C := powerEmb hj.1 j 13
  let A := powerEmb hj.1 j a
  let w := (Word.power 12).app (Word.power (a-1))
  let t := Word.power (k-1)
  obtain ⟨β,small,above⟩ := cross
  have ew : w.embedding hj.1 j = applyEmb hj.1 C A := by
    change applyEmb hj.1 C _ = applyEmb hj.1 C _
    rw [positive_power_word hj.1 j apos]
  have et : t.embedding hj.1 j = powerEmb hj.1 j k := positive_power_word hj.1 j kpos
  have reaches := reach.trans ((ordinalImage_strictMono C).monotone above)
  have transport := residue_of_rank_agreement hj w t d
    (μ:=ordinalImage C (dyadicPoint hj 4)) (β:=ordinalImage C β)
    (by rw [ew,et]; exact agree) ((ordinalImage_strictMono C) small)
    (by rw [ew,ordinalImage_commutes]; exact reaches)
  change (tables _).mul ((Word.power _).residue _) ((Word.power _).residue _) = (Word.power _).residue _ at transport
  simpa only [Word.residue_power,Nat.sub_add_cancel apos,Nat.sub_add_cancel kpos, (tables _).mul_mod_left,
    (tables _).mul_mod_right,canonical_mul,Nat.mod_eq_of_lt fit] using transport

theorem thirteen_restriction_at_target {j : Emb height} (hj : IsWitness j) {a k : Nat}
    (apos : 0<a) (kpos : 0<k) (fit : k<2^(targetIndex+1))
    (agree : ∀ x : Rank height, x.val.rank <
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)).val →
      applyEmb hj.1 (powerEmb hj.1 j 13) (powerEmb hj.1 j a) x = powerEmb hj.1 j k x)
    (cross : ∃ β : Below height, β < dyadicPoint hj 4 ∧
      ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) ≤ ordinalImage (powerEmb hj.1 j a) β) :
    entry (targetIndex+1) 13 a = k :=
  thirteen_restriction_at_cut hj apos kpos fit (thirteen_above_target hj) agree cross

#print axioms fourth_above_target
#print axioms lift_residue
#print axioms thirteen_above_target
#print axioms thirteen_restriction_at_target
end Gamma11.RankI3
