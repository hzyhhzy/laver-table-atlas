import RankDyadic

/-! Exact finite positions in the actual critical spectrum and their
arithmetic readout. First-row growth is needed below only to prove that
the sequence exhausts the whole spectrum; each finite initial segment
and the two-cut readout are already obtained for every I3 witness. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement
variable {height : Ordinal.{u}}

theorem initial_critical_points {j : Emb height} (hj : IsWitness j) (m : Nat) (α : Below height) :
    ((∃ A, Generated j A ∧ IsCritical A α) ∧ α < dyadicPoint hj m) ↔
      ∃ k < m, dyadicPoint hj k = α := by
  have inc := dyadicPoint_strict hj
  constructor
  · rintro ⟨⟨A,gen,crit⟩,before⟩
    obtain ⟨w,rfl⟩ := generated_is_word gen
    have nz : w.residue m ≠ 0 := by
      intro zero
      have fixed := (zeroClass_of_dyadic_increase hj inc w m).mp zero
      exact before.not_ge ((fixesBefore_iff (w.singleValued hj.1 j) crit _).mp fixed)
    obtain ⟨k,hk,hit⟩ := w.first_nonzero nz
    exact ⟨k,hk,critical_unique (w.singleValued hj.1 j) (word_at_first_nonzero hj inc w k hit) crit⟩
  · rintro ⟨k,hk,rfl⟩
    let w := Word.power (2^k-1)
    exact ⟨⟨_,w.generated j,Classical.choose_spec (w.critical_exists hj)⟩,inc hk⟩

private def imageWord (a x : Nat) : Word := (Word.power (a-1)).app (Word.power (2^x-1))

private theorem imageWord_residue {a : Nat} (pos : 0 < a) (x m : Nat) :
    (imageWord a x).residue m = entry m a (2^x) := by
  change (tables _).mul ((Word.power _).residue _) ((Word.power _).residue _) = _
  rw [Word.residue_power,Word.residue_power,Nat.sub_add_cancel pos,Nat.sub_add_cancel (Nat.two_pow_pos x),
    (tables _).mul_mod_left,(tables _).mul_mod_right,canonical_mul]

private theorem imageWord_critical {j : Emb height} (hj : IsWitness j) {a : Nat} (pos : 0 < a) (x : Nat) :
    IsCritical ((imageWord a x).realize j) (ordinalImage (powerEmb hj.1 j a) (dyadicPoint hj x)) := by
  rw [Word.realize_eq_graph hj.1]
  change IsCritical (graphOf (applyEmb _ ((Word.power _).embedding _ _) ((Word.power _).embedding _ _))) _
  rw [positive_power_word hj.1 j pos,positive_power_word hj.1 j (Nat.two_pow_pos x)]
  exact applyEmb_critical hj.1 _ _ (dyadicPoint_critical hj x)

theorem native_cut {j : Emb height} (hj : IsWitness j) {a : Nat} (pos : 0 < a) (x m : Nat) :
    entry m a (2^x) = 0 ↔ dyadicPoint hj m ≤ ordinalImage (powerEmb hj.1 j a) (dyadicPoint hj x) := by
  rw [← imageWord_residue pos]
  exact (zeroClass_of_dyadic_increase hj (dyadicPoint_strict hj) _ _).trans
    (fixesBefore_iff (Word.singleValued hj.1 j _) (imageWord_critical hj pos x) _)

theorem native_exact {j : Emb height} (hj : IsWitness j) {a : Nat} (pos : 0 < a) (x y : Nat) :
    leftPower j a (point (dyadicPoint hj x)) (point (dyadicPoint hj y)) ↔
      entry y a (2^x) = 0 ∧ entry (y+1) a (2^x) ≠ 0 := by
  rw [← powerEmb_graph hj.1]
  change powerEmb hj.1 j a (point _) = point _ ↔ _
  rw [ordinalImage_spec,point_injective.eq_iff]
  have inc := dyadicPoint_strict hj
  constructor
  · intro image
    refine ⟨(native_cut hj pos x y).mpr image.ge,fun zero => ?_⟩
    have high := (native_cut hj pos x (y+1)).mp zero
    exact (inc (Nat.lt_succ_self y)).not_ge (high.trans image.le)
  · rintro ⟨lo,hi⟩
    let w := imageWord a x
    obtain ⟨k,upper,hit⟩ := w.first_nonzero (fun h => hi ((imageWord_residue pos x (y+1)) ▸ h))
    have eqv := critical_unique (w.singleValued hj.1 j) (imageWord_critical hj pos x)
      (word_at_first_nonzero hj inc w k hit)
    have lower := (native_cut hj pos x y).mp lo
    rw [eqv,inc.le_iff_le] at lower
    exact eqv.trans (congrArg (dyadicPoint hj) (show k=y by omega))

/-- An actual, unconditional lower bound within each I3 witness. -/
theorem actual_lower_bound {j : Emb height} (hj : IsWitness j) :
    dyadicPoint hj targetIndex ≤ ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 3) :=
  (native_cut hj (by decide : 0<11) 3 targetIndex).mp (row11_zero_through_target _ le_rfl)

/-- The equality at the two specified places has exactly one finite
remaining test. No table correspondence or other premise is required. -/
theorem actual_endpoint_iff_target {j : Emb height} (hj : IsWitness j) :
    leftPower j 11 (point (dyadicPoint hj 3)) (point (dyadicPoint hj targetIndex)) ↔ Target := by
  rw [native_exact hj (by decide : 0<11),target_iff_nonzero]
  exact ⟨And.right, fun h => ⟨row11_zero_through_target _ le_rfl,h⟩⟩

namespace Word
theorem table_total (H : FirstRowUnbounded) (w : Word) : w.tableValue.Total := by
  induction w with
  | generator => exact generator_total H
  | app s t hs ht => exact total_app hs ht

private theorem moves_index (H : FirstRowUnbounded) (w : Word) :
    ∃ x, x < w.tableValue.index (w.table_total H) x := by
  induction w with
  | generator =>
    refine ⟨0,?_⟩
    apply ((numeral 1).zero_iff (generator_total H) 1 0).mp
    change (tables 1).mul (1%2^1) 1 = 0
    rw [(tables 1).mul_one]
  | app s t _ ht =>
    obtain ⟨x,moves⟩ := ht
    refine ⟨s.tableValue.index (s.table_total H) x,?_⟩
    have e := index_app (s.table_total H) (t.table_total H) x
    exact (s.tableValue.index_strict (s.table_total H) moves).trans_eq e.symm

theorem exists_nonzero (H : FirstRowUnbounded) (w : Word) : ∃ m, w.residue m ≠ 0 := by
  obtain ⟨x,moves⟩ := w.moves_index H
  refine ⟨x+1,fun zero => ?_⟩
  have h := (w.tableValue.zero_iff (w.table_total H) (x+1) x).mpr moves
  rw [w.tableValue_rep,zero,(tables _).zero_mul] at h
  exact Nat.not_succ_le_self x ((pow_mod_zero_iff x (x+1)).mp h)
end Word

theorem quotientLaws_of_first_row {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded) :
    QuotientLaws j (dyadicPoint hj) := by
  have inc := dyadicPoint_strict hj
  refine ⟨⟨inc,?_⟩,zeroClass_of_dyadic_increase hj inc⟩
  intro α
  constructor
  · rintro ⟨A,hA,crit⟩
    obtain ⟨w,rfl⟩ := generated_is_word hA
    obtain ⟨m,nz⟩ := w.exists_nonzero H
    obtain ⟨k,_,hit⟩ := w.first_nonzero nz
    exact ⟨k,critical_unique (w.singleValued hj.1 j) (word_at_first_nonzero hj inc w k hit) crit⟩
  · rintro ⟨k,rfl⟩
    let w := Word.power (2^k-1)
    exact ⟨_,w.generated j,Classical.choose_spec (w.critical_exists hj)⟩

theorem enumerates_eq_dyadic {j : Emb height} (hj : IsWitness j) {γ : Nat → Below height}
    (h : Enumerates j γ) : γ = dyadicPoint hj := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_contra ne
    rcases lt_or_gt_of_ne ne with before|after
    · have gen := (h.2 _).mpr ⟨n,rfl⟩
      obtain ⟨k,hk,eqv⟩ := (initial_critical_points hj n (γ n)).mp ⟨gen,before⟩
      exact hk.ne (h.1.injective ((ih k hk).trans eqv))
    · let w := Word.power (2^n-1)
      obtain ⟨m,eqv⟩ := (h.2 (dyadicPoint hj n)).mp ⟨_,w.generated j,Classical.choose_spec (w.critical_exists hj)⟩
      have mn := h.1.lt_iff_lt.mp (eqv.trans_lt after)
      exact mn.ne ((dyadicPoint_strict hj).injective ((ih m mn).symm.trans eqv))

theorem enumeration_iff_first_row {j : Emb height} (hj : IsWitness j) :
    (∃ γ, Enumerates j γ) ↔ FirstRowUnbounded := by
  constructor
  · rintro ⟨γ,hγ⟩
    obtain rfl := enumerates_eq_dyadic hj hγ
    intro x
    let w := imageWord 1 x
    obtain ⟨k,whereAt⟩ := (hγ.2 _).mp ⟨_,w.generated j,imageWord_critical hj (by decide : 0<1) x⟩
    refine ⟨k+1,fun zero => ?_⟩
    have bound := (native_cut hj (by decide : 0<1) x (k+1)).mp zero
    exact ((dyadicPoint_strict hj) (Nat.lt_succ_self k)).not_ge (bound.trans whereAt.ge)
  · exact fun H => ⟨_,(quotientLaws_of_first_row hj H).enumerates⟩

/-- Constant-sequence case of Steel's cofinality theorem, expressed for
    the genuine left powers. The finite quotient theory needed after this
    input has already been proved above for each I3 witness. -/
def LeftPowersCofinal (j : Emb height) : Prop :=
  ∀ α : Below height, ∃ (r : Nat) (β : Below height), α < β ∧ IsCritical (leftPower j (r+1)) β

theorem first_row_of_left_powers_cofinal {j : Emb height} (hj : IsWitness j) (cof : LeftPowersCofinal j) :
    FirstRowUnbounded := by
  apply (enumeration_iff_first_row hj).mp
  refine ⟨_,(quotientLaws_of_dyadic hj (dyadicPoint_strict hj) ?_).enumerates⟩
  intro α
  obtain ⟨r,β,above,crit⟩ := cof α
  let w := Word.power r
  have bound (m : Nat) : m < 2^m := by
    induction m with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos m; omega
  have nz : w.residue (r+1) ≠ 0 := by
    rw [Word.residue_power,Nat.mod_eq_of_lt (bound (r+1))]
    omega
  obtain ⟨i,_,hit⟩ := w.first_nonzero nz
  have atPower : IsCritical (w.realize j) β := by rwa [Word.realize_power]
  have eqv := critical_unique (w.singleValued hj.1 j) atPower (word_at_first_nonzero hj (dyadicPoint_strict hj) w i hit)
  exact ⟨i,above.trans_eq eqv⟩

#print axioms initial_critical_points
#print axioms actual_lower_bound
#print axioms actual_endpoint_iff_target
#print axioms quotientLaws_of_first_row
#print axioms enumeration_iff_first_row
#print axioms first_row_of_left_powers_cofinal
end Gamma11.RankI3
