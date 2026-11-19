import RankSpectrum

/-! The critical points of the left powers J_(2^n) strictly increase.
The intermediate powers all send the preceding critical point to at
least the current one, by the half-period bound in the finite table.
This permits copying all successors up to the image of the current cut. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

theorem positive_power_word (hl : Order.IsSuccLimit height) (j : Emb height) {i : Nat} (pos : 0 < i) :
    (Word.power (i-1)).embedding hl j = powerEmb hl j i := by
  cases i with
  | zero => omega
  | succ i => rfl

theorem ordinalImage_commutes (hl : Order.IsSuccLimit height) (a b : Emb height) (δ : Below height) :
    ordinalImage (applyEmb hl a b) (ordinalImage a δ) = ordinalImage a (ordinalImage b δ) := by
  apply point_injective
  rw [← ordinalImage_spec, ← ordinalImage_spec, ← ordinalImage_spec, applyEmb_commutes, ordinalImage_spec b δ]

theorem critical_moves (a : Emb height) {θ : Below height} (h : IsCritical (graphOf a) θ) :
    θ < ordinalImage a θ := by
  obtain ⟨β,hβ,hp⟩ := h.2
  rwa [point_injective ((ordinalImage_spec a θ).symm.trans hp)]

/-- This bound holds before establishing that the dyadic cuts increase. -/
theorem intermediate_power_bound {j : Emb height} (hj : IsWitness j) (k i : Nat)
    (hi : 0 < i) (small : i < 2^(k+1)) :
    dyadicPoint hj (k+1) ≤ ordinalImage (powerEmb hj.1 j i) (dyadicPoint hj k) := by
  let w := Word.app (Word.power (i-1)) (Word.power (2^k-1))
  have hz : w.residue (k+1) = 0 := by
    change (tables _).mul ((Word.power _).residue _) ((Word.power _).residue _) = 0
    rw [Word.residue_power,Word.residue_power,Nat.sub_add_cancel hi,Nat.sub_add_cancel (Nat.two_pow_pos k),
      (tables _).mul_mod_left,(tables _).mul_mod_right]
    exact positive_half_zero tables k i hi small
  have trace := dyadic_trace hj w (k+1)
  dsimp only [w,Word.embedding] at trace
  rw [positive_power_word hj.1 j hi,positive_power_word hj.1 j (Nat.two_pow_pos k)] at trace
  change TraceEq _ (applyEmb _ _ _) (powerEmb _ _ (w.residue _)) at trace
  rw [hz] at trace
  have fixed := (trace_identity_iff hj.1 _ _).mp trace
  have crit := applyEmb_critical hj.1 (powerEmb hj.1 j i) _ (dyadicPoint_critical hj k)
  exact (fixesBefore_iff (graphOf_singleValued _) crit _).mp fixed

private theorem copy_successors (hl : Order.IsSuccLimit height) (j : Emb height) (S : Nat)
    (θ σ : Below height) (θlim : Order.IsSuccPrelimit θ.val) (σlim : Order.IsSuccPrelimit σ.val)
    (wrap : TraceEq θ (powerEmb hl j S) (identityEmb height))
    (bound : ∀ i, 0 < i → i < S → σ ≤ ordinalImage (applyEmb hl (powerEmb hl j S) (powerEmb hl j i)) θ)
    (i : Nat) (lo : 0 < i) (hi : i ≤ S) :
    TraceEq σ (powerEmb hl j (S+i)) (applyEmb hl (powerEmb hl j S) (powerEmb hl j i)) := by
  have same := wrap.symm.app hl θlim (TraceEq.refl θ j)
  rw [identity_apply] at same
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases z : i=0
    · subst i
      rw [← apply_generator hl j S]
      rfl
    · have prev := ih (by omega) (by omega)
      have left := prev.app hl σlim (TraceEq.refl σ j)
      have right := (same.map_right hl (applyEmb hl (powerEmb hl j S) (powerEmb hl j i))).mono
        (bound i (by omega) (by omega))
      have step := left.trans right
      rw [← applyEmb_ld hl (powerEmb hl j S) (powerEmb hl j i) j,apply_generator,apply_generator] at step
      exact step

private theorem dyadic_first {j : Emb height} (hj : IsWitness j) :
    dyadicPoint hj 0 < dyadicPoint hj 1 := by
  have first := dyadicPoint_critical hj 0
  change IsCritical (graphOf j) (dyadicPoint hj 0) at first
  have second := dyadicPoint_critical hj 1
  change IsCritical (graphOf (applyEmb hj.1 j j)) (dyadicPoint hj 1) at second
  have eqv := critical_unique (graphOf_singleValued _) second (applyEmb_critical hj.1 j j first)
  rw [eqv]
  exact critical_moves j first

private theorem dyadic_step {j : Emb height} (hj : IsWitness j) (k : Nat)
    (prev : dyadicPoint hj k < dyadicPoint hj (k+1)) :
    dyadicPoint hj (k+1) < dyadicPoint hj (k+2) := by
  let S := 2^(k+1)
  let c := powerEmb hj.1 j S
  let θ := dyadicPoint hj (k+1)
  let σ := ordinalImage c θ
  have cθ : IsCritical (graphOf c) θ := dyadicPoint_critical hj (k+1)
  have ccσ : IsCritical (graphOf (applyEmb hj.1 c c)) σ := applyEmb_critical hj.1 c c cθ
  have wrap := (trace_identity_iff hj.1 c θ).mpr cθ.1
  have fixed : ordinalImage c (dyadicPoint hj k) = dyadicPoint hj k :=
    point_injective ((ordinalImage_spec c _).symm.trans (cθ.1 _ prev))
  have strong (i : Nat) (lo : 0 < i) (hi : i < S) :
      σ ≤ ordinalImage (applyEmb hj.1 c (powerEmb hj.1 j i)) θ := by
    have moved := (ordinalImage_strictMono c).monotone (intermediate_power_bound hj k i lo hi)
    rw [← ordinalImage_commutes hj.1 c (powerEmb hj.1 j i),fixed] at moved
    exact moved.trans ((ordinalImage_strictMono _).monotone prev.le)
  have trace := copy_successors hj.1 j S θ σ (critical_prelimit hj.1 c cθ)
    (critical_prelimit hj.1 _ ccσ) wrap strong S (Nat.two_pow_pos _) le_rfl
  have eqv : S+S = 2^(k+2) := by change 2^(k+1)+2^(k+1) = 2^((k+1)+1); rw [Nat.pow_succ]; omega
  rw [eqv] at trace
  have fixedBefore := (trace_identity_iff hj.1 _ σ).mp
    (trace.trans ((trace_identity_iff hj.1 _ σ).mpr ccσ.1))
  have after := (fixesBefore_iff (graphOf_singleValued _) (dyadicPoint_critical hj (k+2)) σ).mp fixedBefore
  exact (critical_moves c cθ).trans_le after

theorem dyadicPoint_strict {j : Emb height} (hj : IsWitness j) : StrictMono (dyadicPoint hj) := by
  apply strictMono_nat_of_lt_succ
  intro k
  induction k with
  | zero => exact dyadic_first hj
  | succ k ih => exact dyadic_step hj k ih

/-- The quarter row fixes the exact next point, after strictness has
    been proved independently at every degree. -/
theorem dyadic_self_image {j : Emb height} (hj : IsWitness j) (k : Nat) :
    ordinalImage (powerEmb hj.1 j (2^k)) (dyadicPoint hj k) = dyadicPoint hj (k+1) := by
  let p := Word.power (2^k-1)
  have native : p.embedding hj.1 j = powerEmb hj.1 j (2^k) := positive_power_word hj.1 j (Nat.two_pow_pos k)
  have hit : (p.app p).residue (k+2) = 2^(k+1) := by
    change (tables _).mul ((Word.power _).residue _) ((Word.power _).residue _) = _
    rw [Word.residue_power,Nat.sub_add_cancel (Nat.two_pow_pos k),(tables _).mul_mod_left,(tables _).mul_mod_right]
    exact quarter_square k
  have trace := dyadic_trace hj (p.app p) (k+2)
  rw [hit] at trace
  change TraceEq _ (applyEmb hj.1 (p.embedding hj.1 j) (p.embedding hj.1 j)) _ at trace
  rw [native] at trace
  have crit := trace.symm.critical hj.1 (dyadicPoint_strict hj (Nat.lt_succ_self (k+1))) (dyadicPoint_critical hj (k+1))
  exact critical_unique (graphOf_singleValued _) (applyEmb_critical hj.1 _ _ (dyadicPoint_critical hj k)) crit

#print axioms dyadicPoint_strict
#print axioms dyadic_self_image
end Gamma11.RankI3
