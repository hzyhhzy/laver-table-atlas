import RankTransport

/-! Recover ordinary composition at every finite cut. Iterating
(a,b) ↦ (a(b),a) preserves a ∘ b. Each nonzero left residue either
increases or becomes zero, when the left map fixes every set below the cut.
The final application to J11 identifies its ordinary restriction from the
finite calculation in TwelveCut. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

private theorem drop_identity_left (hl : Order.IsSuccLimit height) {θ : Below height}
    {a : Emb height} (b : Emb height) (tr : TraceEq θ a (identityEmb height)) :
    TraceEq θ (a.comp b) b := by
  intro x y _ hy
  have fixed := fixes_set_below hl a θ ((trace_identity_iff hl _ _).mp tr) y hy
  have mem : (a y).val ∈ (a (b x)).val ↔ y.val ∈ (b x).val :=
    (RankDef.memV (0 : Fin 2) 1).transfer a ![y,b x]
  rwa [fixed] at mem

theorem word_composition_trace {j : Emb height} (hj : IsWitness j) (m : Nat) (w t : Word) :
    TraceEq (dyadicPoint hj m) ((w.embedding hj.1 j).comp (t.embedding hj.1 j))
      (powerEmb hj.1 j ((tables m).comp (w.residue m) (t.residue m))) := by
  by_cases zero : w.residue m = 0
  · rw [zero,(tables m).zero_comp,Nat.mod_eq_of_lt (t.residue_lt m)]
    exact (drop_identity_left hj.1 _ ((w.zero_iff_identity_trace hj m).mp zero)).trans (dyadic_trace hj t m)
  · have swap : (w.embedding hj.1 j).comp (t.embedding hj.1 j) =
        ((w.app t).embedding hj.1 j).comp (w.embedding hj.1 j) :=
      DFunLike.ext _ _ fun x => (applyEmb_commutes hj.1 _ _ x).symm
    rw [swap,(tables m).comp_swap]
    exact word_composition_trace hj m (w.app t) w
termination_by if w.residue m=0 then 0 else 2^m-w.residue m
decreasing_by
  change (if (tables m).mul (w.residue m) (t.residue m)=0 then 0 else
    2^m - (tables m).mul (w.residue m) (t.residue m)) <
    (if w.residue m=0 then 0 else 2^m-w.residue m)
  rw [if_neg zero]
  have bound := w.residue_lt m
  have productBound := (tables m).mul_lt (w.residue m) (t.residue m)
  rcases (tables m).row_grows (w.residue m) (t.residue m) bound with hit|advance
  · rw [if_pos hit]
    omega
  · rw [if_neg (show (tables m).mul (w.residue m) (t.residue m)≠0 by omega)]
    omega

private theorem point_rank_below (x θ : Below height) (h : x<θ) : (point x).val.rank<θ.val := by
  change x.val.toZFSet.rank < θ.val
  rwa [Ordinal.rank_toZFSet]

theorem TraceEq.read_ordinal {θ : Below height} {a b : Emb height} (tr : TraceEq θ a b)
    {x : Below height} (small : x<θ) (visible : ordinalImage a x<θ) : ordinalImage a x = ordinalImage b x := by
  have rd (y : Below height) (hy : y<θ) : (y<ordinalImage a x ↔ y<ordinalImage b x) := by
    have e := tr (point x) (point y) (point_rank_below _ _ small) (point_rank_below _ _ hy)
    rw [ordinalImage_spec,ordinalImage_spec] at e
    exact Ordinal.toZFSet_mem_toZFSet_iff.symm.trans (e.trans Ordinal.toZFSet_mem_toZFSet_iff)
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((rd _ (h.trans visible)).mp h)
  · apply le_of_not_gt
    intro h
    exact lt_irrefl _ ((rd _ visible).mpr h)

theorem TraceEq.read_set (hl : Order.IsSuccLimit height) {θ : Below height} {a b : Emb height}
    (tr : TraceEq θ a b) {x : Rank height} (small : x.val.rank<θ.val) (visible : (a x).val.rank<θ.val) :
    a x = b x := by
  let α : Below height := ⟨x.val.rank,x.property⟩
  have ma := map_set_rank hl a x
  have mb := map_set_rank hl b x
  have atOrd := tr.read_ordinal (x:=α) small (show (ordinalImage a α).val<θ.val from ma.symm.trans_lt visible)
  have same : (a x).val.rank = (b x).val.rank := ma.trans ((congrArg Subtype.val atOrd).trans mb.symm)
  apply (rank_ext_iff _ _).mpr
  intro y
  by_cases hy : y.val.rank<θ.val
  · exact tr x y small hy
  · exact ⟨fun h => (hy ((ZFSet.rank_lt_of_mem h).trans visible)).elim,
      fun h => (hy ((ZFSet.rank_lt_of_mem h).trans (same ▸ visible))).elim⟩

theorem eleven_composition_trace {j : Emb height} (hj : IsWitness j) (m : Nat)
    (within : dyadicPoint hj m ≤ ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2)) :
    TraceEq (dyadicPoint hj m) (j.comp j) (powerEmb hj.1 j 11) := by
  have zero := (native_cut hj (by decide : 0<11) 2 m).mpr within
  have value := one_two_before_eleven_second tables m ((canonical_mul m 11 4).trans zero)
  have comp : (tables m).comp 1 1 = 11 % 2^m := by
    change ((tables m).mul 1 2 + 2^m-1)%2^m = _
    rw [value]
    exact (tables m).predecessor_successor 11
  have tr := word_composition_trace hj m .generator .generator
  change TraceEq _ (j.comp j) (powerEmb _ _ ((tables m).comp (1%2^m) (1%2^m))) at tr
  rw [(tables m).comp_mod_left,(tables m).comp_mod_right,comp] at tr
  have native := dyadic_trace hj (Word.power 10) m
  rw [Word.residue_power] at native
  exact tr.trans native.symm

/-- Whenever the second image has a finite index, Appendix A.3's ordinary
restriction of J11 to V_delta2 follows without a separate rank hypothesis. -/
theorem eleven_agrees_below_two {j : Emb height} (hj : IsWitness j) {m : Nat}
    (known : ordinalImage (powerEmb hj.1 j 11) (dyadicPoint hj 2) = dyadicPoint hj m)
    (x : Rank height) (small : x.val.rank<(dyadicPoint hj 2).val) : powerEmb hj.1 j 11 x = j (j x) := by
  let K := powerEmb hj.1 j 11
  have tr := (eleven_composition_trace hj m known.ge).symm
  have prior : dyadicPoint hj 2 ≤ dyadicPoint hj m := known ▸ (ordinalImage_strictMono K).le_apply
  have visible : (K x).val.rank < (dyadicPoint hj m).val := by
    rw [map_set_rank hj.1 K x,← known]
    exact (ordinalImage_strictMono K) (show (⟨x.val.rank,x.property⟩ : Below height) < dyadicPoint hj 2 from small)
  exact tr.read_set hj.1 (small.trans_le prior) visible

#print axioms word_composition_trace
#print axioms eleven_composition_trace
#print axioms eleven_agrees_below_two
end Gamma11.RankI3
