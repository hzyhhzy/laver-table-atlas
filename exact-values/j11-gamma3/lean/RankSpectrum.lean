import RankQuotients
import RankTrace
import QuarterRow

/-! Recover the finite table on arbitrary words from the critical points
of dyadic powers. A power whose critical point is θ equals the identity
in the trace at θ. This supplies the wrap in the finite table recursion.
The first nonzero projection of a word then identifies its critical point. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

noncomputable def powerEmb (hl : Order.IsSuccLimit height) (j : Emb height) : Nat → Emb height
  | 0 => identityEmb height
  | k+1 => (Word.power k).embedding hl j

theorem apply_generator (hl : Order.IsSuccLimit height) (j : Emb height) (i : Nat) :
    applyEmb hl (powerEmb hl j i) j = powerEmb hl j (i+1) := by
  cases i with
  | zero => exact identity_apply hl j
  | succ k => rfl

theorem powerEmb_graph (hl : Order.IsSuccLimit height) (j : Emb height) (i : Nat) :
    graphOf (powerEmb hl j i) = leftPower j i := by
  cases i with
  | zero => rfl
  | succ i => exact ((Word.power i).realize_eq_graph hl j).symm.trans (Word.realize_power j i)

private theorem trace_succ (hl : Order.IsSuccLimit height) (j : Emb height) (θ : Below height) {d : Nat}
    (wrap : TraceEq θ (powerEmb hl j (2^d)) (identityEmb height)) (i : Nat) (hi : i < 2^d) :
    TraceEq θ (applyEmb hl (powerEmb hl j i) j) (powerEmb hl j ((i+1)%2^d)) := by
  rw [apply_generator]
  rcases Nat.lt_or_eq_of_le hi with less|last
  · rw [Nat.mod_eq_of_lt less]
  · change i+1=2^d at last
    rw [last,Nat.mod_self]
    exact wrap

private theorem trace_table_mul (hl : Order.IsSuccLimit height) (j : Emb height) (θ : Below height)
    (cut : Order.IsSuccPrelimit θ.val) (d : Nat)
    (wrap : TraceEq θ (powerEmb hl j (2^d)) (identityEmb height))
    (a b : Nat) (ha : a < 2^d) (hb : b < 2^d) :
    TraceEq θ (applyEmb hl (powerEmb hl j a) (powerEmb hl j b))
      (powerEmb hl j ((tables d).mul a b)) := by
  by_cases za : a=0
  · subst a
    change TraceEq θ (applyEmb hl (identityEmb _) _) _
    rw [identity_apply,(tables d).zero_mul,Nat.mod_eq_of_lt hb]
  cases b with
  | zero =>
    change TraceEq θ (applyEmb hl _ (identityEmb _)) _
    rw [apply_identity,(tables d).mul_zero]
    rfl
  | succ b =>
    have prev := trace_table_mul hl j θ cut d wrap a b ha (by omega)
    rw [← apply_generator hl j b,applyEmb_ld,(tables d).row_recurrence,
      ← (tables d).mul_mod_right ((tables d).mul a b) (a+1)]
    apply (prev.app hl cut (trace_succ hl j θ wrap a ha)).trans
    have fit := Nat.mod_lt (a+1) (Nat.two_pow_pos d)
    rcases (tables d).row_grows a b ha with zero|later
    · rw [zero,(tables d).zero_mul,Nat.mod_eq_of_lt fit]
      exact (identity_apply hl _).symm ▸ TraceEq.refl θ _
    · exact trace_table_mul hl j θ cut d wrap _ _ ((tables d).mul_lt _ _) fit
termination_by (2^d-a,b)
decreasing_by all_goals decreasing_trivial

namespace Word

def tableValue : Word → TableElement
  | .generator => .numeral 1
  | .app s t => s.tableValue.app t.tableValue

theorem tableValue_rep (w : Word) (d : Nat) : w.tableValue.rep d = w.residue d := by
  induction w with
  | generator => rfl
  | app s t hs ht => exact congrArg₂ (tables d).mul hs ht

theorem residue_lt (w : Word) (d : Nat) : w.residue d < 2^d :=
  (w.tableValue_rep d) ▸ w.tableValue.bound d

theorem residue_project (w : Word) {d m : Nat} (h : d ≤ m) :
    w.residue m % 2^d = w.residue d := by
  rw [← w.tableValue_rep,← w.tableValue_rep]
  exact w.tableValue.project h

theorem first_nonzero (w : Word) {m : Nat} (nz : w.residue m ≠ 0) :
    ∃ k < m, w.residue (k+1) = 2^k := by
  induction m with
  | zero => have h := w.residue_lt 0; simp at h; contradiction
  | succ m ih =>
    by_cases old : w.residue m = 0
    · refine ⟨m,Nat.lt_succ_self m,?_⟩
      have bound := w.residue_lt (m+1)
      rw [Nat.pow_succ] at bound
      exact (multiple_below_twice bound ((w.residue_project (Nat.le_succ m)).trans old)).resolve_left nz
    · obtain ⟨k,hk,found⟩ := ih old
      exact ⟨k,hk.trans (Nat.lt_succ_self m),found⟩

theorem trace_residue (hl : Order.IsSuccLimit height) (j : Emb height) (θ : Below height)
    (cut : Order.IsSuccPrelimit θ.val) (d : Nat)
    (wrap : TraceEq θ (powerEmb hl j (2^d)) (identityEmb height)) (w : Word) :
    TraceEq θ (w.embedding hl j) (powerEmb hl j (w.residue d)) := by
  induction w with
  | generator =>
    have step := trace_succ hl j θ wrap 0 (Nat.two_pow_pos d)
    change TraceEq θ j (powerEmb hl j (1%2^d))
    change TraceEq θ (applyEmb hl (identityEmb height) j) (powerEmb hl j (1%2^d)) at step
    rwa [identity_apply] at step
  | app s t hs ht =>
    exact (hs.app hl cut ht).trans
      (trace_table_mul hl j θ cut d wrap _ _ (s.residue_lt d) (t.residue_lt d))
end Word

theorem TraceEq.critical {θ α : Below height} (hl : Order.IsSuccLimit height) {a b : Emb height}
    (h : TraceEq θ a b) (earlier : α < θ) (crit : IsCritical (graphOf a) α) :
    IsCritical (graphOf b) α := by
  have fixed := (trace_identity_iff hl a α).mpr crit.1
  refine ⟨(trace_identity_iff hl b α).mp ((h.symm.mono earlier.le).trans fixed),
    ordinalImage b α,?_,ordinalImage_spec b α⟩
  have low : (point α).val.rank < θ.val := by change α.val.toZFSet.rank < θ.val; rwa [Ordinal.rank_toZFSet]
  obtain ⟨δ,up,image⟩ := crit.2
  have old : (point α).val ∈ (a (point α)).val := by
    rw [show a (point α) = point δ from image]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr up
  have new := (h (point α) (point α) low low).mp old
  rw [ordinalImage_spec b α] at new
  exact Ordinal.toZFSet_mem_toZFSet_iff.mp new

theorem critical_unique {A : Graph height} (single : SingleValuedOnPoints A) {α β : Below height}
    (ha : IsCritical A α) (hb : IsCritical A β) : α = β := by
  apply le_antisymm
  · exact (fixesBefore_iff single hb α).mp ha.1
  · exact (fixesBefore_iff single ha β).mp hb.1

noncomputable def dyadicPoint {j : Emb height} (hj : IsWitness j) (n : Nat) : Below height :=
  Classical.choose ((Word.power (2^n-1)).critical_exists hj)

theorem dyadicPoint_critical {j : Emb height} (hj : IsWitness j) (n : Nat) :
    IsCritical (graphOf (powerEmb hj.1 j (2^n))) (dyadicPoint hj n) := by
  have c := Classical.choose_spec ((Word.power (2^n-1)).critical_exists hj)
  change IsCritical ((Word.power (2^n-1)).realize j) (dyadicPoint hj n) at c
  rw [Word.realize_power,Nat.sub_add_cancel (Nat.two_pow_pos n)] at c
  rwa [powerEmb_graph]

theorem dyadic_trace {j : Emb height} (hj : IsWitness j) (w : Word) (n : Nat) :
    TraceEq (dyadicPoint hj n) (w.embedding hj.1 j) (powerEmb hj.1 j (w.residue n)) := by
  have crit := dyadicPoint_critical hj n
  exact w.trace_residue hj.1 j _ (critical_prelimit hj.1 _ crit) n ((trace_identity_iff hj.1 _ _).mpr crit.1)

theorem word_at_first_nonzero {j : Emb height} (hj : IsWitness j) (inc : StrictMono (dyadicPoint hj))
    (w : Word) (k : Nat) (hit : w.residue (k+1) = 2^k) : IsCritical (w.realize j) (dyadicPoint hj k) := by
  have trace := dyadic_trace hj w (k+1)
  rw [hit] at trace
  rw [w.realize_eq_graph hj.1]
  exact trace.symm.critical hj.1 (inc (Nat.lt_succ_self k)) (dyadicPoint_critical hj k)

/-- The zero test needs strict increase of the dyadic critical points.
    Cofinality enters only when showing that all critical points have
    been enumerated. -/
theorem zeroClass_of_dyadic_increase {j : Emb height} (hj : IsWitness j)
    (inc : StrictMono (dyadicPoint hj)) (w : Word) (m : Nat) :
    w.residue m = 0 ↔ FixesBefore (w.realize j) (dyadicPoint hj m) := by
  constructor
  · intro h
    have trace := dyadic_trace hj w m
    rw [h] at trace
    rw [w.realize_eq_graph hj.1]
    exact (trace_identity_iff hj.1 _ _).mp trace
  · intro fixes
    by_contra nz
    obtain ⟨k,hk,hit⟩ := w.first_nonzero nz
    have earlier := inc hk
    have upper := (fixesBefore_iff (w.singleValued hj.1 j) (word_at_first_nonzero hj inc w k hit) _).mp fixes
    exact earlier.not_ge upper

theorem generated_is_word {j : Emb height} {A : Graph height} (g : Generated j A) :
    ∃ w : Word, w.realize j = A := by
  induction g with
  | generator => exact ⟨.generator,rfl⟩
  | app _ _ ha hb =>
    obtain ⟨s,rfl⟩ := ha
    obtain ⟨t,rfl⟩ := hb
    exact ⟨.app s t,rfl⟩

theorem quotientLaws_of_dyadic {j : Emb height} (hj : IsWitness j) (inc : StrictMono (dyadicPoint hj))
    (cofinal : ∀ α : Below height, ∃ m, α < dyadicPoint hj m) : QuotientLaws j (dyadicPoint hj) := by
  refine ⟨⟨inc,?_⟩,zeroClass_of_dyadic_increase hj inc⟩
  intro α
  constructor
  · rintro ⟨A,gen,crit⟩
    obtain ⟨w,rfl⟩ := generated_is_word gen
    obtain ⟨m,hm⟩ := cofinal α
    have nz : w.residue m ≠ 0 := by
      intro zero
      have within := (zeroClass_of_dyadic_increase hj inc w m).mp zero
      exact hm.not_ge ((fixesBefore_iff (w.singleValued hj.1 j) crit _).mp within)
    obtain ⟨k,_,hit⟩ := w.first_nonzero nz
    exact ⟨k,critical_unique (w.singleValued hj.1 j) (word_at_first_nonzero hj inc w k hit) crit⟩
  · rintro ⟨n,rfl⟩
    let w := Word.power (2^n-1)
    exact ⟨_,w.generated j,Classical.choose_spec (w.critical_exists hj)⟩

#print axioms Word.trace_residue
#print axioms quotientLaws_of_dyadic
end Gamma11.RankI3
