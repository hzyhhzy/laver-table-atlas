import RankReadout

/-! At each finite critical cut the actual Laver trace quotient on
application words is the ordinary binary Laver table. Repeated right
application of the generator translates the residues. Choosing the
translation that sends the first residue to zero detects equality. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

namespace Word
def successors (w : Word) : Nat → Word
  | 0 => w
  | n+1 => (w.successors n).app .generator

theorem residue_successors (w : Word) (m n : Nat) :
    (w.successors n).residue m = (w.residue m+n)%2^m := by
  induction n with
  | zero => exact (Nat.mod_eq_of_lt (w.residue_lt m)).symm
  | succ n ih =>
    change (tables m).mul ((w.successors n).residue m) (1%2^m) = _
    rw [ih,(tables _).mul_mod_left,(tables _).mul_mod_right,(tables _).mul_one]
    rw [Nat.add_assoc]

theorem trace_successors {j : Emb height} (hj : IsWitness j) {w t : Word} (m : Nat)
    (h : TraceEq (dyadicPoint hj m) (w.embedding hj.1 j) (t.embedding hj.1 j)) (n : Nat) :
    TraceEq (dyadicPoint hj m) ((w.successors n).embedding hj.1 j) ((t.successors n).embedding hj.1 j) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.app hj.1 (critical_prelimit hj.1 _ (dyadicPoint_critical hj m)) (.refl _ j)

theorem zero_iff_identity_trace {j : Emb height} (hj : IsWitness j) (w : Word) (m : Nat) :
    w.residue m = 0 ↔ TraceEq (dyadicPoint hj m) (w.embedding hj.1 j) (identityEmb height) := by
  rw [trace_identity_iff hj.1,zeroClass_of_dyadic_increase hj (dyadicPoint_strict hj)]
  rw [w.realize_eq_graph hj.1]
  rfl
end Word

theorem trace_iff_residue {j : Emb height} (hj : IsWitness j) (m : Nat) (w t : Word) :
    TraceEq (dyadicPoint hj m) (w.embedding hj.1 j) (t.embedding hj.1 j) ↔ w.residue m = t.residue m := by
  constructor
  · intro h
    let M := 2^m
    let k := M-w.residue m
    have wb : w.residue m < M := w.residue_lt m
    have tb : t.residue m < M := t.residue_lt m
    have wrap : (w.successors k).residue m = 0 := by
      rw [w.residue_successors, show w.residue m+k=M by dsimp [k]; omega, Nat.mod_self]
    have same := Word.trace_successors hj m h k
    have ht := ((t.successors k).zero_iff_identity_trace hj m).mpr
      (same.symm.trans (((w.successors k).zero_iff_identity_trace hj m).mp wrap))
    rw [t.residue_successors] at ht
    have small : t.residue m+k < M*2 := by dsimp [k]; omega
    rcases multiple_below_twice small ht with impossible|found <;> dsimp [k] at * <;> omega
  · intro same
    have left := dyadic_trace hj w m
    rw [same] at left
    exact left.trans (dyadic_trace hj t m).symm

def wordTraceSetoid {j : Emb height} (hj : IsWitness j) (m : Nat) : Setoid Word where
  r w t := TraceEq (dyadicPoint hj m) (w.embedding hj.1 j) (t.embedding hj.1 j)
  iseqv := ⟨fun _ => .refl _ _, fun h => h.symm, fun h k => h.trans k⟩

def finiteClass {j : Emb height} (hj : IsWitness j) (m : Nat) :
    Quotient (wordTraceSetoid hj m) → Fin (2^m) :=
  Quotient.lift (fun w => ⟨w.residue m,w.residue_lt m⟩)
    (fun w t same => Fin.ext ((trace_iff_residue hj m w t).mp same))

noncomputable def finiteTraceEquiv {j : Emb height} (hj : IsWitness j) (m : Nat) :
    Quotient (wordTraceSetoid hj m) ≃ Fin (2^m) := by
  apply Equiv.ofBijective (finiteClass hj m)
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | _ w =>
      induction b using Quotient.inductionOn with | _ t =>
        intro same
        exact Quotient.sound ((trace_iff_residue hj m w t).mpr (congrArg Fin.val same))
  · intro r
    by_cases zero : r.val=0
    · let w := Word.power (2^m-1)
      refine ⟨Quotient.mk _ w,Fin.ext ?_⟩
      change (Word.power _).residue m = r.val
      rw [Word.residue_power,Nat.sub_add_cancel (Nat.two_pow_pos m),Nat.mod_self,zero]
    · let w := Word.power (r.val-1)
      refine ⟨Quotient.mk _ w,Fin.ext ?_⟩
      change (Word.power _).residue m = r.val
      rw [Word.residue_power,Nat.sub_add_cancel (by omega),Nat.mod_eq_of_lt r.isLt]

theorem finiteTraceEquiv_apply {j : Emb height} (hj : IsWitness j) (m : Nat) (w t : Word) :
    (finiteTraceEquiv hj m (Quotient.mk _ (w.app t))).val =
      (tables m).mul (finiteTraceEquiv hj m (Quotient.mk _ w)).val
        (finiteTraceEquiv hj m (Quotient.mk _ t)).val := rfl

private def initialPart (β : Below height) (x : Rank height) : Rank height :=
  ⟨x.val.sep (· ∈ (stage β).val), (ZFSet.rank_mono ZFSet.sep_subset).trans_lt x.property⟩

private theorem initialPart_bound (β : Below height) (x : Rank height) :
    (initialPart β x).val.rank ≤ β.val := by
  have within : (initialPart β x).val ⊆ (stage β).val := fun _ h => (ZFSet.mem_sep.mp h).2
  exact (ZFSet.rank_mono within).trans_eq (ZFSet.rank_vonNeumann _)

private theorem map_initialPart (a : Emb height) (β : Below height) (x y : Rank height) :
    y.val ∈ (a (initialPart β x)).val ↔ y.val ∈ (a x).val ∧ y.val ∈ (a (stage β)).val := by
  have D : RankDef (fun v : Fin 3 → Rank height => ∀ y : Rank height,
      y.val ∈ (v 0).val ↔ y.val ∈ (v 1).val ∧ y.val ∈ (v 2).val) := by
    apply RankDef.all1
    exact (RankDef.memV (Sum.inr ()) (Sum.inl 0)).iffD
      ((RankDef.memV (Sum.inr ()) (Sum.inl 1)).andD (RankDef.memV (Sum.inr ()) (Sum.inl 2)))
  exact ((D.transfer a ![initialPart β x,x,stage β]).mpr (fun _ => ZFSet.mem_sep)) y

/-- A common restriction to V_μ also determines traces above μ: it
    suffices for one image a(β), β<μ, to reach the desired cut. This is
    the change from ordinary agreement to membership agreement in A.3. -/
theorem trace_of_rank_agreement (hl : Order.IsSuccLimit height) (a b : Emb height) {μ θ β : Below height}
    (agree : ∀ x : Rank height, x.val.rank < μ.val → a x = b x)
    (small : β < μ) (reach : θ ≤ ordinalImage a β) : TraceEq θ a b := by
  intro x y _ hy
  have smallStage : (stage β).val.rank < μ.val := by
    change (ZFSet.vonNeumann β.val).rank < μ.val
    rwa [ZFSet.rank_vonNeumann]
  have stageSame := agree (stage β) smallStage
  have partSame := agree (initialPart β x) ((initialPart_bound β x).trans_lt small)
  have ya : y.val ∈ (a (stage β)).val := by
    rw [map_stage hl]
    exact ZFSet.mem_vonNeumann.mpr (hy.trans_le reach)
  have yb : y.val ∈ (b (stage β)).val := stageSame ▸ ya
  have one := map_initialPart a β x y
  have two := map_initialPart b β x y
  rw [partSame] at one
  exact ⟨fun h => (two.mp (one.mpr ⟨h,ya⟩)).1, fun h => (one.mp (two.mpr ⟨h,yb⟩)).1⟩

theorem residue_of_rank_agreement {j : Emb height} (hj : IsWitness j) (w t : Word) (m : Nat)
    {μ β : Below height} (agree : ∀ x : Rank height, x.val.rank < μ.val →
      w.embedding hj.1 j x = t.embedding hj.1 j x)
    (small : β < μ) (reach : dyadicPoint hj m ≤ ordinalImage (w.embedding hj.1 j) β) :
    w.residue m = t.residue m :=
  (trace_iff_residue hj m w t).mp (trace_of_rank_agreement hj.1 _ _ agree small reach)

#print axioms trace_iff_residue
#print axioms finiteTraceEquiv
#print axioms residue_of_rank_agreement
end Gamma11.RankI3
