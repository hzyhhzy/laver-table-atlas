import RankOrdinals

/-! First-order predicates on the actual membership structure of a limit rank.
The quantifier lemmas keep the ranks of all bound variables explicit. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder FirstOrder.Language
variable {height : Ordinal.{u}}

def RankDef {ι : Type} (P : (ι → Rank height) → Prop) : Prop :=
  ∃ φ : membershipLanguage.Formula ι, ∀ v, φ.Realize v ↔ P v

namespace RankDef
variable {ι : Type} {P Q : (ι → Rank height) → Prop}

theorem transfer (h : RankDef P) (a : Emb height) (v : ι → Rank height) :
    P (a ∘ v) ↔ P v := by
  obtain ⟨φ, read⟩ := h
  exact (read _).symm.trans ((a.map_formula φ v).trans (read _))

theorem congr (h : RankDef P) (e : ∀ v, P v ↔ Q v) : RankDef Q := by
  obtain ⟨φ, read⟩ := h
  exact ⟨φ, fun v => (read v).trans (e v)⟩

theorem eqV (i k : ι) : RankDef (fun v : ι → Rank height => v i = v k) :=
  ⟨(Term.var i).equal (.var k), fun _ => Formula.realize_equal⟩

theorem memV (i k : ι) : RankDef (fun v : ι → Rank height => (v i).val ∈ (v k).val) :=
  ⟨Relations.formula₂ (L := membershipLanguage) MembershipSymbol.mem (.var i) (.var k),
    fun _ => Formula.realize_rel₂⟩

theorem andD (p : RankDef P) (q : RankDef Q) : RankDef (fun v => P v ∧ Q v) := by
  obtain ⟨φ,f⟩ := p
  obtain ⟨ψ,g⟩ := q
  exact ⟨φ ⊓ ψ, fun v => Formula.realize_inf.trans (and_congr (f v) (g v))⟩

theorem orD (p : RankDef P) (q : RankDef Q) : RankDef (fun v => P v ∨ Q v) := by
  obtain ⟨φ,f⟩ := p
  obtain ⟨ψ,g⟩ := q
  exact ⟨φ ⊔ ψ, fun v => Formula.realize_sup.trans (or_congr (f v) (g v))⟩

theorem impD (p : RankDef P) (q : RankDef Q) : RankDef (fun v => P v → Q v) := by
  obtain ⟨φ,f⟩ := p
  obtain ⟨ψ,g⟩ := q
  exact ⟨φ.imp ψ, fun v => Formula.realize_imp.trans (imp_congr (f v) (g v))⟩

theorem iffD (p : RankDef P) (q : RankDef Q) : RankDef (fun v => P v ↔ Q v) := by
  obtain ⟨φ,f⟩ := p
  obtain ⟨ψ,g⟩ := q
  exact ⟨φ.iff ψ, fun v => Formula.realize_iff.trans (iff_congr (f v) (g v))⟩

theorem allD {κ : Type} [Finite κ] {R : (ι → Rank height) → (κ → Rank height) → Prop}
    (h : RankDef (fun v => R (v ∘ Sum.inl) (v ∘ Sum.inr))) :
    RankDef (fun v => ∀ z, R v z) := by
  obtain ⟨φ,f⟩ := h
  refine ⟨φ.iAlls κ, fun v => Formula.realize_iAlls.trans (forall_congr' fun z => ?_)⟩
  exact f (Sum.elim v z)

theorem all1 {R : (ι → Rank height) → Rank height → Prop}
    (h : RankDef (fun v : ι ⊕ Unit → Rank height => R (v ∘ Sum.inl) (v (Sum.inr ())))) :
    RankDef (fun v => ∀ z, R v z) := by
  obtain ⟨φ,f⟩ := h
  refine ⟨φ.iAlls Unit, fun v => Formula.realize_iAlls.trans ?_⟩
  exact ⟨fun h z => (f (Sum.elim v (fun _ => z))).mp (h _),
    fun h z => (f (Sum.elim v z)).mpr (h _)⟩

theorem ex1 {R : (ι → Rank height) → Rank height → Prop}
    (h : RankDef (fun v : ι ⊕ Unit → Rank height => R (v ∘ Sum.inl) (v (Sum.inr ())))) :
    RankDef (fun v => ∃ z, R v z) := by
  obtain ⟨φ,f⟩ := h
  refine ⟨φ.iExs Unit, fun v => Formula.realize_iExs.trans ?_⟩
  exact ⟨fun ⟨z,hz⟩ => ⟨z (), (f (Sum.elim v z)).mp hz⟩,
    fun ⟨z,hz⟩ => ⟨fun _ => z, (f (Sum.elim v (fun _ => z))).mpr hz⟩⟩

theorem finiteAnd {κ : Type} (s : Finset κ) {R : κ → (ι → Rank height) → Prop}
    (h : ∀ i ∈ s, RankDef (R i)) : RankDef (fun v => ∀ i ∈ s, R i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, fun _ => by simp⟩
  | insert i s _ ih =>
    have head := h i (Finset.mem_insert_self i s)
    have tail := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact (head.andD tail).congr (fun _ => by simp)

end RankDef

def rankMember (x : Rank height) {y : ZFSet} (h : y ∈ x.val) : Rank height :=
  ⟨y, (ZFSet.rank_lt_of_mem h).trans x.property⟩

theorem rank_ext_iff (x y : Rank height) :
    x = y ↔ ∀ z : Rank height, z.val ∈ x.val ↔ z.val ∈ y.val := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => (h (rankMember x hz)).mp hz, fun hz => (h (rankMember y hz)).mpr hz⟩

def unordered (hl : Order.IsSuccLimit height) (x y : Rank height) : Rank height :=
  ⟨{x.val, y.val}, by rw [ZFSet.rank_pair]; exact max_lt (hl.succ_lt x.property) (hl.succ_lt y.property)⟩

namespace RankDef
variable {ι : Type} (hl : Order.IsSuccLimit height)

theorem unorderedD (x y t : ι) :
    RankDef (fun v : ι → Rank height => v t = unordered hl (v x) (v y)) := by
  apply RankDef.congr (P := fun v => ∀ z : Rank height,
    z.val ∈ (v t).val ↔ z = v x ∨ z = v y)
  · apply all1
    exact (memV (Sum.inr ()) (Sum.inl t)).iffD ((eqV (Sum.inr ()) (Sum.inl x)).orD (eqV (Sum.inr ()) (Sum.inl y)))
  · intro v
    rw [rank_ext_iff]
    exact forall_congr' fun z => by simp [unordered, Subtype.ext_iff]

include hl in
theorem orderedD (x y t : ι) :
    RankDef (fun v : ι → Rank height => (v t).val = ZFSet.pair (v x).val (v y).val) := by
  apply RankDef.congr (P := fun v => ∃ a b : Rank height,
    a = unordered hl (v x) (v x) ∧ b = unordered hl (v x) (v y) ∧ v t = unordered hl a b)
  · apply ex1
    apply ex1
    let old (i : ι) : (ι ⊕ Unit) ⊕ Unit := .inl (Sum.inl i)
    exact (unorderedD hl (old x) (old x) (Sum.inl (Sum.inr ()))).andD
      ((unorderedD hl (old x) (old y) (Sum.inr ())).andD
        (unorderedD hl (Sum.inl (Sum.inr ())) (Sum.inr ()) (old t)))
  · intro v
    simp [Subtype.ext_iff, unordered, ZFSet.pair, ZFSet.pair_eq_singleton]

include hl in
theorem edgeD (x y s : ι) :
    RankDef (fun v : ι → Rank height => ZFSet.pair (v x).val (v y).val ∈ (v s).val) := by
  apply RankDef.congr (P := fun v => ∃ p : Rank height,
    p.val = ZFSet.pair (v x).val (v y).val ∧ p.val ∈ (v s).val)
  · apply ex1
    exact (orderedD hl (Sum.inl x) (Sum.inl y) (Sum.inr ())).andD (memV (Sum.inr ()) (Sum.inl s))
  · intro v
    exact ⟨fun ⟨p,h,hm⟩ => h ▸ hm, fun h => ⟨rankMember (v s) h,rfl,h⟩⟩

theorem subsetD (x y : ι) :
    RankDef (fun v : ι → Rank height => (v x).val ⊆ (v y).val) := by
  apply RankDef.congr (P := fun v => ∀ z : Rank height, z.val ∈ (v x).val → z.val ∈ (v y).val)
  · apply all1
    exact (memV (Sum.inr ()) (Sum.inl x)).impD (memV (Sum.inr ()) (Sum.inl y))
  · exact fun v => ⟨fun h _ hm => h (rankMember (v x) hm) hm, fun h _ hm => h hm⟩
end RankDef
end Gamma11.RankI3
