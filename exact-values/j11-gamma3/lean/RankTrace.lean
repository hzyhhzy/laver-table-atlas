import RankAlgebra

/-! Laver's equivalence at a cut compares membership in images. At limit
cuts the traces of bounded rectangles lie strictly below the cut, giving
a congruence for application of actual elementary embeddings. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder
variable {height : Ordinal.{u}}

def identityEmb (height : Ordinal.{u}) : Emb height :=
  FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage (Rank height)

def TraceEq (θ : Below height) (a b : Emb height) : Prop :=
  ∀ x y : Rank height, x.val.rank < θ.val → y.val.rank < θ.val →
    (y.val ∈ (a x).val ↔ y.val ∈ (b x).val)

namespace TraceEq

@[refl] theorem refl (θ : Below height) (a : Emb height) : TraceEq θ a a :=
  fun _ _ _ _ => Iff.rfl

@[symm] theorem symm {θ : Below height} {a b : Emb height} (h : TraceEq θ a b) : TraceEq θ b a :=
  fun x y hx hy => (h x y hx hy).symm

@[trans] theorem trans {θ : Below height} {a b c : Emb height} (h : TraceEq θ a b) (k : TraceEq θ b c) :
    TraceEq θ a c := fun x y hx hy => (h x y hx hy).trans (k x y hx hy)

theorem mono {σ θ : Below height} {a b : Emb height} (h : TraceEq θ a b) (le : σ ≤ θ) :
    TraceEq σ a b := fun x y hx hy => h x y (hx.trans_le le) (hy.trans_le le)
end TraceEq

theorem fixes_set_below (hl : Order.IsSuccLimit height) (a : Emb height) (θ : Below height)
    (fixed : ∀ δ : Below height, δ < θ → a (point δ) = point δ)
    (x : Rank height) (hx : x.val.rank < θ.val) : a x = x := by
  have h := congrArg (fun z : Rank height => z.val.rank) (fixed ⟨x.val.rank,x.property⟩ hx)
  have ranks : (a x).val.rank = x.val.rank :=
    (map_set_rank hl a x).trans (by simpa [ordinalImage,point] using h)
  apply (rank_ext_iff _ _).mpr
  intro z
  by_cases l : z.val.rank < x.val.rank
  · have mem : (a z).val ∈ (a x).val ↔ z.val ∈ x.val :=
      (RankDef.memV (0 : Fin 2) 1).transfer a ![z,x]
    rwa [fixes_set_below hl a θ fixed z (l.trans hx)] at mem
  · exact ⟨fun hz => (l ((ZFSet.rank_lt_of_mem hz).trans_eq ranks)).elim,
      fun hz => (l (ZFSet.rank_lt_of_mem hz)).elim⟩
termination_by x.val.rank
decreasing_by exact l

theorem trace_identity_iff (hl : Order.IsSuccLimit height) (a : Emb height) (θ : Below height) :
    TraceEq θ a (identityEmb height) ↔ ∀ δ : Below height, δ < θ → a (point δ) = point δ := by
  constructor
  · intro h δ hd
    have below : (point δ).val.rank < θ.val := by change δ.val.toZFSet.rank < θ.val; rwa [Ordinal.rank_toZFSet]
    have mem := h (point δ) (point δ) below below
    change (point δ).val ∈ (a (point δ)).val ↔ (point δ).val ∈ (point δ).val at mem
    rw [ordinalImage_spec] at mem ⊢
    have no : ¬ δ < ordinalImage a δ :=
      fun hr => (lt_irrefl δ.val) (Ordinal.toZFSet_mem_toZFSet_iff.mp
        (mem.mp (Ordinal.toZFSet_mem_toZFSet_iff.mpr hr)))
    exact congrArg point (le_antisymm (le_of_not_gt no) (ordinalImage_strictMono a).le_apply)
  · intro h x y hx _
    rw [fixes_set_below hl a θ h x hx]
    rfl

private noncomputable def traceSet (hl : Order.IsSuccLimit height) (b : Emb height) (α : Below height) :
    Rank height := relationSet hl (stage α) (stage α)
      (fun u v => ∃ x : Rank height, x.val = u ∧ v ∈ (b x).val)

private theorem trace_edge (hl : Order.IsSuccLimit height) (b : Emb height) (α : Below height)
    (x y : Rank height) (hx : x.val ∈ (stage α).val) (hy : y.val ∈ (stage α).val) :
    ZFSet.pair x.val y.val ∈ (traceSet hl b α).val ↔ y.val ∈ (b x).val := by
  rw [traceSet, relationSet_edge]
  constructor
  · rintro ⟨_,_,z,eqv,hm⟩
    obtain rfl : z = x := Subtype.ext eqv
    exact hm
  · exact fun h => ⟨hx,hy,x,rfl,h⟩

private theorem trace_set_eq (hl : Order.IsSuccLimit height) {b c : Emb height} {θ : Below height}
    (h : TraceEq θ b c) (α : Below height) (within : α ≤ θ) : traceSet hl b α = traceSet hl c α := by
  apply Subtype.ext
  apply ZFSet.ext
  intro p
  change p ∈ ZFSet.pairSep _ _ _ ↔ p ∈ ZFSet.pairSep _ _ _
  rw [ZFSet.mem_pairSep,ZFSet.mem_pairSep]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  apply and_congr_right
  intro _
  apply exists_congr
  intro z
  apply and_congr_right
  rintro rfl
  exact h z (rankMember (stage α) hy) ((ZFSet.mem_vonNeumann.mp hx).trans_le within)
    ((ZFSet.mem_vonNeumann.mp hy).trans_le within)

private theorem linksD (hl : Order.IsSuccLimit height) :
    RankDef (fun v : Fin 3 → Rank height => ∀ x y : Rank height,
      x.val ∈ (v 0).val → y.val ∈ (v 0).val →
      (ZFSet.pair x.val y.val ∈ (v 2).val ↔ ∃ z : Rank height,
        ZFSet.pair x.val z.val ∈ (v 1).val ∧ y.val ∈ z.val)) := by
  apply RankDef.all1
  apply RankDef.all1
  let old (i : Fin 3) : (Fin 3 ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl i)
  let x : (Fin 3 ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let y : (Fin 3 ⊕ Unit) ⊕ Unit := Sum.inr ()
  apply (RankDef.memV x (old 0)).impD
  apply (RankDef.memV y (old 0)).impD
  apply (RankDef.edgeD hl x y (old 2)).iffD
  apply RankDef.ex1
  exact (RankDef.edgeD hl (Sum.inl x) (Sum.inr ()) (Sum.inl (old 1))).andD
    (RankDef.memV (Sum.inl y) (Sum.inr ()))

private theorem read_trace (hl : Order.IsSuccLimit height) (a b : Emb height) (α : Below height)
    (x y : Rank height) (hx : x.val.rank < (ordinalImage a α).val) (hy : y.val.rank < (ordinalImage a α).val) :
    ZFSet.pair x.val y.val ∈ (a (traceSet hl b α)).val ↔ y.val ∈ (applyEmb hl a b x).val := by
  let s := sectionAt hl b α
  let t := traceSet hl b α
  let v : Fin 3 → Rank height := ![stage α,s,t]
  have old : ∀ x y : Rank height, x.val ∈ (stage α).val → y.val ∈ (stage α).val →
      (ZFSet.pair x.val y.val ∈ t.val ↔ ∃ z : Rank height, ZFSet.pair x.val z.val ∈ s.val ∧ y.val ∈ z.val) := by
    intro x y hx hy
    rw [trace_edge hl b α x y hx hy]
    constructor
    · exact fun h => ⟨b x,((sectionAt_spec hl b α).edge _ _).mpr ⟨ZFSet.mem_vonNeumann.mp hx,rfl⟩,h⟩
    · rintro ⟨z,hedge,hm⟩
      have eqv : b x = z := (((sectionAt_spec hl b α).edge _ _).mp hedge).2
      rwa [eqv]
  have h := ((linksD hl).transfer a v).mpr old
  have dom {z : Rank height} (hz : z.val.rank < (ordinalImage a α).val) : z.val ∈ (a (stage α)).val := by
    rw [map_stage hl]
    exact ZFSet.mem_vonNeumann.mpr hz
  refine (h x y (dom hx) (dom hy)).trans ?_
  have natural := section_natural hl a b α
  change (∃ z : Rank height, ZFSet.pair x.val z.val ∈ (a (sectionAt hl b α)).val ∧ y.val ∈ z.val) ↔ _
  rw [natural]
  have e := sectionAt_spec hl (applyEmb hl a b) (ordinalImage a α)
  constructor
  · rintro ⟨z,hz,hyz⟩
    have eqv : applyEmb hl a b x = z := ((e.edge _ _).mp hz).2
    rwa [eqv]
  · intro hyx
    exact ⟨_,(e.edge _ _).mpr ⟨hx,rfl⟩,hyx⟩

theorem TraceEq.map_right (hl : Order.IsSuccLimit height) {θ : Below height} {b c : Emb height}
    (h : TraceEq θ b c) (a : Emb height) :
    TraceEq (ordinalImage a θ) (applyEmb hl a b) (applyEmb hl a c) := by
  intro x y hx hy
  rw [← read_trace hl a b θ x y hx hy, ← read_trace hl a c θ x y hx hy, trace_set_eq hl h θ le_rfl]

/-- Equality of traces at θ survives application in both arguments. Only
    bounded traces of much smaller rectangles are used as parameters. -/
theorem TraceEq.app (hl : Order.IsSuccLimit height) {θ : Below height}
    (limit : Order.IsSuccPrelimit θ.val) {a a' b b' : Emb height}
    (ha : TraceEq θ a a') (hb : TraceEq θ b b') :
    TraceEq θ (applyEmb hl a b) (applyEmb hl a' b') := by
  intro x y hx hy
  let m := max x.val.rank y.val.rank
  have hm : m < θ.val := max_lt hx hy
  let α : Below height := ⟨Order.succ m,(limit.succ_lt hm).trans θ.property⟩
  have hal : α.val < θ.val := limit.succ_lt hm
  have ax : x.val.rank < α.val := (le_max_left _ _).trans_lt (Order.lt_succ m)
  have ay : y.val.rank < α.val := (le_max_right _ _).trans_lt (Order.lt_succ m)
  have small : (traceSet hl b α).val.rank < θ.val := by
    have subset : (traceSet hl b α).val ⊆ ZFSet.powerset (ZFSet.powerset ((stage α).val ∪ (stage α).val)) := by
      intro p hp
      simp only [traceSet,relationSet,ZFSet.pairSep,ZFSet.mem_sep] at hp
      exact hp.1
    apply (ZFSet.rank_mono subset).trans_lt
    rw [ZFSet.rank_powerset,ZFSet.rank_powerset,ZFSet.rank_union,max_self]
    change Order.succ (Order.succ (ZFSet.vonNeumann α.val).rank) < θ.val
    rw [ZFSet.rank_vonNeumann]
    exact limit.succ_lt (limit.succ_lt hal)
  have hp : (ZFSet.pair x.val y.val).rank < θ.val := by
    simp only [ZFSet.pair,ZFSet.rank_pair,ZFSet.rank_singleton]
    exact max_lt (limit.succ_lt (limit.succ_lt hx))
      (limit.succ_lt (max_lt (limit.succ_lt hx) (limit.succ_lt hy)))
  have t := ha (traceSet hl b α) ⟨_,hp.trans θ.property⟩ small hp
  have same := trace_set_eq hl hb α hal.le
  have up (e : Emb height) : α.val ≤ (ordinalImage e α).val := (ordinalImage_strictMono e).le_apply
  exact (read_trace hl a b α x y (ax.trans_le (up a)) (ay.trans_le (up a))).symm.trans
    (t.trans (by rw [same]; exact read_trace hl a' b' α x y (ax.trans_le (up a')) (ay.trans_le (up a'))))

theorem identity_apply (hl : Order.IsSuccLimit height) (b : Emb height) :
    applyEmb hl (identityEmb height) b = b :=
  DFunLike.ext _ _ (fun x => applyEmb_commutes hl (identityEmb height) b x)

theorem apply_identity (hl : Order.IsSuccLimit height) (a : Emb height) :
    applyEmb hl a (identityEmb height) = identityEmb height := by
  apply DFunLike.ext
  intro x
  let b := identityEmb height
  let y := applyEmb hl a b x
  have rel : application (graphOf a) (graphOf b) x y := by rw [application_eq hl]; rfl
  obtain ⟨α,s,_,hs,rfl,edge⟩ := rel
  have D : RankDef (fun v : Unit → Rank height => ∀ t u : Rank height,
      ZFSet.pair t.val u.val ∈ (v ()).val → u = t) := by
    apply RankDef.all1
    apply RankDef.all1
    exact (RankDef.edgeD hl (Sum.inl (Sum.inr ())) (Sum.inr ()) (Sum.inl (Sum.inl ()))).impD
      (RankDef.eqV (Sum.inr ()) (Sum.inl (Sum.inr ())))
  have h : ∀ t u : Rank height, ZFSet.pair t.val u.val ∈ s.val → u = t :=
    fun t u e => ((hs.edge _ _).mp e).2.symm
  exact ((D.transfer a (fun _ => s)).mpr h) x y edge

private def nextOrdinal (hl : Order.IsSuccLimit height) (δ : Below height) : Below height :=
  ⟨Order.succ δ.val,hl.succ_lt δ.property⟩

private theorem mem_next (hl : Order.IsSuccLimit height) (δ : Below height) (x : Rank height) :
    x.val ∈ (point (nextOrdinal hl δ)).val ↔ x = point δ ∨ x.val ∈ (point δ).val := by
  change x.val ∈ (δ.val + 1).toZFSet ↔ _
  rw [Ordinal.toZFSet_add_one,ZFSet.mem_insert_iff]
  exact or_congr ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩ Iff.rfl

private theorem map_next (hl : Order.IsSuccLimit height) (a : Emb height) (δ : Below height) :
    a (point (nextOrdinal hl δ)) = point (nextOrdinal hl (ordinalImage a δ)) := by
  have D : RankDef (fun v : Fin 2 → Rank height => ∀ x : Rank height,
      x.val ∈ (v 1).val ↔ x = v 0 ∨ x.val ∈ (v 0).val) := by
    apply RankDef.all1
    exact (RankDef.memV (Sum.inr ()) (Sum.inl 1)).iffD
      ((RankDef.eqV (Sum.inr ()) (Sum.inl 0)).orD (RankDef.memV (Sum.inr ()) (Sum.inl 0)))
  have h := (D.transfer a ![point δ,point (nextOrdinal hl δ)]).mpr (mem_next hl δ)
  apply (rank_ext_iff _ _).mpr
  intro x
  have read := h x
  change x.val ∈ (a (point (nextOrdinal hl δ))).val ↔ x = a (point δ) ∨ x.val ∈ (a (point δ)).val at read
  rw [ordinalImage_spec a δ] at read
  exact read.trans (mem_next hl _ _).symm

theorem critical_prelimit (hl : Order.IsSuccLimit height) (a : Emb height) {θ : Below height}
    (h : IsCritical (graphOf a) θ) : Order.IsSuccPrelimit θ.val := by
  apply Order.isSuccPrelimit_of_succ_lt
  intro δ hδ
  apply lt_of_le_of_ne (Order.succ_le_of_lt hδ)
  intro same
  let t : Below height := ⟨δ,hδ.trans θ.property⟩
  have te : nextOrdinal hl t = θ := Subtype.ext same
  have fixed : ordinalImage a t = t := by
    apply Subtype.ext
    exact (congrArg (fun x : Rank height => x.val.rank) (h.1 t hδ)).trans (Ordinal.rank_toZFSet _)
  have atθ := map_next hl a t
  rw [fixed,te] at atθ
  obtain ⟨v,hv,ev⟩ := h.2
  have pe : (point θ).val = (point v).val := congrArg Subtype.val (atθ.symm.trans ev)
  exact hv.ne (Subtype.ext (Ordinal.toZFSet_injective pe))

#print axioms TraceEq.app
end Gamma11.RankI3
