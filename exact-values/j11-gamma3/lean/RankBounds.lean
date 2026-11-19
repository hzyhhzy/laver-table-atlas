import RankFormulas
import Mathlib.SetTheory.ZFC.VonNeumann

/-! A bounded rank certificate is a set of ordered pairs of objects and labels.
Every member of a labelled object must receive a member of its label. This
defines rank comparison with an ordinal inside V_λ itself. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder
variable {height : Ordinal.{u}}

noncomputable def stage (α : Below height) : Rank height :=
  ⟨ZFSet.vonNeumann α.val, by rw [ZFSet.rank_vonNeumann]; exact α.property⟩

noncomputable def relationSet (hl : Order.IsSuccLimit height) (x y : Rank height)
    (P : ZFSet.{u} → ZFSet.{u} → Prop) : Rank height :=
  ⟨ZFSet.pairSep P x.val y.val, by
    apply lt_of_le_of_lt (ZFSet.rank_mono (ZFSet.sep_subset (x := ZFSet.powerset
      (ZFSet.powerset (x.val ∪ y.val)))))
    rw [ZFSet.rank_powerset, ZFSet.rank_powerset, ZFSet.rank_union]
    exact hl.succ_lt (hl.succ_lt (max_lt x.property y.property))⟩

theorem relationSet_edge (hl : Order.IsSuccLimit height) (d r : Rank height)
    (P : ZFSet.{u} → ZFSet.{u} → Prop) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ (relationSet hl d r P).val ↔ x ∈ d.val ∧ y ∈ r.val ∧ P x y := by
  change _ ∈ ZFSet.pairSep P d.val r.val ↔ _
  rw [ZFSet.mem_pairSep]
  constructor
  · rintro ⟨x',hx,y',hy,e,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp e
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨x,hx,y,hy,rfl,h⟩

def DescendingLabels (s : Rank height) : Prop :=
  ∀ x b : Rank height, ZFSet.pair x.val b.val ∈ s.val →
    ∀ y : Rank height, y.val ∈ x.val →
      ∃ c : Rank height, c.val ∈ b.val ∧ ZFSet.pair y.val c.val ∈ s.val

def LabelledBelow (x a : Rank height) : Prop :=
  ∃ s : Rank height, DescendingLabels s ∧ ∃ b : Rank height,
    b.val ∈ a.val ∧ ZFSet.pair x.val b.val ∈ s.val

namespace RankDef
variable {ι : Type} (hl : Order.IsSuccLimit height)
include hl

theorem descendingD (s : ι) :
    RankDef (fun v : ι → Rank height => DescendingLabels (v s)) := by
  unfold DescendingLabels
  apply all1
  apply all1
  let x : (ι ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let b : (ι ⊕ Unit) ⊕ Unit := Sum.inr ()
  let graph : (ι ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl s)
  apply (edgeD hl x b graph).impD
  apply all1
  apply (memV (Sum.inr ()) (Sum.inl x)).impD
  apply ex1
  exact (memV (Sum.inr ()) (Sum.inl (Sum.inl b))).andD
    (edgeD hl (Sum.inl (Sum.inr ())) (Sum.inr ()) (Sum.inl (Sum.inl graph)))

theorem labelledBelowD (x a : ι) :
    RankDef (fun v : ι → Rank height => LabelledBelow (v x) (v a)) := by
  unfold LabelledBelow
  apply ex1
  apply (descendingD hl (Sum.inr ())).andD
  apply ex1
  exact (memV (Sum.inr ()) (Sum.inl (Sum.inl a))).andD
    (edgeD hl (Sum.inl (Sum.inl x)) (Sum.inr ()) (Sum.inl (Sum.inr ())))
end RankDef

theorem DescendingLabels.rank_le {s : Rank height} (h : DescendingLabels s)
    (x b : Rank height) (hx : ZFSet.pair x.val b.val ∈ s.val) : x.val.rank ≤ b.val.rank := by
  apply ZFSet.rank_le_iff.mpr
  intro y hy
  obtain ⟨c,hc,hedge⟩ := h x b hx (rankMember x hy) hy
  exact (h.rank_le (rankMember x hy) c hedge).trans_lt (ZFSet.rank_lt_of_mem hc)
termination_by b.val.rank
decreasing_by exact ZFSet.rank_lt_of_mem hc

theorem labelledBelow_iff (hl : Order.IsSuccLimit height) (x : Rank height) (α : Below height) :
    LabelledBelow x (point α) ↔ x.val.rank < α.val := by
  constructor
  · rintro ⟨s,desc,b,hb,hx⟩
    have bound := (desc.rank_le x b hx).trans_lt (ZFSet.rank_lt_of_mem hb)
    simpa [point] using bound
  · intro hx
    let r (u v : ZFSet.{u}) := u.rank.toZFSet = v
    let s := relationSet hl (stage α) (point α) r
    have label (y : Rank height) (hy : y.val.rank < α.val) :
        ZFSet.pair y.val y.val.rank.toZFSet ∈ s.val :=
      (relationSet_edge hl (stage α) (point α) r _ _).mpr
        ⟨ZFSet.mem_vonNeumann.mpr hy, Ordinal.toZFSet_mem_toZFSet_iff.mpr hy,rfl⟩
    refine ⟨s, ?_, point ⟨x.val.rank,x.property⟩, Ordinal.toZFSet_mem_toZFSet_iff.mpr hx, label x hx⟩
    intro u b hedge v hv
    obtain ⟨hu,_,hr⟩ := (relationSet_edge hl (stage α) (point α) r _ _).mp hedge
    have hvu := ZFSet.rank_lt_of_mem hv
    refine ⟨point ⟨v.val.rank,v.property⟩, ?_, label v (hvu.trans (ZFSet.mem_vonNeumann.mp hu))⟩
    change v.val.rank.toZFSet ∈ b.val
    rw [← show u.val.rank.toZFSet = b.val from hr]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hvu

theorem map_rank_cut (hl : Order.IsSuccLimit height) (a : Emb height)
    (x : Rank height) (α : Below height) :
    (a x).val.rank < (ordinalImage a α).val ↔ x.val.rank < α.val := by
  let v : Fin 2 → Rank height := ![x, point α]
  have t := (RankDef.labelledBelowD hl (0 : Fin 2) 1).transfer a v
  change LabelledBelow (a x) (a (point α)) ↔ LabelledBelow x (point α) at t
  rwa [ordinalImage_spec, labelledBelow_iff hl, labelledBelow_iff hl] at t

theorem map_stage (hl : Order.IsSuccLimit height) (a : Emb height) (α : Below height) :
    a (stage α) = stage (ordinalImage a α) := by
  have D : RankDef (fun v : Fin 2 → Rank height => ∀ z : Rank height,
      z.val ∈ (v 0).val ↔ LabelledBelow z (v 1)) := by
    apply RankDef.all1
    exact (RankDef.memV (Sum.inr ()) (Sum.inl 0)).iffD
      (RankDef.labelledBelowD hl (Sum.inr ()) (Sum.inl 1))
  let v : Fin 2 → Rank height := ![stage α,point α]
  have old : ∀ z : Rank height, z.val ∈ (stage α).val ↔ LabelledBelow z (point α) :=
    fun z => ZFSet.mem_vonNeumann.trans (labelledBelow_iff hl z α).symm
  have new := (D.transfer a v).mpr old
  apply (rank_ext_iff _ _).mpr
  intro z
  have read := new z
  change z.val ∈ (a (stage α)).val ↔ LabelledBelow z (a (point α)) at read
  rw [ordinalImage_spec] at read
  exact read.trans ((labelledBelow_iff hl _ _).trans ZFSet.mem_vonNeumann.symm)

/-- Even if the height has countable cofinality, the image of each particular
    set has exactly the image of its rank. The upper cut is tested at the
    successor of that rank, which is still strictly below the height. -/
theorem map_set_rank (hl : Order.IsSuccLimit height) (a : Emb height) (x : Rank height) :
    (a x).val.rank = (ordinalImage a ⟨x.val.rank,x.property⟩).val := by
  let α : Below height := ⟨x.val.rank,x.property⟩
  let β : Below height := ⟨Order.succ α.val,hl.succ_lt α.property⟩
  have upper := (map_rank_cut hl a x β).mpr (Order.lt_succ α.val)
  have lower : ¬ (a x).val.rank < (ordinalImage a α).val :=
    fun h => (lt_irrefl α.val) ((map_rank_cut hl a x α).mp h)
  have noMiddle : ¬ ∃ z : Rank height, z.val ∈ (a (point β)).val ∧ z.val ∉ (a (point α)).val ∧
      z ≠ a (point α) := by
    have bound : ∀ z : Rank height, z.val ∈ (point β).val →
        z.val ∈ (point α).val ∨ z = point α := by
      intro z hz
      obtain ⟨t,ht,eqv⟩ := Ordinal.mem_toZFSet_iff.mp hz
      rcases (Order.lt_succ_iff.mp ht).lt_or_eq with less|same
      · exact Or.inl (eqv ▸ Ordinal.toZFSet_mem_toZFSet_iff.mpr less)
      · exact Or.inr (Subtype.ext (eqv.symm.trans (congrArg Ordinal.toZFSet same)))
    let v : Fin 2 → Rank height := ![point α,point β]
    have D : RankDef (fun w : Fin 2 → Rank height => ∀ z : Rank height,
        z.val ∈ (w 1).val → z.val ∈ (w 0).val ∨ z = w 0) := by
      apply RankDef.all1
      exact (RankDef.memV (Sum.inr ()) (Sum.inl 1)).impD
        ((RankDef.memV (Sum.inr ()) (Sum.inl 0)).orD (RankDef.eqV (Sum.inr ()) (Sum.inl 0)))
    have mapped := (D.transfer a v).mpr bound
    exact fun ⟨z,hz,h₁,h₂⟩ => (mapped z hz).elim h₁ h₂
  apply le_antisymm _ (le_of_not_gt lower)
  by_contra! h
  let z := point (⟨(a x).val.rank,(a x).property⟩ : Below height)
  apply noMiddle
  rw [ordinalImage_spec a β, ordinalImage_spec a α]
  refine ⟨z,Ordinal.toZFSet_mem_toZFSet_iff.mpr upper,?_,?_⟩
  · exact fun hm => lower (Ordinal.toZFSet_mem_toZFSet_iff.mp hm)
  · intro eqv
    exact h.ne' (Ordinal.toZFSet_injective (congrArg Subtype.val eqv))

private theorem fixed_of_preserves_ranks (j : Emb height)
    (ranks : ∀ x : Rank height, (j x).val.rank = x.val.rank) (x : Rank height) : j x = x := by
  apply (rank_ext_iff _ _).mpr
  intro z
  have mem : (j z).val ∈ (j x).val ↔ z.val ∈ x.val :=
    (RankDef.memV (0 : Fin 2) 1).transfer j ![z,x]
  by_cases l : z.val.rank < x.val.rank
  · rwa [fixed_of_preserves_ranks j ranks z] at mem
  · exact ⟨fun h => (l ((ZFSet.rank_lt_of_mem h).trans_eq (ranks x))).elim,
      fun h => (l (ZFSet.rank_lt_of_mem h)).elim⟩
termination_by x.val.rank
decreasing_by exact l

theorem generator_has_critical {j : Emb height} (hj : IsWitness j) :
    ∃ α, IsCritical (graphOf j) α := by
  classical
  apply critical_of_moved_point
  by_contra! allFixed
  have ranks (x : Rank height) : (j x).val.rank = x.val.rank := by
    have h := congrArg (fun z : Rank height => z.val.rank) (allFixed ⟨x.val.rank,x.property⟩)
    exact (map_set_rank hj.1 j x).trans (by simpa [ordinalImage,point] using h)
  exact hj.2.elim fun x moved => moved (fixed_of_preserves_ranks j ranks x)

#print axioms map_set_rank
#print axioms generator_has_critical
end Gamma11.RankI3
