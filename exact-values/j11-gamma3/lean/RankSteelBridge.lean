import RankReadout
import Comparator.Statement

/-! Translate the two presentations of a rank embedding. The underlying
sets are identical. In application, a cut on the rank of an ordered
pair and a cut on the rank of its first coordinate are cofinal families
of graph sections. -/
set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder FirstOrder.Language
variable {height : Ordinal.{u}}

private def steelLanguage : LaverTables.setLang →ᴸ membershipLanguage where
  onFunction := fun {_} x => nomatch x
  onRelation := fun {_} x => match x with | .mem => MembershipSymbol.mem

private instance : membershipLanguage.Structure (LaverTables.VSet height) :=
  inferInstanceAs (membershipLanguage.Structure (Rank height))

private instance : steelLanguage.IsExpansionOn (LaverTables.VSet height) where
  map_onFunction := fun {_} x => nomatch x
  map_onRelation := by intro n r xs; cases r; rfl

def asSteelEmbedding (a : Emb height) :
    LaverTables.VSet height ↪ₑ[LaverTables.setLang] LaverTables.VSet height where
  toFun := a
  map_formula' := by
    intro n φ x
    have mapped := a.map_formula (steelLanguage.onFormula φ) x
    exact (steelLanguage.realize_onFormula (M:=LaverTables.VSet height) φ (v:=a ∘ x)).symm.trans
      (mapped.trans (steelLanguage.realize_onFormula (M:=LaverTables.VSet height) φ (v:=x)))

abbrev asSteelFn (a : Emb height) : LaverTables.VSet height → LaverTables.VSet height := a

private noncomputable def graphCut (b : Emb height) (α : Below height) : Rank height :=
  ⟨LaverTables.graphInter (asSteelFn b) α.val,(LaverTables.rank_graphInter_le _ _).trans_lt α.property⟩

private theorem left_rank_lt_pair (x y : ZFSet.{u}) : x.rank < (ZFSet.pair x y).rank :=
  (ZFSet.rank_lt_of_mem (show x ∈ ({x} : ZFSet) by simp)).trans
    (ZFSet.rank_lt_of_mem (show ({x} : ZFSet) ∈ ZFSet.pair x y by simp [ZFSet.pair]))

private theorem cut_le_section (hl : Order.IsSuccLimit height) (b : Emb height) (α : Below height) :
    (graphCut b α).val ⊆ (sectionAt hl b α).val := by
  intro p hp
  unfold graphCut LaverTables.graphInter at hp
  rw [ZFSet.mem_sep] at hp
  obtain ⟨stageMem,x,rfl⟩ := hp
  exact ((sectionAt_spec hl b α) _).mpr ⟨x,b x,(left_rank_lt_pair ..).trans (ZFSet.mem_vonNeumann.mp stageMem),rfl,rfl⟩

private theorem section_le_cut (b : Emb height) {α : Below height} {s : Rank height}
    (hs : Restriction (graphOf b) α s) : s.val ⊆ (graphCut b ⟨s.val.rank,s.property⟩).val := by
  intro p hp
  obtain ⟨x,y,_,image,pair⟩ := (hs _).mp hp
  unfold graphCut LaverTables.graphInter
  rw [ZFSet.mem_sep]
  exact ⟨ZFSet.mem_vonNeumann.mpr (ZFSet.rank_lt_of_mem hp),x,
    pair.trans (congrArg (ZFSet.pair x.val) (congrArg Subtype.val image).symm)⟩

private theorem cut_reads (hl : Order.IsSuccLimit height) (a b : Emb height) (x y : Rank height) :
    (∃ (θ : Ordinal) (ht : θ<height), ZFSet.pair x.val y.val ∈ (a (graphCut b ⟨θ,ht⟩)).val) ↔
    applyEmb hl a b x=y := by
  change _ ↔ graphOf (applyEmb hl a b) x y
  rw [←application_eq]
  constructor
  · rintro ⟨θ,ht,hp⟩
    let α : Below height := ⟨θ,ht⟩
    exact ⟨α,_,_,sectionAt_spec hl b α,rfl,map_subset a (cut_le_section hl b α) hp⟩
  · rintro ⟨α,s,z,hs,(rfl : a s=z),hp⟩
    exact ⟨s.val.rank,s.property,map_subset a (section_le_cut b hs) hp⟩

theorem steel_app_eq (hl : Order.IsSuccLimit height) (a b : Emb height) :
    LaverTables.app (asSteelFn a) (asSteelFn b)=asSteelFn (applyEmb hl a b) := by
  classical
  funext x
  let P := fun y : Rank height => ∃ (θ : Ordinal) (ht : θ<height),
    ZFSet.pair x.val y.val ∈ (a (graphCut b ⟨θ,ht⟩)).val
  have h : ∃! y, P y := ⟨applyEmb hl a b x,(cut_reads ..).mpr rfl,fun y hy => ((cut_reads ..).mp hy).symm⟩
  unfold LaverTables.app
  change (if h : ∃! y, P y then h.choose else x)=_
  split
  next existsOne => exact ((cut_reads ..).mp existsOne.choose_spec.1).symm
  next absent => exact (absent h).elim

theorem steel_critical_eq (a : Emb height) {δ : Below height} (h : IsCritical (graphOf a) δ) :
    LaverTables.critOf (asSteelFn a)=δ.val := by
  let S := {ξ : Ordinal.{u} | ξ < LaverTables.mapOrd (asSteelFn a) ξ}
  have atPoint (β : Below height) : LaverTables.mapOrd (asSteelFn a) β.val=(ordinalImage a β).val := by
    rw [LaverTables.mapOrd,dif_pos (show β.val<height from β.property)]; rfl
  have mem : δ.val ∈ S := by
    change δ.val < LaverTables.mapOrd (asSteelFn a) δ.val
    rw [atPoint]; exact critical_moves a h
  apply le_antisymm (csInf_le' mem)
  apply le_csInf ⟨_,mem⟩
  intro ξ hx
  apply le_of_not_gt
  intro lt
  let β : Below height := ⟨ξ,lt.trans δ.property⟩
  have fixed := h.1 β lt
  change a (point β)=point β at fixed
  have fixβ : ordinalImage a β=β := point_injective ((ordinalImage_spec a β).symm.trans fixed)
  change β.val < LaverTables.mapOrd (asSteelFn a) β.val at hx
  rw [atPoint,fixβ] at hx
  exact lt_irrefl _ hx

#print axioms steel_app_eq
#print axioms steel_critical_eq
end Gamma11.RankI3
