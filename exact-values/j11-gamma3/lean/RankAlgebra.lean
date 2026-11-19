import RankApplication

/-! Naturality of the actual bounded graph, and the resulting
left-distributive law for application. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder
variable {height : Ordinal.{u}}

private theorem edges_with_domainD (hl : Order.IsSuccLimit height) :
    RankDef (fun v : Fin 2 → Rank height => ∀ p : Rank height, p.val ∈ (v 1).val →
      ∃ x y : Rank height, x.val ∈ (v 0).val ∧ p.val = ZFSet.pair x.val y.val) := by
  apply RankDef.all1
  apply (RankDef.memV (Sum.inr ()) (Sum.inl 1)).impD
  apply RankDef.ex1
  apply RankDef.ex1
  let x : ((Fin 2 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let y : ((Fin 2 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inr ()
  let p : ((Fin 2 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl (Sum.inr ()))
  exact (RankDef.memV x (Sum.inl (Sum.inl (Sum.inl 0)))).andD (RankDef.orderedD hl x y p)

theorem section_natural (hl : Order.IsSuccLimit height) (a b : Emb height) (α : Below height) :
    a (sectionAt hl b α) = sectionAt hl (applyEmb hl a b) (ordinalImage a α) := by
  let s := sectionAt hl b α
  have onlyEdges : ∀ p : Rank height, p.val ∈ s.val →
      ∃ x y : Rank height, x.val ∈ (stage α).val ∧ p.val = ZFSet.pair x.val y.val := by
    intro p hp
    obtain ⟨x,y,hx,_,pair⟩ := ((sectionAt_spec hl b α) _).mp hp
    exact ⟨x,y,ZFSet.mem_vonNeumann.mpr hx,pair⟩
  have mapped := ((edges_with_domainD hl).transfer a ![stage α,s]).mpr onlyEdges
  apply Subtype.ext
  apply ZFSet.ext
  intro p
  rw [sectionAt_spec hl (applyEmb hl a b) (ordinalImage a α)]
  constructor
  · intro hp
    obtain ⟨x,y,hx,pair⟩ := mapped (rankMember (a s) hp) hp
    change x.val ∈ (a (stage α)).val at hx
    rw [map_stage hl] at hx
    change p = ZFSet.pair x.val y.val at pair
    refine ⟨x,y,ZFSet.mem_vonNeumann.mp hx,?_,pair⟩
    rw [← application_eq]
    exact ⟨α,s,a s,sectionAt_spec hl b α,rfl,pair ▸ hp⟩
  · rintro ⟨x,y,hx,rel,rfl⟩
    obtain ⟨z,edge⟩ := image_section_total hl a b α x hx
    have yz : y = z := rel.symm.trans (by
      change graphOf (applyEmb hl a b) x z
      rw [← application_eq]
      exact ⟨α,s,a s,sectionAt_spec hl b α,rfl,edge⟩)
    exact yz ▸ edge

theorem applyEmb_ld (hl : Order.IsSuccLimit height) (a b c : Emb height) :
    applyEmb hl a (applyEmb hl b c) = applyEmb hl (applyEmb hl a b) (applyEmb hl a c) := by
  apply DFunLike.ext
  intro x
  let α : Below height := ⟨Order.succ x.val.rank,hl.succ_lt x.property⟩
  let β := ordinalImage b α
  let s := sectionAt hl c α
  have ab : α ≤ β := (ordinalImage_strictMono b).le_apply
  have ar : β ≤ ordinalImage a β := (ordinalImage_strictMono a).le_apply
  obtain ⟨y,edge⟩ := image_section_total hl a (applyEmb hl b c) β x
    ((Order.lt_succ x.val.rank).trans_le (ab.trans ar))
  have left : applyEmb hl a (applyEmb hl b c) x = y := by
    change graphOf (applyEmb hl a (applyEmb hl b c)) x y
    rw [← application_eq]
    exact ⟨β,_,_,sectionAt_spec hl _ β,rfl,edge⟩
  rw [left]
  symm
  change graphOf (applyEmb hl (applyEmb hl a b) (applyEmb hl a c)) x y
  rw [← application_eq]
  have restricted : Restriction (graphOf (applyEmb hl a c)) (ordinalImage a α) (a s) := by
    dsimp only [s]
    rw [section_natural]
    exact sectionAt_spec hl _ _
  refine ⟨ordinalImage a α,a s,a (b s),restricted,applyEmb_commutes hl a b s,?_⟩
  change ZFSet.pair x.val y.val ∈ (a (b (sectionAt hl c α))).val
  rwa [section_natural hl b c]

#print axioms section_natural
#print axioms applyEmb_ld
end Gamma11.RankI3
