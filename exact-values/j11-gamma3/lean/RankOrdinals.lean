import RankI3

/-! Ordinal points and the least moved one for an actual elementary
    embedding of the membership structure on V_height. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder FirstOrder.Language

private abbrev boundVar {n : Nat} (i : Fin n) : membershipLanguage.Term (Unit ⊕ Fin n) :=
  .var (.inr i)

private abbrev freePoint {n : Nat} : membershipLanguage.Term (Unit ⊕ Fin n) :=
  .var (.inl ())

private abbrev belongs {n : Nat} (l r : membershipLanguage.Term (Unit ⊕ Fin n)) :
    membershipLanguage.BoundedFormula Unit n :=
  Language.Relations.boundedFormula₂ (L := membershipLanguage) MembershipSymbol.mem l r

private def ordinalFormula : membershipLanguage.Formula Unit :=
  (.all (.all ((belongs (boundVar 1) (boundVar 0)).imp
    ((belongs (boundVar 0) freePoint).imp (belongs (boundVar 1) freePoint))))) ⊓
  (.all (.all (.all ((belongs (boundVar 0) freePoint).imp
    ((belongs (boundVar 2) (boundVar 1)).imp
      ((belongs (boundVar 1) (boundVar 0)).imp (belongs (boundVar 2) (boundVar 0))))))))

private def memberOfRank {height : Ordinal.{u}} (x : Rank height) {y : ZFSet}
    (member : y ∈ x.val) : Rank height :=
  ⟨y, (ZFSet.rank_lt_of_mem member).trans x.property⟩

/-- The absolute characterization used here is a transitive set of
    transitive sets. Every witness to failure already lies in V_height. -/
private theorem ordinalFormula_spec {height : Ordinal.{u}} (v : Unit → Rank height) :
    ordinalFormula.Realize v ↔ (v ()).val.IsOrdinal := by
  change (_ ⊓ _ : membershipLanguage.BoundedFormula Unit 0).Realize v default ↔ _
  rw [BoundedFormula.realize_inf, ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  change ((∀ y z : Rank height, z.val ∈ y.val → y.val ∈ (v ()).val → z.val ∈ (v ()).val) ∧
    (∀ y z w : Rank height, y.val ∈ (v ()).val → w.val ∈ z.val → z.val ∈ y.val → w.val ∈ y.val)) ↔ _
  constructor
  · rintro ⟨t,members⟩
    constructor
    · apply ZFSet.isTransitive_iff_mem_trans.mpr
      intro z y zy yx
      let yr := memberOfRank (v ()) yx
      exact t yr (memberOfRank yr zy) zy yx
    · intro y yx
      apply ZFSet.isTransitive_iff_mem_trans.mpr
      intro w z wz zy
      let yr := memberOfRank (v ()) yx
      let zr := memberOfRank yr zy
      exact members yr zr (memberOfRank zr wz) yx wz zy
  · rintro ⟨t,members⟩
    exact ⟨fun _ _ zy yx => t.mem_trans zy yx,
      fun y _ _ yx wz zy => (members y.val yx).mem_trans wz zy⟩

theorem maps_ordinals {height : Ordinal.{u}} (j : Emb height) (x : Rank height) :
    (j x).val.IsOrdinal ↔ x.val.IsOrdinal := by
  let v := fun _ : Unit => x
  exact (ordinalFormula_spec (j ∘ v)).symm.trans
    ((j.map_formula ordinalFormula v).trans (ordinalFormula_spec v))

noncomputable def ordinalImage {height : Ordinal.{u}} (j : Emb height) (α : Below height) : Below height :=
  ⟨(j (point α)).val.rank, (j (point α)).property⟩

theorem ordinalImage_spec {height : Ordinal.{u}} (j : Emb height) (α : Below height) :
    j (point α) = point (ordinalImage j α) := by
  apply Subtype.ext
  exact ((maps_ordinals j (point α)).mpr (ZFSet.isOrdinal_toZFSet α.val)).toZFSet_rank_eq.symm

theorem ordinalImage_strictMono {height : Ordinal.{u}} (j : Emb height) : StrictMono (ordinalImage j) := by
  intro α β lt
  let v : Fin 2 → Rank height := ![point α, point β]
  have read := j.map_rel MembershipSymbol.mem v
  change (j (point α)).val ∈ (j (point β)).val ↔ (point α).val ∈ (point β).val at read
  have member := read.mpr (Ordinal.toZFSet_mem_toZFSet_iff.mpr lt)
  rw [ordinalImage_spec j α, ordinalImage_spec j β] at member
  exact Ordinal.toZFSet_mem_toZFSet_iff.mp member

/-- A single moved ordinal suffices. The well-order of the ordinals gives
    the least one and order preservation forces its image strictly upward. -/
theorem critical_of_moved_point {height : Ordinal.{u}} (j : Emb height)
    (moved : ∃ α : Below height, j (point α) ≠ point α) : ∃ α, IsCritical (graphOf j) α := by
  classical
  let S := {α : Below height | j (point α) ≠ point α}
  obtain ⟨α,hα,first⟩ := wellFounded_lt.has_min S moved
  refine ⟨α, ?_, ordinalImage j α, ?_, ordinalImage_spec j α⟩
  · intro β earlier
    by_contra h
    exact first β h earlier
  · apply lt_of_le_of_ne (ordinalImage_strictMono j).le_apply
    intro eqv
    apply hα
    rw [ordinalImage_spec j α, ← eqv]

#print axioms critical_of_moved_point
end Gamma11.RankI3
