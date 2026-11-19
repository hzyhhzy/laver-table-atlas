import RankBounds

/-! Application of actual elementary embeddings on a limit rank. Each
restriction lives in the same rank. Its image is a partial elementary map,
and the images of these restrictions agree on overlapping domains. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open FirstOrder FirstOrder.Language
variable {height : Ordinal.{u}}

noncomputable def sectionAt (hl : Order.IsSuccLimit height) (b : Emb height) (α : Below height) :
    Rank height :=
  relationSet hl (stage α) (stage (ordinalImage b α))
    (fun x y => ∃ u : Rank height, u.val = x ∧ (b u).val = y)

theorem sectionAt_spec (hl : Order.IsSuccLimit height) (b : Emb height) (α : Below height) :
    Restriction (graphOf b) α (sectionAt hl b α) := by
  intro p
  change _ ∈ ZFSet.pairSep _ _ _ ↔ _
  rw [ZFSet.mem_pairSep]
  constructor
  · rintro ⟨x,hx,y,_,pair, u,rfl,rfl⟩
    exact ⟨u,b u,ZFSet.mem_vonNeumann.mp hx,rfl,pair⟩
  · rintro ⟨x,y,hx,hy,pair⟩
    change b x = y at hy
    subst y
    exact ⟨x.val,ZFSet.mem_vonNeumann.mpr hx,(b x).val,
      ZFSet.mem_vonNeumann.mpr ((map_rank_cut hl b x α).mpr hx),pair,x,rfl,rfl⟩

theorem Restriction.edge {B : Graph height} {α : Below height} {s : Rank height}
    (hs : Restriction B α s) (x y : Rank height) :
    ZFSet.pair x.val y.val ∈ s.val ↔ x.val.rank < α.val ∧ B x y := by
  rw [hs]
  constructor
  · rintro ⟨v,w,hv,hB,hp⟩
    obtain ⟨hx,hy⟩ := ZFSet.pair_inj.mp hp
    obtain rfl : x = v := Subtype.ext hx
    obtain rfl : y = w := Subtype.ext hy
    exact ⟨hv,hB⟩
  · rintro ⟨hx,hy⟩
    exact ⟨x,y,hx,hy,rfl⟩

theorem Restriction.subset_of_le {B : Graph height} {α β : Below height} {s t : Rank height}
    (hs : Restriction B α s) (ht : Restriction B β t) (h : α ≤ β) : s.val ⊆ t.val := by
  intro p hp
  obtain ⟨x,y,hx,rel,eqv⟩ := (hs p).mp hp
  exact (ht p).mpr ⟨x,y,hx.trans_le h,rel,eqv⟩

theorem map_subset (a : Emb height) {s t : Rank height} (h : s.val ⊆ t.val) :
    (a s).val ⊆ (a t).val :=
  ((RankDef.subsetD (0 : Fin 2) 1).transfer a ![s,t]).mpr h

theorem map_edge (hl : Order.IsSuccLimit height) (a : Emb height) (x y s : Rank height) :
    ZFSet.pair (a x).val (a y).val ∈ (a s).val ↔ ZFSet.pair x.val y.val ∈ s.val :=
  (RankDef.edgeD hl (0 : Fin 3) 1 2).transfer a ![x,y,s]

private def IsFunctional (s : Rank height) : Prop :=
  ∀ x y z : Rank height, ZFSet.pair x.val y.val ∈ s.val →
    ZFSet.pair x.val z.val ∈ s.val → y = z

private theorem functionalD (hl : Order.IsSuccLimit height) :
    RankDef (fun v : Unit → Rank height => IsFunctional (v ())) := by
  unfold IsFunctional
  apply RankDef.all1
  apply RankDef.all1
  apply RankDef.all1
  let s : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl (Sum.inl ()))
  let x : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl (Sum.inr ()))
  let y : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let z : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inr ()
  exact (RankDef.edgeD hl x y s).impD ((RankDef.edgeD hl x z s).impD (RankDef.eqV y z))

private theorem image_functional (hl : Order.IsSuccLimit height) (a b : Emb height)
    {s : Rank height} {α : Below height} (hs : Restriction (graphOf b) α s) : IsFunctional (a s) := by
  apply ((functionalD hl).transfer a (fun _ => s)).mpr
  intro x y z e f
  exact ((hs.edge x y).mp e).2.symm.trans ((hs.edge x z).mp f).2

theorem application_unique (hl : Order.IsSuccLimit height) (a b : Emb height) {x y z : Rank height}
    (h : application (graphOf a) (graphOf b) x y) (k : application (graphOf a) (graphOf b) x z) :
    y = z := by
  obtain ⟨α,s,_,hs,rfl,ey⟩ := h
  obtain ⟨β,t,_,ht,rfl,ez⟩ := k
  rcases le_total α β with hab|hba
  · exact image_functional hl a b ht x y z ((map_subset a (hs.subset_of_le ht hab)) ey) ez
  · exact image_functional hl a b hs x y z ey ((map_subset a (ht.subset_of_le hs hba)) ez)

private theorem graph_domainD (hl : Order.IsSuccLimit height) :
    RankDef (fun v : Fin 2 → Rank height => ∀ x : Rank height, x.val ∈ (v 0).val →
      ∃ y : Rank height, ZFSet.pair x.val y.val ∈ (v 1).val) := by
  apply RankDef.all1
  apply (RankDef.memV (Sum.inr ()) (Sum.inl 0)).impD
  apply RankDef.ex1
  exact RankDef.edgeD hl (Sum.inl (Sum.inr ())) (Sum.inr ()) (Sum.inl (Sum.inl 1))

theorem image_section_total (hl : Order.IsSuccLimit height) (a b : Emb height) (α : Below height)
    (x : Rank height) (hx : x.val.rank < (ordinalImage a α).val) :
    ∃ y : Rank height, ZFSet.pair x.val y.val ∈ (a (sectionAt hl b α)).val := by
  let s := sectionAt hl b α
  have source : ∀ x : Rank height, x.val ∈ (stage α).val →
      ∃ y : Rank height, ZFSet.pair x.val y.val ∈ s.val :=
    fun x h => ⟨b x, ((sectionAt_spec hl b α).edge _ _).mpr ⟨ZFSet.mem_vonNeumann.mp h,rfl⟩⟩
  have domain := ((graph_domainD hl).transfer a ![stage α,s]).mpr source
  have hmem : x.val ∈ (a (stage α)).val := by rw [map_stage hl]; exact ZFSet.mem_vonNeumann.mpr hx
  exact domain x hmem

theorem application_total (hl : Order.IsSuccLimit height) (a b : Emb height) (x : Rank height) :
    ∃ y, application (graphOf a) (graphOf b) x y := by
  let α : Below height := ⟨Order.succ x.val.rank,hl.succ_lt x.property⟩
  have up : α ≤ ordinalImage a α := (ordinalImage_strictMono a).le_apply
  obtain ⟨y,hy⟩ := image_section_total hl a b α x ((Order.lt_succ _).trans_le up)
  exact ⟨y,α,sectionAt hl b α,a (sectionAt hl b α),sectionAt_spec hl b α,rfl,hy⟩

private theorem image_section_agrees (hl : Order.IsSuccLimit height) (a b : Emb height) (α : Below height)
    (x y : Rank height) (hx : x.val.rank < (ordinalImage a α).val)
    (rel : application (graphOf a) (graphOf b) x y) :
    ZFSet.pair x.val y.val ∈ (a (sectionAt hl b α)).val := by
  obtain ⟨z,hz⟩ := image_section_total hl a b α x hx
  have eqv := application_unique hl a b rel
    ⟨α,sectionAt hl b α,a (sectionAt hl b α),sectionAt_spec hl b α,rfl,hz⟩
  exact eqv ▸ hz

private theorem formulaOn {n : Nat} {ι : Type} (φ : membershipLanguage.Formula (Fin n)) (f : Fin n → ι) :
    RankDef (fun v : ι → Rank height => φ.Realize (v ∘ f)) :=
  ⟨φ.relabel f, fun _ => Formula.realize_relabel⟩

private def PreservesOn {n : Nat} (φ : membershipLanguage.Formula (Fin n)) (s : Rank height) : Prop :=
  ∀ v w : Fin n → Rank height, (∀ i, ZFSet.pair (v i).val (w i).val ∈ s.val) →
    (φ.Realize w ↔ φ.Realize v)

private theorem preservesD (hl : Order.IsSuccLimit height) {n : Nat}
    (φ : membershipLanguage.Formula (Fin n)) :
    RankDef (fun v : Unit → Rank height => PreservesOn φ (v ())) := by
  classical
  unfold PreservesOn
  apply RankDef.allD
  apply RankDef.allD
  let s : (Unit ⊕ Fin n) ⊕ Fin n := Sum.inl (Sum.inl ())
  let x (i : Fin n) : (Unit ⊕ Fin n) ⊕ Fin n := Sum.inl (Sum.inr i)
  let y (i : Fin n) : (Unit ⊕ Fin n) ⊕ Fin n := Sum.inr i
  have guards := RankDef.finiteAnd (height := height) (R := fun i v =>
    ZFSet.pair (v (x i)).val (v (y i)).val ∈ (v s).val) Finset.univ
    (fun i _ => RankDef.edgeD hl (x i) (y i) s)
  exact (guards.congr (fun _ => by simp [s,x,y])).impD ((formulaOn φ y).iffD (formulaOn φ x))

private theorem bounds_for_tuple (hl : Order.IsSuccLimit height) {n : Nat} (x : Fin n → Rank height) :
    ∃ α : Below height, ∀ i, (x i).val.rank < α.val := by
  classical
  let m := Finset.univ.sup (fun i => (x i).val.rank)
  have bound : m < height := (Finset.sup_lt_iff hl.bot_lt).mpr (fun i _ => (x i).property)
  refine ⟨⟨Order.succ m,hl.succ_lt bound⟩,fun i => ?_⟩
  exact lt_of_le_of_lt (Finset.le_sup (f := fun i => (x i).val.rank) (Finset.mem_univ i)) (Order.lt_succ m)

theorem application_map_formula (hl : Order.IsSuccLimit height) (a b : Emb height) {n : Nat}
    (φ : membershipLanguage.Formula (Fin n)) (v w : Fin n → Rank height)
    (rel : ∀ i, application (graphOf a) (graphOf b) (v i) (w i)) :
    φ.Realize w ↔ φ.Realize v := by
  obtain ⟨α,bound⟩ := bounds_for_tuple hl v
  let s := sectionAt hl b α
  have old : PreservesOn φ s := by
    intro x y edges
    have eqv : b ∘ x = y := funext fun i => (((sectionAt_spec hl b α).edge _ _).mp (edges i)).2
    exact eqv ▸ b.map_formula φ x
  have transported := ((preservesD hl φ).transfer a (fun _ => s)).mpr old
  exact transported v w fun i => image_section_agrees hl a b α (v i) (w i)
    ((bound i).trans_le (show α ≤ ordinalImage a α from (ordinalImage_strictMono a).le_apply)) (rel i)

noncomputable def applyEmb (hl : Order.IsSuccLimit height) (a b : Emb height) : Emb height where
  toFun x := Classical.choose (application_total hl a b x)
  map_formula' {_} φ x := application_map_formula hl a b φ x _ fun i =>
    Classical.choose_spec (application_total hl a b (x i))

theorem application_eq (hl : Order.IsSuccLimit height) (a b : Emb height) :
    application (graphOf a) (graphOf b) = graphOf (applyEmb hl a b) := by
  funext x y
  apply propext
  have h : application (graphOf a) (graphOf b) x (applyEmb hl a b x) :=
    Classical.choose_spec (application_total hl a b x)
  exact ⟨fun rel => application_unique hl a b h rel, fun eqv => eqv ▸ h⟩

theorem applyEmb_commutes (hl : Order.IsSuccLimit height) (a b : Emb height) (x : Rank height) :
    applyEmb hl a b (a x) = a (b x) := by
  change graphOf (applyEmb hl a b) _ _
  rw [← application_eq]
  let α : Below height := ⟨Order.succ x.val.rank,hl.succ_lt x.property⟩
  refine ⟨α,sectionAt hl b α,a (sectionAt hl b α),sectionAt_spec hl b α,rfl,?_⟩
  exact (map_edge hl a _ _ _).mpr (((sectionAt_spec hl b α).edge _ _).mpr ⟨Order.lt_succ _,rfl⟩)

/-- If b first moves α, a(b) first moves a(α). The fixed initial segment is
    transferred with a universal quantifier, so it includes ordinals that
    need not be pointwise images of elements of α. -/
theorem applyEmb_critical (hl : Order.IsSuccLimit height) (a b : Emb height) {α : Below height}
    (h : IsCritical (graphOf b) α) : IsCritical (graphOf (applyEmb hl a b)) (ordinalImage a α) := by
  let cut : Below height := ⟨Order.succ α.val,hl.succ_lt α.property⟩
  let s := sectionAt hl b cut
  have D : RankDef (fun v : Fin 2 → Rank height => ∀ x : Rank height,
      x.val ∈ (v 0).val → ZFSet.pair x.val x.val ∈ (v 1).val) := by
    apply RankDef.all1
    exact (RankDef.memV (Sum.inr ()) (Sum.inl 0)).impD
      (RankDef.edgeD hl (Sum.inr ()) (Sum.inr ()) (Sum.inl 1))
  have old : ∀ x : Rank height, x.val ∈ (point α).val → ZFSet.pair x.val x.val ∈ s.val := by
    intro x hx
    obtain ⟨δ,hδ,eqv⟩ := Ordinal.mem_toZFSet_iff.mp hx
    let t : Below height := ⟨δ,hδ.trans α.property⟩
    have ep : point t = x := Subtype.ext eqv
    rw [← ep]
    apply ((sectionAt_spec hl b cut).edge _ _).mpr
    exact ⟨by change δ.toZFSet.rank < Order.succ α.val; rw [Ordinal.rank_toZFSet]
              exact hδ.trans (Order.lt_succ _),h.1 t hδ⟩
  have moved := (D.transfer a ![point α,s]).mpr old
  constructor
  · intro δ hδ
    rw [← application_eq]
    refine ⟨cut,s,a s,sectionAt_spec hl b cut,rfl,moved (point δ) ?_⟩
    change (point δ).val ∈ (a (point α)).val
    rw [ordinalImage_spec]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hδ
  · obtain ⟨δ,hδ,e⟩ := h.2
    refine ⟨ordinalImage a δ,ordinalImage_strictMono a hδ,?_⟩
    change applyEmb hl a b (point (ordinalImage a α)) = point (ordinalImage a δ)
    rw [← ordinalImage_spec a α, ← ordinalImage_spec a δ, applyEmb_commutes, show b (point α) = point δ from e]

#print axioms application_eq
#print axioms applyEmb_commutes
#print axioms applyEmb_critical
end Gamma11.RankI3
