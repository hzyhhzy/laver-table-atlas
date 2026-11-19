import RankTransport

/-! The supremum of the images of the ordinals below a point. Its
definition by the least upper bound is valid in any ambient rank; the
bounded graph of a restriction lets elementarity carry the supremum to
all arguments below the new domain. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
variable {height : Ordinal.{u}}

def ExactImageSup (b : Emb height) (α σ : Below height) : Prop :=
  ∀ θ : Below height, θ<σ ↔ ∃ β : Below height, β<α ∧ θ<ordinalImage b β

private theorem exists_imageSup (b : Emb height) (α : Below height) : ∃ σ, ExactImageSup b α σ := by
  let S : Set (Below height) := {z | ∀ β : Below height, β<α → ordinalImage b β ≤ z}
  have member : ordinalImage b α ∈ S := fun _ h => ((ordinalImage_strictMono b) h).le
  obtain ⟨σ,ub,least⟩ := wellFounded_lt.has_min S ⟨_,member⟩
  refine ⟨σ,fun θ => ⟨?_,?_⟩⟩
  · intro lower
    by_contra! no
    exact least θ (show θ∈S from no) lower
  · rintro ⟨β,small,hit⟩
    exact hit.trans_le (ub β small)

noncomputable def imageSup (b : Emb height) (α : Below height) : Below height :=
  Classical.choose (exists_imageSup b α)

theorem imageSup_spec (b : Emb height) (α : Below height) : ExactImageSup b α (imageSup b α) :=
  Classical.choose_spec (exists_imageSup b α)

private theorem imageSup_eq {b : Emb height} {α σ : Below height} (h : ExactImageSup b α σ) :
    σ = imageSup b α := by
  have read (θ : Below height) := (h θ).trans (imageSup_spec b α θ).symm
  rcases lt_trichotomy σ (imageSup b α) with lo|eqv|hi
  · exact False.elim ((lt_irrefl σ) ((read σ).mpr lo))
  · exact eqv
  · exact False.elim ((lt_irrefl _) ((read _).mp hi))

theorem imageSup_le (b : Emb height) (α : Below height) : imageSup b α ≤ ordinalImage b α := by
  apply le_of_not_gt
  intro high
  obtain ⟨β,lt,above⟩ := (imageSup_spec b α _).mp high
  exact above.not_ge ((ordinalImage_strictMono b) lt).le

theorem lt_imageSup (b : Emb height) {α β : Below height} (limit : Order.IsSuccPrelimit α.val) (lt : β<α) :
    ordinalImage b β < imageSup b α := by
  have after := limit.succ_lt lt
  let β' : Below height := ⟨Order.succ β.val,after.trans α.property⟩
  exact (imageSup_spec b α _).mpr ⟨β',after,(ordinalImage_strictMono b) (Order.lt_succ β.val)⟩

private def SupGraph (D s U : Rank height) : Prop := ∀ y : Rank height, y.val∈U.val ↔
  ∃ x z : Rank height, x.val∈D.val ∧ ZFSet.pair x.val z.val∈s.val ∧ y.val∈z.val

private theorem supGraphD (hl : Order.IsSuccLimit height) :
    RankDef (fun v : Fin 3 → Rank height => SupGraph (v 0) (v 1) (v 2)) := by
  unfold SupGraph
  apply RankDef.all1
  apply (RankDef.memV (Sum.inr ()) (Sum.inl 2)).iffD
  apply RankDef.ex1
  apply RankDef.ex1
  let src (i : Fin 3) : ((Fin 3 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl (Sum.inl i))
  let y : ((Fin 3 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inl (Sum.inr ()))
  let x : ((Fin 3 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let z : ((Fin 3 ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.inr ()
  exact (RankDef.memV x (src 0)).andD ((RankDef.edgeD hl x z (src 1)).andD (RankDef.memV y z))

private theorem ordinal_member {x : Rank height} {α : Below height} (hx : x.val ∈ (point α).val) :
    ∃ β : Below height, β<α ∧ x=point β := by
  obtain ⟨o,lo,h⟩ := Ordinal.mem_toZFSet_iff.mp hx
  exact ⟨⟨o,lo.trans α.property⟩,lo,Subtype.ext h.symm⟩

private theorem supGraph_iff (hl : Order.IsSuccLimit height) (b : Emb height) (α σ : Below height) :
    SupGraph (point α) (sectionAt hl b α) (point σ) ↔ ExactImageSup b α σ := by
  have witness (β θ : Below height) (small : β<α) (hit : θ<ordinalImage b β) :
      ∃ x z : Rank height, x.val∈(point α).val ∧ ZFSet.pair x.val z.val∈(sectionAt hl b α).val ∧
        (point θ).val∈z.val := by
    have rank : (point β).val.rank < α.val := by change β.val.toZFSet.rank<α.val; rwa [Ordinal.rank_toZFSet]
    exact ⟨point β,point (ordinalImage b β),Ordinal.toZFSet_mem_toZFSet_iff.mpr small,
      ((sectionAt_spec hl b α).edge _ _).mpr ⟨rank,ordinalImage_spec _ _⟩,Ordinal.toZFSet_mem_toZFSet_iff.mpr hit⟩
  have decode {y x z : Rank height} (dom : x.val∈(point α).val)
      (edge : ZFSet.pair x.val z.val∈(sectionAt hl b α).val) (mem : y.val∈z.val) :
      ∃ θ β : Below height, y=point θ ∧ β<α ∧ θ<ordinalImage b β := by
    obtain ⟨β,small,rfl⟩ := ordinal_member dom
    have e : b (point β) = z := (((sectionAt_spec hl b α).edge _ _).mp edge).2
    rw [← e,ordinalImage_spec] at mem
    obtain ⟨θ,hit,eqv⟩ := ordinal_member mem
    exact ⟨θ,β,eqv,small,hit⟩
  constructor
  · intro h θ
    constructor
    · intro below
      obtain ⟨x,z,dom,edge,mem⟩ := (h (point θ)).mp (Ordinal.toZFSet_mem_toZFSet_iff.mpr below)
      obtain ⟨θ',β,eqv,small,hit⟩ := decode dom edge mem
      exact ⟨β,small,point_injective eqv ▸ hit⟩
    · rintro ⟨β,small,hit⟩
      exact Ordinal.toZFSet_mem_toZFSet_iff.mp ((h (point θ)).mpr (witness β θ small hit))
  · intro h y
    constructor
    · intro mem
      obtain ⟨θ,lo,rfl⟩ := ordinal_member mem
      obtain ⟨β,small,hit⟩ := (h θ).mp lo
      exact witness β θ small hit
    · rintro ⟨x,z,dom,edge,mem⟩
      obtain ⟨θ,β,rfl,small,hit⟩ := decode dom edge mem
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr ((h θ).mpr ⟨β,small,hit⟩)

theorem imageSup_natural (hl : Order.IsSuccLimit height) (a b : Emb height) (α : Below height) :
    ordinalImage a (imageSup b α) = imageSup (applyEmb hl a b) (ordinalImage a α) := by
  have source := (supGraph_iff hl b α _).mpr (imageSup_spec b α)
  have result := ((supGraphD hl).transfer a ![point α,sectionAt hl b α,point (imageSup b α)]).mpr source
  change SupGraph (a (point α)) (a (sectionAt hl b α)) (a (point (imageSup b α))) at result
  rw [ordinalImage_spec,ordinalImage_spec,section_natural] at result
  exact imageSup_eq ((supGraph_iff hl _ _ _).mp result)

/-- A shorter strictly increasing image cannot be cofinal in a critical
ordinal. This local regularity statement suffices for σ1 and σ2. -/
theorem imageSup_lt_critical (hl : Order.IsSuccLimit height) (a b : Emb height) {κ α : Below height}
    (crit : IsCritical (graphOf a) κ) (small : α<κ) (bounded : ordinalImage b α ≤ κ) :
    imageSup b α < κ := by
  have fixed {β : Below height} (h : β<κ) : ordinalImage a β = β :=
    point_injective ((ordinalImage_spec a β).symm.trans (crit.1 β h))
  apply lt_of_le_of_ne ((imageSup_le _ _).trans bounded)
  intro eqv
  have lifts := imageSup_natural hl a b α
  rw [eqv,fixed small] at lifts
  have above := (critical_moves _ crit).trans_eq lifts
  obtain ⟨β,lo,hit⟩ := (imageSup_spec (applyEmb hl a b) α κ).mp above
  have before := ((ordinalImage_strictMono b) lo).trans_le bounded
  have comm := ordinalImage_commutes hl a b β
  rw [fixed (lo.trans small),fixed before] at comm
  exact hit.not_ge (comm.trans_lt before).le

/-- The ordinary restriction is an element of the bounding critical rank.
The supremum of the smaller images gives a uniform range bound. -/
theorem section_below_critical (hl : Order.IsSuccLimit height) (a b : Emb height) {κ α : Below height}
    (crit : IsCritical (graphOf a) κ) (lim : Order.IsSuccPrelimit α.val)
    (small : α<κ) (bounded : ordinalImage b α ≤ κ) : (sectionAt hl b α).val.rank < κ.val := by
  let σ := imageSup b α
  have smallσ : σ<κ := imageSup_lt_critical hl a b crit small bounded
  have subset : (sectionAt hl b α).val ⊆ ZFSet.powerset (ZFSet.powerset ((stage α).val ∪ (stage σ).val)) := by
    intro p hp
    obtain ⟨x,y,hx,hy,rfl⟩ := (sectionAt_spec hl b α p).mp hp
    change b x=y at hy
    subst y
    have below : (b x).val.rank < σ.val := (map_set_rank hl b x).trans_lt
      (lt_imageSup b lim (show (⟨x.val.rank,x.property⟩ : Below height) < α from hx))
    have member := (relationSet_edge hl (stage α) (stage σ) (fun _ _ => True) x.val (b x).val).mpr
      ⟨ZFSet.mem_vonNeumann.mpr hx,ZFSet.mem_vonNeumann.mpr below,trivial⟩
    simp only [relationSet,ZFSet.pairSep,ZFSet.mem_sep] at member
    exact member.1
  apply (ZFSet.rank_mono subset).trans_lt
  rw [ZFSet.rank_powerset,ZFSet.rank_powerset,ZFSet.rank_union]
  change Order.succ (Order.succ (max (ZFSet.vonNeumann α.val).rank (ZFSet.vonNeumann σ.val).rank)) < κ.val
  rw [ZFSet.rank_vonNeumann,ZFSet.rank_vonNeumann]
  have pre := critical_prelimit hl a crit
  exact pre.succ_lt (pre.succ_lt (max_lt small smallσ))

#print axioms imageSup_natural
#print axioms imageSup_lt_critical
#print axioms section_below_critical
end Gamma11.RankI3
