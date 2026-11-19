import RankImageSup

/-! A common argument below delta_4 at which the second and third left
powers already cross the source of both of Dougherty's restriction identities.
All finite inputs to the argument are canonical A9 entries. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable
variable {height : Ordinal.{u}}

theorem read9 {j : Emb height} (hj : IsWitness j) {a x y v : Nat} (pos : 0<a)
    (raw : (tables 9).mul a (2^x) = v) (index : signature 9 v = y) (visible : y<9) :
    ordinalImage (powerEmb hj.1 j a) (dyadicPoint hj x) = dyadicPoint hj y :=
  native_read_act hj pos (show act tables 9 a x = y from (congrArg (signature 9) raw).trans index) visible

theorem bounded_generator_sections {j : Emb height} (hj : IsWitness j) :
    (sectionAt hj.1 j (dyadicPoint hj 1)).val.rank < (dyadicPoint hj 2).val ∧
    (sectionAt hj.1 j (dyadicPoint hj 2)).val.rank < (dyadicPoint hj 4).val := by
  have j1 : ordinalImage j (dyadicPoint hj 1)=dyadicPoint hj 2 :=
    read9 hj (a:=1) (by decide) (LowProducts.v1_2 _) (by decide) (by decide)
  have lim (i : Nat) := critical_prelimit hj.1 _ (dyadicPoint_critical hj i)
  exact ⟨section_below_critical hj.1 _ j (dyadicPoint_critical hj 2) (lim 1)
    ((dyadicPoint_strict hj) (by decide : 1<2)) j1.le,
    section_below_critical hj.1 _ j (dyadicPoint_critical hj 4) (lim 2)
    ((dyadicPoint_strict hj) (by decide : 2<4)) (generator_two hj).le⟩

theorem low_crossings {j : Emb height} (hj : IsWitness j) :
    ∃ β : Below height, β < dyadicPoint hj 4 ∧
      ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) < ordinalImage (powerEmb hj.1 j 2) β ∧
      ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4) < ordinalImage (powerEmb hj.1 j 3) β := by
  let e := powerEmb hj.1 j
  let f (i : Nat) := ordinalImage (e i)
  let δ := dyadicPoint hj
  have limit (i : Nat) := critical_prelimit hj.1 _ (dyadicPoint_critical hj i)
  have inc := dyadicPoint_strict hj
  have j1 : ordinalImage j (δ 1)=δ 2 := read9 hj (a:=1) (by decide) (LowProducts.v1_2 _) (by decide) (by decide)
  have j2 : ordinalImage j (δ 2)=δ 4 := generator_two hj
  have b2 : f 2 (δ 2)=δ 4 := read9 hj (by decide) (LowProducts.v2_4 _) (by decide) (by decide)
  have g2 : f 3 (δ 2)=δ 4 := read9 hj (by decide) (LowProducts.v3_4 _) (by decide) (by decide)
  have q2 : f 4 (δ 2)=δ 3 := dyadic_self_image hj 2
  have a5 : f 5 (δ 1)=δ 3 := read9 hj (by decide) (LowProducts.v5_2 _) (by decide) (by decide)
  have a6 : f 6 (δ 1)=δ 3 := read9 hj (by decide) (LowProducts.v6_2 _) (by decide) (by decide)
  have a7 : f 7 (δ 1)=δ 4 := read9 hj (by decide) (LowProducts.v7_2 _) (by decide) (by decide)
  have a8 : f 8 (δ 2)=δ 2 := read9 hj (by decide) (LowProducts.v8_4 _) (by decide) (by decide)
  have a9 : f 9 (δ 1)=δ 2 := read9 hj (by decide) (LowProducts.v9_2 _) (by decide) (by decide)
  have a10 : f 10 (δ 1)=δ 2 := read9 hj (by decide) (LowProducts.v10_2 _) (by decide) (by decide)
  have cov (i : Nat) (α : Below height) : f (i+1) (f i α) = f i (ordinalImage j α) := by
    have h := ordinalImage_commutes hj.1 (e i) j α
    rw [show applyEmb hj.1 (e i) j = e (i+1) from apply_generator hj.1 j i] at h
    exact h
  have sCov (i : Nat) (α : Below height) : f i (imageSup j α) = imageSup (e (i+1)) (f i α) := by
    have h := imageSup_natural hj.1 (e i) j α
    rw [show applyEmb hj.1 (e i) j = e (i+1) from apply_generator hj.1 j i] at h
    exact h
  have l7 := cov 7 (δ 1)
  have l8 := cov 8 (δ 2)
  have l9 := cov 9 (δ 1)
  have l10 := cov 10 (δ 1)
  rw [a7,j1] at l7
  rw [a8,j2] at l8
  rw [a9,j1] at l9
  rw [a10,j1] at l10
  have mu : f 11 (δ 2) = f 7 (δ 2) := l10.trans (l9.trans (l8.trans l7))
  let σ1 := imageSup j (δ 1)
  let σ2 := imageSup j (δ 2)
  have small1 : σ1 < δ 2 := imageSup_lt_critical hj.1 _ j (dyadicPoint_critical hj 2)
    (inc (by decide : 1<2)) j1.le
  have small2 : σ2 < δ 4 := imageSup_lt_critical hj.1 _ j (dyadicPoint_critical hj 4)
    (inc (by decide : 2<4)) j2.le
  have last := cov 6 (δ 1)
  rw [a6,j1] at last
  have lower : f 11 (δ 2) < f 6 (δ 2) := by
    rw [mu,← last]
    exact (ordinalImage_strictMono _) (inc (by decide : 2<3))
  have to5 := sCov 5 (δ 1)
  have to4 := sCov 4 (δ 2)
  have to3 := sCov 3 (δ 2)
  have to2 := sCov 2 (δ 2)
  rw [a5] at to5
  rw [q2] at to4
  rw [g2] at to3
  rw [b2] at to2
  have v5 : f 6 (δ 2) < f 5 σ1 := (lt_imageSup (e 6) (limit 3) (inc (by decide : 2<3))).trans_eq to5.symm
  have v4 : f 5 σ1 < f 4 σ2 :=
    (lt_imageSup (e 5) (limit 3) (small1.trans (inc (by decide : 2<3)))).trans_eq to4.symm
  have v3 : f 4 σ2 < f 3 σ2 := (lt_imageSup (e 4) (limit 4) small2).trans_eq to3.symm
  have v2 : f 3 σ2 < f 2 σ2 := (lt_imageSup (e 3) (limit 4) small2).trans_eq to2.symm
  have cross := lower.trans (v5.trans (v4.trans v3))
  rw [restriction_source hj]
  exact ⟨σ2,small2,cross.trans v2,cross⟩

private theorem read_both_restrictions {j : Emb height} (hj : IsWitness j) (d : Nat) (large : 16≤d)
    (reach : dyadicPoint hj d ≤ ordinalImage (powerEmb hj.1 j 13)
      (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)))
    (agree : ∀ (a k : Nat), (a=2 ∧ k=65520) ∨ (a=3 ∧ k=65534) →
      ∀ x : Rank height, x.val.rank < (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)).val →
      applyEmb hj.1 (powerEmb hj.1 j 13) (powerEmb hj.1 j a) x = powerEmb hj.1 j k x) :
    entry d 13 2 = 65520 ∧ entry d 13 3 = 65534 := by
  have size := Nat.pow_le_pow_right (by decide : 0<2) large
  obtain ⟨β,small,b,c⟩ := low_crossings hj
  exact ⟨thirteen_restriction_at_cut hj (by decide) (by decide)
    ((show 65520<2^16 by decide).trans_le size) reach (agree _ _ (Or.inl ⟨rfl,rfl⟩)) ⟨β,small,b.le⟩,
    thirteen_restriction_at_cut hj (by decide) (by decide)
    ((show 65534<2^16 by decide).trans_le size) reach (agree _ _ (Or.inr ⟨rfl,rfl⟩)) ⟨β,small,c.le⟩⟩

/-- For the two concrete constants in A.3, the sections in Dougherty II
§8 are now the only mathematical input. -/
theorem thirteen_two_and_three_of_restrictions {j : Emb height} (hj : IsWitness j)
    (agree : ∀ (a k : Nat), (a=2 ∧ k=65520) ∨ (a=3 ∧ k=65534) →
      ∀ x : Rank height, x.val.rank < (ordinalImage (powerEmb hj.1 j 13) (dyadicPoint hj 4)).val →
      applyEmb hj.1 (powerEmb hj.1 j 13) (powerEmb hj.1 j a) x = powerEmb hj.1 j k x) :
    entry (targetIndex+1) 13 2 = 65520 ∧ entry (targetIndex+1) 13 3 = 65534 := by
  have large : 16≤targetIndex+1 := by
    have p := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 4≤2048)
    change 2^4≤targetIndex at p; omega
  exact read_both_restrictions hj _ large (thirteen_above_target hj) agree

#print axioms low_crossings
#print axioms thirteen_two_and_three_of_restrictions
end Gamma11.RankI3
