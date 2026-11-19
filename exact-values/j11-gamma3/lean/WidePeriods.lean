import WideCrossing
import FourthJump

/-! The weak period estimate at T and the strictly stronger estimate
for a nonzero high background at T+1 (Appendix E). -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem thirteen_data {m a : Nat} (room : 272≤m) (one : act tables m a 1=1)
    (source : act tables m 13 4≤256) :
    let f := act tables m a
    let p := (tables m).mul a 13
    act tables m p 0=1 ∧ act tables m p 1=f 4 ∧ act tables m p (f 4)≤f 256 := by
  have zero : act tables m a 0=0 := by
    have h := act_strict_below_cap tables m a 0 1 (by decide) (show act tables m a 1<m by omega)
    omega
  have c0 := act_from_low tables m 13 0 _ 1 (by omega) (LowProducts.v13_1 _) (by decide) (by decide)
  have c1 := act_from_low tables m 13 1 _ 4 (by omega) (LowProducts.v13_2 _) (by decide) (by decide)
  have p0 := act_application tables m a 13 0
  have p1 := act_application tables m a 13 1
  have p4 := act_application tables m a 13 4
  rw [zero,c0,one] at p0
  rw [one,c1] at p1
  exact ⟨p0,p1,Nat.le_trans (Nat.le_of_eq p4) (act_mono tables m a source)⟩

private theorem visible_with_large_fourth {t a : Nat} (scale : t=256^256) (one : act tables (t+1) a 1=1)
    (source : act tables (t+1) 13 4≤256) (large : 256≤act tables (t+1) a 4)
    (visible : act tables (t+1) a 256<t+1) :
    act tables (t+1) a 4=256 ∧ act tables (t+1) a 256=t ∧ a%2^(t+1)<2^256 := by
  let d := t+1
  let p := (tables d).mul a 13
  have room : 272≤d := by dsimp [d]; rw [scale]; decide
  obtain ⟨p0,p1,p4⟩ := thirteen_data (a:=a) room one source
  have below := Nat.le_trans (act_mono tables d p large) p4
  obtain ⟨bits,old⟩ := exponential_at_threshold tables scale (by decide : 0<256) p0 (p1.symm ▸ large)
    (Nat.lt_of_le_of_lt below visible)
  have base := old 1 (by decide)
  rw [p1,Nat.pow_one] at base
  have endv := old 256 (Nat.le_refl _)
  rw [← scale] at endv
  have exactEnd : act tables d a 256=t := Nat.le_antisymm (Nat.le_of_lt_succ visible) (endv ▸ below)
  have nz : (tables d).mul a 13 % 2^d≠0 := bits ▸ (by decide : 2^256-3≠0)
  have lt := left_residue_lt tables (Nat.le_refl d) nz
  rw [bits] at lt
  exact ⟨base,exactEnd,Nat.lt_trans lt (by decide)⟩

/-- At a visible wide image the equality case forces the high part of
the acting row to vanish. This gives both period guards by projection. -/
theorem visible_wide {t a : Nat} (scale : t=256^256) (hom : SixteenRowData)
    (four : act tables (t+1) 14 4=16) (two : act tables (t+1) 13 2=16)
    (source : act tables (t+1) 13 4≤256)
    (guard : ∀ r row, 4≤r → r<256 → signature (t+1) row=r → 256≤act tables (t+1) row r →
      act tables (t+1) row 256=t+1)
    (low : 0<a%2^256) (inside : a%2^256<2^256-2) (visible : act tables (t+1) a 256<t+1) :
    act tables (t+1) a 256=t ∧ a%2^(t+1)<2^256 := by
  let d := t+1
  let f := act tables d a
  have room : 272≤d := by dsimp [d]; rw [scale]; decide
  obtain ⟨α,β,z,zs,z1,z2,at0,at1,pos,sm,reach⟩ := cross_256 room hom four low inside
  let h := (tables d).mul a z
  have hs : signature d h=f α := (signature_mul tables d a z).trans (congrArg f zs)
  have h1 := act_application tables d a z α
  have h2 := act_application tables d a z β
  rw [z1] at h1
  rw [z2] at h2
  change act tables d h (f α)=f β at h1
  change act tables d h (f β)=f 256 at h2
  change 0<f α at pos
  change f α<256 at sm
  change 256≤f β at reach
  have hBound := Nat.le_trans (act_mono tables d h reach) (Nat.le_of_eq h2)
  have hvis : act tables d h 256<d := Nat.lt_of_le_of_lt hBound visible
  by_cases big : 4≤f α
  · have cap := guard (f α) h big sm hs (h1.symm ▸ reach)
    exact False.elim ((Nat.ne_of_lt hvis) cap)
  by_cases one : f α=1
  · have αlo : α≤1 := by
      by_cases lt : α≤d
      · exact one ▸ le_act tables d a α lt
      · have far := Nat.le_trans (le_act tables d a d (Nat.le_refl _)) (act_mono tables d a (by omega : d≤α))
        change d≤f α at far; omega
    rcases (show α=0 ∨ α=1 by omega) with left|right
    · have br := at0 left
      rw [left] at one
      rw [br] at reach
      obtain ⟨bits,old⟩ := exponential_at_threshold tables scale (by decide : 0<256) one reach visible
      exact ⟨(old 256 (Nat.le_refl _)).trans scale.symm,Nat.lt_of_le_of_lt (Nat.le_of_eq bits) (by decide)⟩
    · have br := at1 right
      rw [right] at one
      rw [br] at reach
      by_cases large : 256≤f 4
      · exact (visible_with_large_fourth scale one source large visible).2
      have critical : 2≤signature d a := by
        apply Nat.le_of_not_gt
        intro l
        have move := act_gt_input tables d a 1 (by omega) (by omega)
        change 1<f 1 at move; omega
      have fix2 : f 2=2 := by
        apply fixes_below_signature
        by_cases h : signature d a=2
        · exact False.elim (large (unspecialized_fourth_image (by omega) (Or.inl h)))
        · omega
      let p := (tables d).mul a 13
      let h' := (tables d).mul p 2
      obtain ⟨_,p1,p4⟩ := thirteen_data room one source
      have p2 := act_application tables d a 13 2
      change act tables d p (f 2)=f (act tables d 13 2) at p2
      rw [fix2,two] at p2
      have js : signature d 2=1 := signature_pow d 1 (by omega)
      have j1 := act_from_low tables d 2 1 _ 2 (by omega) (LowProducts.v2_2 _) (by decide) (by decide)
      have j2 := act_from_low tables d 2 2 _ 4 (by omega) (LowProducts.v2_4 _) (by decide) (by decide)
      have hs' : signature d h'=f 4 := (signature_mul tables d p 2).trans (js ▸ p1)
      have a1 := act_application tables d p 2 1
      have a2 := act_application tables d p 2 2
      rw [p1,j1,p2] at a1
      rw [p2,j2] at a2
      have fourle : 4≤f 4 := le_act tables d a 4 (by omega)
      have kill := guard (f 4) h' fourle (Nat.lt_of_not_ge large) hs' (a1.symm ▸ reach)
      have step := act_mono tables d h' reach
      change act tables d h' (f 16)=act tables d p 4 at a2
      rw [kill,a2] at step
      have endv := Nat.le_trans step (Nat.le_trans (act_mono tables d p fourle) p4)
      exact False.elim ((Nat.not_le_of_gt visible) endv)
  · have minH : 2≤signature d h := by omega
    have fix1 := fixes_below_signature tables d h 1 (by omega)
    have positive : f α<4 := Nat.lt_of_not_ge big
    have vis4 := Nat.lt_of_le_of_lt (act_mono tables d h (show 4≤256 by decide)) hvis
    have gap := act_distance tables d h (Nat.le_of_lt positive) vis4
    rw [h1] at gap
    have hi4 : 256<act tables d h 4 := by omega
    obtain ⟨eqv,_,_⟩ := visible_with_large_fourth scale fix1 source (Nat.le_of_lt hi4) hvis
    exact False.elim ((Nat.ne_of_gt hi4) eqv)

#print axioms visible_wide

/-- Appendix E including backgrounds in the top half of the larger
table. All additions are ordinary natural additions because an aligned
background has room for an entire 256-bit block. -/
structure WidePeriodEstimates (t : Nat) : Prop where
  native : ∀ b, 1≤b → b<2^256-2 → entry t b (2^256)=0
  background : ∀ A, 0<A → A<2^(t+1) → 2^256 ∣ A → ∀ b, 1≤b → b<2^256-2 →
    entry (t+1) (A+b) (2^256)=0
  addition : ∀ A, 0<A → A<2^(t+1) → 2^256 ∣ A → ∀ b, 1≤b → b≤2^256-2 →
    (tables (t+1)).mul A b=A+b

theorem periods_from_equality_case {t : Nat} (room : 256≤t)
    (equalityCase : ∀ a, 0<a%2^256 → a%2^256<2^256-2 → act tables (t+1) a 256<t+1 →
      act tables (t+1) a 256=t ∧ a%2^(t+1)<2^256) : WidePeriodEstimates t := by
  let d := t+1
  have native (b : Nat) (pos : 1≤b) (stop : b<2^256-2) : entry t b (2^256)=0 := by
    rw [← canonical_mul]
    apply (le_act_iff tables (t+1) b 256 t (Nat.le_succ _)).mp
    by_cases visible : act tables d b 256<d
    · have lo : b%2^256=b := Nat.mod_eq_of_lt (by omega)
      exact Nat.le_of_eq (equalityCase b (by rw [lo]; exact pos) (by rw [lo]; exact stop) visible).1.symm
    · exact Nat.le_trans (Nat.le_succ t) (Nat.le_of_not_gt visible)
  have roomD : 256≤d := Nat.le_trans room (Nat.le_succ _)
  have fits {A b : Nat} (fit : A<2^d) (div : 2^256 ∣ A) (small : b<2^256) : A+b<2^d := by
    have gap := Nat.le_of_dvd (Nat.sub_pos_of_lt fit) (Nat.dvd_sub (Nat.pow_dvd_pow 2 roomD) div)
    omega
  have background (A : Nat) (posA : 0<A) (fit : A<2^d) (div : 2^256 ∣ A) (b : Nat)
      (pos : 1≤b) (stop : b<2^256-2) : (tables d).mul (A+b) (2^256)=0 := by
    apply (le_act_iff tables d _ 256 d (Nat.le_refl _)).mp
    apply Nat.le_of_not_gt
    intro visible
    have lo : (A+b)%2^256=b := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd div,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega : b<2^256)]
    have high := (equalityCase (A+b) (by rw [lo]; exact pos) (by rw [lo]; exact stop) visible).2
    rw [Nat.mod_eq_of_lt (fits fit div (by omega : b<2^256))] at high
    have lower := Nat.le_of_dvd posA div
    omega
  refine ⟨native,fun A pos fit div b lb ub => (canonical_mul d (A+b) (2^256)).symm.trans (background A pos fit div b lb ub),?_⟩
  intro A pos fit div b lo ub
  cases b with
  | zero => omega
  | succ i =>
    induction i with
    | zero => exact ((tables d).mul_one A).trans (Nat.mod_eq_of_lt (fits fit div (by decide : 1<2^256)))
    | succ i ih =>
      have per := background A pos fit div (i+1) (by omega) ub
      have modOne : (A+1)%2^256=1 := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd div,Nat.zero_add,Nat.mod_mod]
      rw [(tables d).row_recurrence A (i+1),ih (by omega) (by omega),(tables d).reduce_period per (A+1),
        modOne,(tables d).mul_one,Nat.add_assoc,Nat.mod_eq_of_lt (fits fit div (by omega : i+1+1<2^256))]

#print axioms periods_from_equality_case
end Gamma11
