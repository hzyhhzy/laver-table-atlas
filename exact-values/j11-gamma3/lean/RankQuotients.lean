import RankApplication

/-! From a quotient on words, which tests only the identity element, to
    the critical index of every image of every left power. No readout of
    a point image in terms of a finite-table multiplication is assumed. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable

inductive Word where
  | generator
  | app (left right : Word)

namespace Word

def realize {height : Ordinal.{u}} (j : Emb height) : Word → Graph height
  | .generator => graphOf j
  | .app s t => application (s.realize j) (t.realize j)

def residue (m : Nat) : Word → Nat
  | .generator => 1 % 2^m
  | .app s t => (tables m).mul (s.residue m) (t.residue m)

theorem generated {height : Ordinal.{u}} (j : Emb height) (w : Word) : Generated j (w.realize j) := by
  induction w with
  | generator => exact .generator
  | app s t hs ht => exact .app hs ht

/-- Argument n denotes the positive left power J_(n+1). -/
def power : Nat → Word
  | 0 => .generator
  | n+1 => .app (power n) .generator

theorem realize_power {height : Ordinal.{u}} (j : Emb height) (n : Nat) :
    (power n).realize j = leftPower j (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f => application f (graphOf j)) ih

theorem residue_power (m n : Nat) : (power n).residue m = (n+1) % 2^m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (tables m).mul ((power n).residue m) (1 % 2^m) = _
    rw [ih, (tables m).mul_mod_left, (tables m).mul_mod_right, (tables m).mul_one]

end Word

def FixesBefore {height : Ordinal.{u}} (A : Graph height) (δ : Below height) : Prop :=
  ∀ β : Below height, β < δ → A (point β) (point β)

def SingleValuedOnPoints {height : Ordinal.{u}} (A : Graph height) : Prop :=
  ∀ {α β δ : Below height}, A (point α) (point β) → A (point α) (point δ) → β = δ

theorem point_injective {height : Ordinal.{u}} : Function.Injective (@point height) := by
  intro α β h
  exact Subtype.ext (Ordinal.toZFSet_injective (congrArg Subtype.val h))

theorem graphOf_singleValued {height : Ordinal.{u}} (e : Emb height) :
    SingleValuedOnPoints (graphOf e) :=
  fun first second => point_injective (first.symm.trans second)

namespace Word
variable {height : Ordinal.{u}}

noncomputable def embedding (hl : Order.IsSuccLimit height) (j : Emb height) : Word → Emb height
  | .generator => j
  | .app s t => applyEmb hl (s.embedding hl j) (t.embedding hl j)

theorem realize_eq_graph (hl : Order.IsSuccLimit height) (j : Emb height) (w : Word) :
    w.realize j = graphOf (w.embedding hl j) := by
  induction w with
  | generator => rfl
  | app s t hs ht =>
    change application (s.realize j) (t.realize j) = graphOf (applyEmb hl _ _)
    rw [hs,ht,application_eq]

theorem singleValued (hl : Order.IsSuccLimit height) (j : Emb height) (w : Word) :
    SingleValuedOnPoints (w.realize j) := by
  rw [w.realize_eq_graph hl]
  exact graphOf_singleValued _

theorem carries (hl : Order.IsSuccLimit height) (j : Emb height) (s t : Word) {α : Below height}
    (ht : IsCritical (t.realize j) α) :
    ∃ β, (s.realize j) (point α) (point β) ∧ IsCritical ((s.app t).realize j) β := by
  rw [t.realize_eq_graph hl] at ht
  rw [s.realize_eq_graph hl, (s.app t).realize_eq_graph hl]
  exact ⟨_,ordinalImage_spec (s.embedding hl j) α,applyEmb_critical hl _ _ ht⟩

theorem critical_exists {j : Emb height} (hj : IsWitness j) (w : Word) :
    ∃ α, IsCritical (w.realize j) α := by
  induction w with
  | generator => exact generator_has_critical hj
  | app s t _ ht =>
    obtain ⟨α,hα⟩ := ht
    obtain ⟨β,_,hβ⟩ := s.carries hj.1 j t hα
    exact ⟨β,hβ⟩
end Word

theorem fixesBefore_iff {height : Ordinal.{u}} {A : Graph height} {α : Below height}
    (single : SingleValuedOnPoints A) (atCrit : IsCritical A α) (δ : Below height) :
    FixesBefore A δ ↔ δ ≤ α := by
  constructor
  · intro fixed
    apply le_of_not_gt
    intro earlier
    obtain ⟨β, moved, image⟩ := atCrit.2
    exact moved.ne (single (fixed α earlier) image)
  · intro within β before
    exact atCrit.1 β (lt_of_lt_of_le before within)

/-- Structural inputs for an actual rank embedding. The last line is
    only the zero class of the finite quotient. None of the inputs
    prescribes a numerical index for a point image. -/
structure QuotientLaws {height : Ordinal.{u}} (j : Emb height) (γ : Nat → Below height) : Prop where
  enumerates : Enumerates j γ
  zeroClass : ∀ (w : Word) m, w.residue m = 0 ↔ FixesBefore (w.realize j) (γ m)

namespace QuotientLaws
variable {height : Ordinal.{u}} {j : Emb height} {γ : Nat → Below height}

theorem detects (L : QuotientLaws j γ) (hl : Order.IsSuccLimit height) {w : Word} {y : Nat}
    (h : IsCritical (w.realize j) (γ y)) (m : Nat) : w.residue m = 0 ↔ m ≤ y :=
  (L.zeroClass w m).trans ((fixesBefore_iff (w.singleValued hl j) h (γ m)).trans L.enumerates.1.le_iff_le)

theorem critical_number (L : QuotientLaws j γ) {w : Word} {β : Below height}
    (h : IsCritical (w.realize j) β) : ∃ n, γ n = β :=
  (L.enumerates.2 β).mp ⟨w.realize j, w.generated j, h⟩

/-- J_(2^x) has exactly the x-th critical point. This comes from its
    dyadic residues and the identity cut, for every x at once. -/
theorem dyadic_critical (L : QuotientLaws j γ) (hj : IsWitness j) (x : Nat) :
    IsCritical ((Word.power (2^x-1)).realize j) (γ x) := by
  let w := Word.power (2^x-1)
  obtain ⟨β,hβ⟩ := w.critical_exists hj
  obtain ⟨y,rfl⟩ := L.critical_number hβ
  have pos := Nat.two_pow_pos x
  have both (m : Nat) : m ≤ x ↔ m ≤ y := by
    have test := L.detects hj.1 hβ m
    change (Word.power (2^x-1)).residue m = 0 ↔ m ≤ y at test
    rw [Word.residue_power, Nat.sub_add_cancel pos, pow_mod_zero_iff] at test
    exact test
  have eqv := Nat.le_antisymm ((both x).mp (Nat.le_refl x)) ((both y).mpr (Nat.le_refl y))
  exact (congrArg (fun z => IsCritical (w.realize j) (γ z)) eqv).mpr hβ

theorem correspondence (L : QuotientLaws j γ) (hj : IsWitness j) : FiniteCorrespondence j γ := by
  refine ⟨L.enumerates, ?_⟩
  intro a x
  cases a with
  | zero =>
    refine ⟨x, rfl, ?_⟩
    intro m
    rw [← canonical_mul, (tables m).zero_mul, pow_mod_zero_iff]
  | succ n =>
    let t := Word.power (2^x-1)
    let s := Word.power n
    obtain ⟨β,pointImage,crit⟩ := s.carries hj.1 j t (L.dyadic_critical hj x)
    obtain ⟨y,rfl⟩ := L.critical_number crit
    refine ⟨y, ?_, ?_⟩
    · rwa [← Word.realize_power]
    · intro m
      have test := L.detects hj.1 crit m
      change (tables m).mul ((Word.power n).residue m) ((Word.power (2^x-1)).residue m) = 0 ↔ m ≤ y at test
      rw [Word.residue_power, Word.residue_power, Nat.sub_add_cancel (Nat.two_pow_pos x),
        (tables m).mul_mod_left, (tables m).mul_mod_right, canonical_mul] at test
      exact test

end QuotientLaws
#print axioms QuotientLaws.correspondence
#print axioms Word.critical_exists
end Gamma11.RankI3
