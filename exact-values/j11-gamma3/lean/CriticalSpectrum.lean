import Gamma11Endpoint
import LaverLowerBounds.FiniteCongruence

/-! Compatible residues in the actual finite Laver tables. To obtain the
uncapped critical-index functions, the arithmetic hypothesis used here is
unboundedness of the first-row periods. Dougherty–Jech, §§4,7,8, identify
this hypothesis and these functions in an I3 realization. -/

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

@[ext] structure TableElement where
  rep : Nat → Nat
  bound : ∀ m, rep m < 2 ^ m
  project : ∀ {s m}, s ≤ m → rep m % 2 ^ s = rep s

namespace TableElement

def numeral (a : Nat) : TableElement where
  rep m := a % 2 ^ m
  bound _ := Nat.mod_lt _ (Nat.two_pow_pos _)
  project h := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

def app (A B : TableElement) : TableElement where
  rep m := (tables m).mul (A.rep m) (B.rep m)
  bound m := (tables m).mul_lt _ _
  project {s m} h := by
    rw [(tables m).projection (tables s) (Nat.pow_dvd_pow 2 h),
      ← (tables s).mul_mod_left (A.rep m), A.project h,
      ← (tables s).mul_mod_right (A.rep s), B.project h]

def comp (A B : TableElement) : TableElement where
  rep m := (tables m).comp (A.rep m) (B.rep m)
  bound _ := Nat.mod_lt _ (Nat.two_pow_pos _)
  project {s m} h := by
    rw [comp_projection (tables m) (tables s) (Nat.pow_dvd_pow 2 h),
      ← (tables s).comp_mod_left (A.rep m), A.project h,
      ← (tables s).comp_mod_right (A.rep s), B.project h]

theorem app_one (a : Nat) : (numeral a).app (numeral 1) = numeral (a + 1) := by
  apply TableElement.ext
  funext m
  change (tables m).mul (a % _) (1 % _) = _
  rw [(tables m).mul_mod_left, (tables m).mul_mod_right, (tables m).mul_one]
  rfl

def cap (A : TableElement) (m x : Nat) : Nat := act tables m (A.rep m) x

theorem le_cap_iff (A : TableElement) {k m : Nat} (hk : k ≤ m) (x : Nat) :
    k ≤ A.cap m x ↔ (tables k).mul (A.rep k) (2 ^ x) = 0 := by
  rw [cap, le_act_iff tables m _ x k hk, ← (tables k).mul_mod_left (A.rep m), A.project hk]

theorem cap_restrict (A : TableElement) {k m : Nat} (hk : k ≤ m) (x : Nat) :
    A.cap k x = min k (A.cap m x) := by
  have hb : A.cap k x ≤ k := act_le tables k _ _
  have test (r : Nat) (h : r ≤ k) : r ≤ A.cap k x ↔ r ≤ A.cap m x :=
    (A.le_cap_iff h x).trans (A.le_cap_iff (Nat.le_trans h hk) x).symm
  have h1 := (test (A.cap k x) hb).mp (Nat.le_refl _)
  have h2 := (test (min k (A.cap m x)) (Nat.min_le_left ..)).mpr (Nat.min_le_right ..)
  omega

def Total (A : TableElement) : Prop := ∀ x, ∃ m, A.cap m x < m

noncomputable def index (A : TableElement) (hA : A.Total) (x : Nat) : Nat :=
  A.cap (Classical.choose (hA x)) x

theorem cap_eq_min (A : TableElement) (hA : A.Total) (m x : Nat) :
    A.cap m x = min m (A.index hA x) := by
  let k := Classical.choose (hA x)
  have earlier : A.cap k x < k := Classical.choose_spec (hA x)
  have eq1 := A.cap_restrict (Nat.le_max_left k m) x
  have eq2 := A.cap_restrict (Nat.le_max_right k m) x
  change A.cap m x = min m (A.cap k x)
  omega

theorem zero_iff (A : TableElement) (hA : A.Total) (m x : Nat) :
    (tables m).mul (A.rep m) (2 ^ x) = 0 ↔ m ≤ A.index hA x := by
  rw [← A.le_cap_iff (Nat.le_refl m) x, A.cap_eq_min hA]
  omega

theorem index_strict (A : TableElement) (hA : A.Total) {x y : Nat} (hxy : x < y) :
    A.index hA x < A.index hA y := by
  let m := max (A.index hA x) (A.index hA y) + 1
  have hX : A.cap m x = A.index hA x := by rw [A.cap_eq_min hA, Nat.min_eq_right (by dsimp [m]; omega)]
  have hY : A.cap m y = A.index hA y := by rw [A.cap_eq_min hA, Nat.min_eq_right (by dsimp [m]; omega)]
  have hs := act_strict_below_cap tables m (A.rep m) x y hxy (show A.cap m y < m by rw [hY]; dsimp [m]; omega)
  change A.cap m x < A.cap m y at hs
  simpa only [hX, hY] using hs

theorem finite_read (A B : TableElement) (hA : A.Total) (hB : B.Total)
    (m x : Nat) (h : A.rep m = B.rep m) :
    min m (A.index hA x) = min m (B.index hB x) := by
  rw [← A.cap_eq_min hA, ← B.cap_eq_min hB, cap, cap, h]

def FirstRowUnbounded : Prop := ∀ x, ∃ m, entry m 1 (2 ^ x) ≠ 0

theorem generator_total (growth : FirstRowUnbounded) : (numeral 1).Total := by
  intro x
  obtain ⟨m, hm⟩ := growth x
  refine ⟨m, Nat.lt_of_not_ge (fun h => hm ?_)⟩
  have hz := ((numeral 1).le_cap_iff (Nat.le_refl m) x).mp h
  simpa only [numeral, FiniteTable.mul_mod_left, canonical_mul] using hz

theorem identity_total : (numeral 0).Total := by
  intro x
  refine ⟨x + 1, Nat.lt_of_not_ge (fun h => ?_)⟩
  have hz := ((numeral 0).le_cap_iff (Nat.le_refl (x + 1)) x).mp h
  change (tables (x + 1)).mul (0 % _) _ = 0 at hz
  rw [Nat.zero_mod, (tables _).zero_mul] at hz
  have := (pow_mod_zero_iff x (x + 1)).mp hz
  omega

theorem total_app {A B : TableElement} (hA : A.Total) (hB : B.Total) : (A.app B).Total := by
  intro x
  let u := B.index hB x
  let v := A.index hA u
  let m := max x (max u v) + 1
  have bx : B.cap m x = u := by rw [B.cap_eq_min hB]; exact Nat.min_eq_right (by dsimp [m,u,v]; omega)
  have au : A.cap m u = v := by rw [A.cap_eq_min hA]; exact Nat.min_eq_right (by dsimp [m,u,v]; omega)
  have cov := act_application tables m (A.rep m) (B.rep m) x
  change (A.app B).cap m (A.cap m x) = A.cap m (B.cap m x) at cov
  rw [bx, au] at cov
  have hle := le_act tables m (A.rep m) x (by dsimp [m]; omega)
  have hm : (A.app B).cap m x ≤ (A.app B).cap m (A.cap m x) := act_mono tables m _ hle
  refine ⟨m, ?_⟩
  rw [cov] at hm
  exact Nat.lt_of_le_of_lt hm (show v < m by dsimp [m]; omega)

theorem total_comp {A B : TableElement} (hA : A.Total) (hB : B.Total) : (A.comp B).Total := by
  intro x
  let u := B.index hB x
  let v := A.index hA u
  let m := max u v + 1
  have bx : B.cap m x = u := by rw [B.cap_eq_min hB]; exact Nat.min_eq_right (by dsimp [m,u,v]; omega)
  have au : A.cap m u = v := by rw [A.cap_eq_min hA]; exact Nat.min_eq_right (by dsimp [m,u,v]; omega)
  have cov := act_composition tables m (A.rep m) (B.rep m) x
  change (A.comp B).cap m x = A.cap m (B.cap m x) at cov
  rw [bx, au] at cov
  exact ⟨m, by rw [cov]; dsimp [m]; omega⟩

theorem numeral_total (growth : FirstRowUnbounded) (a : Nat) : (numeral a).Total := by
  induction a with
  | zero => exact identity_total
  | succ a ih => rw [← app_one]; exact total_app ih (generator_total growth)

theorem index_comp {A B : TableElement} (hA : A.Total) (hB : B.Total) (x : Nat) :
    (A.comp B).index (total_comp hA hB) x = A.index hA (B.index hB x) := by
  let u := B.index hB x
  let v := A.index hA u
  let w := (A.comp B).index (total_comp hA hB) x
  let m := max u (max v w)
  have he := act_composition tables m (A.rep m) (B.rep m) x
  change (A.comp B).cap m x = A.cap m (B.cap m x) at he
  rw [(A.comp B).cap_eq_min (total_comp hA hB), B.cap_eq_min hB,
    Nat.min_eq_right (show u ≤ m by dsimp [m]; omega), A.cap_eq_min hA] at he
  change min m w = min m v at he
  change w = v
  dsimp [m] at he
  omega

theorem index_app {A B : TableElement} (hA : A.Total) (hB : B.Total) (x : Nat) :
    (A.app B).index (total_app hA hB) (A.index hA x) = A.index hA (B.index hB x) := by
  let u := A.index hA x
  let v := B.index hB x
  let z := A.index hA v
  let w := (A.app B).index (total_app hA hB) u
  let m := max (max u v) (max z w)
  have he := act_application tables m (A.rep m) (B.rep m) x
  change (A.app B).cap m (A.cap m x) = A.cap m (B.cap m x) at he
  rw [A.cap_eq_min hA, B.cap_eq_min hB,
    Nat.min_eq_right (show u ≤ m by dsimp [m]; omega),
    Nat.min_eq_right (show v ≤ m by dsimp [m]; omega),
    (A.app B).cap_eq_min (total_app hA hB), A.cap_eq_min hA] at he
  change min m w = min m z at he
  change w = z
  dsimp [m] at he
  omega

theorem numeral_zero_iff (growth : FirstRowUnbounded) (a m x : Nat) :
    entry m a (2 ^ x) = 0 ↔ m ≤ (numeral a).index (numeral_total growth a) x := by
  have he := (numeral a).zero_iff (numeral_total growth a) m x
  simpa only [numeral, FiniteTable.mul_mod_left, canonical_mul] using he

theorem index_lower_bound (growth : FirstRowUnbounded) :
    targetIndex ≤ (numeral 11).index (numeral_total growth 11) 3 := by
  exact (numeral_zero_iff growth 11 targetIndex 3).mp
    (row11_zero_through_target targetIndex (Nat.le_refl _))

end TableElement
end Gamma11
