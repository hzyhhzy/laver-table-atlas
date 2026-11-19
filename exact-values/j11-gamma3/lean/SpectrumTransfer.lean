import BianeRelocation
import CriticalSpectrum

/-! The two-composition transfer from §3 of the endpoint manuscript.
The first theorem uses finite witnesses at degree v. The uncapped version
obtains v from the image of the later composition in the critical spectrum. -/

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem two_lifts {a b z : Nat} (bound : a < b * 2) (res : a % b = z) :
    a = z ∨ a = b + z := by
  by_cases h : a < b
  · exact Or.inl ((Nat.mod_eq_of_lt h).symm.trans res)
  · rw [Nat.mod_eq_sub_mod (by omega : b ≤ a), Nat.mod_eq_of_lt (by omega)] at res
    exact Or.inr (by omega)

private theorem last_residue {v t x z : Nat} (h : t ≤ v)
    (low : 2 ^ v - 2 ^ t ≤ x) (high : x < 2 ^ v) (res : x % 2 ^ t = z) :
    x = 2 ^ v - 2 ^ t + z := by
  have hp : 2 ^ t ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2) h
  have hd := Nat.dvd_sub (Nat.pow_dvd_pow 2 h) (Nat.dvd_refl (2 ^ t))
  let k := x - (2 ^ v - 2 ^ t)
  have eqx : x = 2 ^ v - 2 ^ t + k := by dsimp [k]; omega
  have hk : k < 2 ^ t := by dsimp [k]; omega
  rw [eqx, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hk] at res
  exact eqx.trans (congrArg _ res)

theorem all_ones_before_hit (C : TableElement) {t v r : Nat} (htv : t ≤ v)
    (pos : 0 < C.rep t)
    (native : (tables (t + 1)).mul (C.rep t) (2 ^ r) ≠ 0)
    (stillZero : (tables v).mul (C.rep v) (2 ^ r) = 0) :
    C.rep v = 2 ^ v - 2 ^ t + C.rep t := by
  have below (k : Nat) (hk : k ≤ v) : (tables k).mul (C.rep k) (2 ^ r) = 0 := by
    have proj := (tables v).projection (tables k) (Nat.pow_dvd_pow 2 hk) (C.rep v) (2 ^ r)
    rw [stillZero, Nat.zero_mod, ← (tables k).mul_mod_left (C.rep v), C.project hk] at proj
    exact proj.symm
  suffices ∀ k, t ≤ k → k ≤ v → C.rep k = 2 ^ k - 2 ^ t + C.rep t from this v htv (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro h _
    have ht : t = 0 := by omega
    simp [ht]
  | succ k ih =>
    intro htk hkv
    by_cases eqv : t = k + 1
    · simp [eqv]
    · have htk' : t ≤ k := by omega
      have prev := ih htk' (by omega)
      have hb : C.rep (k + 1) < 2 ^ k * 2 := C.bound (k + 1)
      rcases two_lifts hb (C.project (Nat.le_succ k)) with lo | hi
      · have hz := below (k + 1) hkv
        rw [lo, prev] at hz
        exact False.elim (native ((biane_zero_iff tables htk' pos (C.bound t) _).mp hz))
      · have hp := Nat.pow_le_pow_right (n := 2) (by decide) htk'
        have hsize : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
        omega

theorem comp_output_succ (D : TableElement) (m i : Nat)
    (hpos : 0 < (tables m).mul (D.rep m) (i + 1)) :
    (D.comp (numeral i)).rep m + 1 = (tables m).mul (D.rep m) (i + 1) := by
  change (tables m).comp (D.rep m) (i % 2 ^ m) + 1 = _
  rw [(tables m).comp_mod_right, FiniteTable.comp]
  let y := (tables m).mul (D.rep m) (i + 1)
  have hy : y < 2 ^ m := (tables m).mul_lt _ _
  change (y + 2 ^ m - 1) % 2 ^ m + 1 = y
  change 0 < y at hpos
  rw [show y + 2 ^ m - 1 = y - 1 + 2 ^ m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem comp_transfer_finite (D : TableElement) {t v i j r s p : Nat}
    (htv : t ≤ v) (hij : i < j) (period : (tables t).FirstZero (D.rep t) p)
    (inside : j + 1 < p) (positive : 1 < (tables t).mul (D.rep t) (i + 1))
    (firstNative : (tables (t + 1)).mul ((D.comp (numeral i)).rep t) (2 ^ r) ≠ 0)
    (firstWaits : (tables v).mul ((D.comp (numeral i)).rep v) (2 ^ r) = 0)
    (lastZero : (tables v).mul ((D.comp (numeral j)).rep v) (2 ^ s) = 0)
    (lastHits : (tables (v + 1)).mul ((D.comp (numeral j)).rep (v + 1)) (2 ^ s) ≠ 0) :
    (tables (t + 1)).mul ((D.comp (numeral j)).rep t) (2 ^ s) ≠ 0 := by
  let X := D.comp (numeral i)
  let Y := D.comp (numeral j)
  have xi := comp_output_succ D t i (by omega)
  have xpos : 0 < X.rep t := by change _ < (D.comp (numeral i)).rep t; omega
  have filled := all_ones_before_hit X htv xpos firstNative firstWaits
  obtain ⟨p', hp'⟩ := (tables v).exists_firstZero (D.rep v)
  have proj (b : Nat) : (tables v).mul (D.rep v) b % 2 ^ t = (tables t).mul (D.rep t) b := by
    rw [(tables v).projection (tables t) (Nat.pow_dvd_pow 2 htv),
      ← (tables t).mul_mod_left (D.rep v), D.project htv]
  have hpz : (tables t).mul (D.rep t) p' = 0 := by rw [← proj, hp'.2.1, Nat.zero_mod]
  have hpp := (tables t).firstZero_le_of_zero period hp'.1 hpz
  have upOrd := (tables v).firstZero_strict hp' (Nat.zero_lt_succ i)
    (show i + 1 < j + 1 by omega) (show j + 1 < p' by omega)
  change (tables v).mul (D.rep v) (i + 1) < (tables v).mul (D.rep v) (j + 1) at upOrd
  have posi : 0 < (tables v).mul (D.rep v) (i + 1) :=
    Nat.pos_of_ne_zero (hp'.2.2 _ (Nat.zero_lt_succ _) (by omega))
  have posj : 0 < (tables v).mul (D.rep v) (j + 1) := Nat.lt_trans posi upOrd
  have xe : X.rep v + 1 = (tables v).mul (D.rep v) (i + 1) := comp_output_succ D v i posi
  have ye : Y.rep v + 1 = (tables v).mul (D.rep v) (j + 1) := comp_output_succ D v j posj
  have ylow : 2 ^ v - 2 ^ t ≤ Y.rep v := by omega
  have ylast := last_residue htv ylow (Y.bound v) (Y.project htv)
  have oldOrd := (tables t).firstZero_strict period (Nat.zero_lt_succ i)
    (show i + 1 < j + 1 by omega) inside
  change (tables t).mul (D.rep t) (i + 1) < (tables t).mul (D.rep t) (j + 1) at oldOrd
  have yr := comp_output_succ D t j (by omega)
  have ypos : 0 < Y.rep t := by change _ < (D.comp (numeral j)).rep t; omega
  have hbound : Y.rep (v + 1) < 2 ^ v * 2 := Y.bound (v + 1)
  rcases two_lifts hbound (Y.project (Nat.le_succ v)) with lo | hi
  · intro hz
    have h := (biane_zero_iff tables htv ypos (Y.bound t) (2 ^ s)).mpr hz
    change (tables (v + 1)).mul (Y.rep (v + 1)) (2 ^ s) ≠ 0 at lastHits
    rw [lo, ylast] at lastHits
    exact lastHits h
  · have up := upper_copy (tables (v + 1)) (tables v) (Y.bound v) (2 ^ s)
    rw [if_pos lastZero] at up
    change (tables (v + 1)).mul (Y.rep (v + 1)) (2 ^ s) ≠ 0 at lastHits
    exact False.elim (lastHits (hi ▸ up))

theorem native_zero_lifts (C : TableElement) {t x : Nat}
    (hz : (tables (t + 1)).mul (C.rep t) (2 ^ x) = 0) :
    (tables (t + 1)).mul (C.rep (t + 1)) (2 ^ x) = 0 := by
  rcases two_lifts (show C.rep (t + 1) < 2 ^ t * 2 from C.bound _)
      (C.project (Nat.le_succ t)) with lo | hi
  · rwa [lo]
  · have old := (tables (t + 1)).projection (tables t) (Nat.pow_dvd_pow 2 (Nat.le_succ t))
      (C.rep t) (2 ^ x)
    rw [hz, Nat.zero_mod] at old
    rw [hi]
    exact (upper_copy (n := 2 ^ t) (tables (t + 1)) (tables t) (C.bound t) (2 ^ x)).trans (if_pos old.symm)

theorem comp_transfer (H : FirstRowUnbounded) (D : TableElement) (hD : D.Total)
    {t i j r s p : Nat} (hij : i < j) (period : (tables t).FirstZero (D.rep t) p)
    (inside : j + 1 < p) (positive : 1 < (tables t).mul (D.rep t) (i + 1))
    (native : (numeral ((D.comp (numeral i)).rep t)).index (numeral_total H _) r = t)
    (later : t < D.index hD ((numeral j).index (numeral_total H j) s))
    (order : D.index hD ((numeral j).index (numeral_total H j) s) ≤
      D.index hD ((numeral i).index (numeral_total H i) r)) :
    (numeral ((D.comp (numeral j)).rep t)).index (numeral_total H _) s = t := by
  let X := D.comp (numeral i)
  let Y := D.comp (numeral j)
  have hX : X.Total := total_comp hD (numeral_total H i)
  have hY : Y.Total := total_comp hD (numeral_total H j)
  let v := Y.index hY s
  have hv : v = D.index hD ((numeral j).index (numeral_total H j) s) :=
    index_comp hD (numeral_total H j) s
  have hx := index_comp hD (numeral_total H i) r
  have hvx : v ≤ X.index hX r := hv ▸ (hx ▸ order)
  have vhigh : t < v := hv ▸ later
  have firstNative : (tables (t + 1)).mul (X.rep t) (2 ^ r) ≠ 0 := by
    intro hz
    have hh := (numeral_zero_iff H (X.rep t) (t + 1) r).mp ((canonical_mul _ _ _).symm.trans hz)
    change (numeral (X.rep t)).index (numeral_total H _) r = t at native
    omega
  have lastHits : (tables (v + 1)).mul (Y.rep (v + 1)) (2 ^ s) ≠ 0 := by
    intro hz
    have hh := (Y.zero_iff hY (v + 1) s).mp hz
    change v + 1 ≤ v at hh
    omega
  have hit := comp_transfer_finite D (Nat.le_of_lt vhigh) hij period inside positive firstNative
    ((X.zero_iff hX v r).mpr hvx) ((Y.zero_iff hY v s).mpr (Nat.le_refl _)) lastHits
  have low := (Y.zero_iff hY t s).mpr (Nat.le_of_lt vhigh)
  have floor := (numeral_zero_iff H (Y.rep t) t s).mp ((canonical_mul _ _ _).symm.trans low)
  have ceil : ¬ t + 1 ≤ (numeral (Y.rep t)).index (numeral_total H _) s := by
    intro high
    exact hit ((canonical_mul _ _ _).trans ((numeral_zero_iff H (Y.rep t) (t + 1) s).mpr high))
  change (numeral (Y.rep t)).index (numeral_total H _) s = t
  omega

end Gamma11
