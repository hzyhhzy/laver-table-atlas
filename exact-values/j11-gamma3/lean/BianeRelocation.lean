import EndpointMidpoint

/-! The forward-table version of Biane, "Laver tables and combinatorics",
Proposition 5.1. All products are the ordinary finite products, also when
the new degree is much larger than the old one. -/

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

theorem last_block_value (F : BinaryFamily) {s m a : Nat} (hs : s ≤ m)
    (hl : 2 ^ m - 2 ^ s ≤ a) (ha : a < 2 ^ m) (y : Nat) :
    (F m).mul a y = if (F s).mul a y = 0 then 0 else 2 ^ m - 2 ^ s + (F s).mul a y := by
  have hle : 2 ^ s ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) hs
  have hd := Nat.pow_dvd_pow 2 hs
  have offset := Nat.dvd_sub hd (Nat.dvd_refl (2 ^ s))
  by_cases hz : (F s).mul a y = 0
  · rw [if_pos hz]; exact (last_block_zero F hs hl ha y).mpr hz
  · rw [if_neg hz]
    have hne : (F m).mul a y ≠ 0 := fun h => hz ((last_block_zero F hs hl ha y).mp h)
    have hg := ((F m).row_grows a y ha).resolve_left hne
    have hb := (F m).mul_lt a y
    let z := (F m).mul a y - (2 ^ m - 2 ^ s)
    have he : (F m).mul a y = (2 ^ m - 2 ^ s) + z := by dsimp [z]; omega
    have hsmall : z < 2 ^ s := by dsimp [z]; omega
    have proj := (F m).projection (F s) hd a y
    rw [he, Nat.add_mod, Nat.mod_eq_zero_of_dvd offset, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hsmall] at proj
    exact he.trans (congrArg _ proj)

/-- Stretch the distance between the two copies of the nonzero residues.
    The separating element b itself is sent to h, and zero stays zero. -/
def relocate (b h x : Nat) : Nat :=
  if x = 0 then 0 else if x ≤ b then h - b + x else 2 * (h - b) + x

private theorem relocate_zero_iff (b h x : Nat) : relocate b h x = 0 ↔ x = 0 := by
  unfold relocate
  split <;> rename_i h0
  · simp [h0]
  · split <;> omega

private theorem halfway {n : Nat} (A : FiniteTable (n * 2)) (B : FiniteTable n) (y : Nat) :
    A.mul n y = if y % n = 0 then 0 else n + y % n := by
  have he := upper_copy A B (x := 0) B.positive y
  simpa only [Nat.add_zero, B.zero_mul] using he

private theorem upper_relocated (F : BinaryFamily) {t v x a : Nat}
    (htv : t ≤ v) (hlo : 2 ^ t < x) (hhi : x < 2 ^ t * 2) :
    (F (v + 1)).mul (2 * (2 ^ v - 2 ^ t) + x) (2 ^ v - 2 ^ t + a) =
      relocate (2 ^ t) (2 ^ v) ((F (t + 1)).mul x a) := by
  let b := 2 ^ t
  let h := 2 ^ v
  have ble : b ≤ h := Nat.pow_le_pow_right (by decide : 0 < 2) htv
  have hoff : b ∣ h - b := Nat.dvd_sub (Nat.pow_dvd_pow 2 htv) (Nat.dvd_refl b)
  have htw : b ∣ 2 * (h - b) := Nat.dvd_mul_left_of_dvd hoff 2
  have sh : 2 ^ (v + 1) = h * 2 := Nat.pow_succ ..
  have sb : 2 ^ (t + 1) = b * 2 := Nat.pow_succ ..
  change b < x at hlo
  change x < b * 2 at hhi
  have hred (d z : Nat) (hd : b ∣ d) : (d + z) % b = z % b := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.zero_add, Nat.mod_mod]
  have hbase : (F t).mul (2 * (h - b) + x) (h - b + a) = (F t).mul x a := by
    rw [← (F t).mul_mod_left (2 * (h - b) + x), hred _ _ htw, (F t).mul_mod_left,
      ← (F t).mul_mod_right x (h - b + a), hred _ _ hoff, (F t).mul_mod_right]
  change (F (v + 1)).mul (2 * (h - b) + x) (h - b + a) = relocate b h ((F (t + 1)).mul x a)
  rw [last_block_value F (s := t) (m := v + 1) (a := 2 * (h - b) + x)
    (by omega) (by change 2 ^ (v + 1) - b ≤ _; omega) (by omega), hbase,
    last_block_value F (s := t) (m := t + 1) (a := x) (Nat.le_succ _)
    (by change 2 ^ (t + 1) - b ≤ _; omega) (by omega)]
  by_cases hz : (F t).mul x a = 0
  · simp [hz, relocate]
  · simp only [if_neg hz]
    change 2 ^ (v + 1) - b + (F t).mul x a = relocate b h (2 ^ (t + 1) - b + (F t).mul x a)
    have hab : b < 2 ^ (t + 1) - b + (F t).mul x a := by omega
    rw [relocate, if_neg (by omega), if_neg (by omega)]
    omega

/-- Moving the highest backward bit changes only its position in the output.
    The strict bounds on a are essential for the lower-copy row. -/
theorem biane_relocate (F : BinaryFamily) {t v : Nat} (htv : t ≤ v) (a y : Nat)
    (ha : 0 < a) (hab : a < 2 ^ t) :
    (F (v + 1)).mul (2 ^ v - 2 ^ t + a) y =
      relocate (2 ^ t) (2 ^ v) ((F (t + 1)).mul a y) := by
  let b := 2 ^ t
  let h := 2 ^ v
  have bpos : 0 < b := Nat.two_pow_pos _
  have ble : b ≤ h := Nat.pow_le_pow_right (by decide : 0 < 2) htv
  have hoff : b ∣ h - b := Nat.dvd_sub (Nat.pow_dvd_pow 2 htv) (Nat.dvd_refl b)
  have sh : 2 ^ (v + 1) = h * 2 := Nat.pow_succ ..
  have sb : 2 ^ (t + 1) = b * 2 := Nat.pow_succ ..
  suffices H : ∀ k a, b - a = k → 0 < a → a < b → ∀ y,
      (F (v + 1)).mul (h - b + a) y = relocate b h ((F (t + 1)).mul a y) by
    exact H _ a rfl ha hab y
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a hk ha hab y
    induction y with
    | zero => simp [FiniteTable.mul_zero, relocate]
    | succ y prev =>
      let A := F (t + 1)
      let B := F (v + 1)
      let x := A.mul a y
      have hx : x < b * 2 := A.mul_lt a y
      have grow : x = 0 ∨ a < x := A.row_grows a y (by omega)
      rw [B.row_recurrence _ y, prev, A.row_recurrence a y]
      change B.mul (relocate b h x) (h - b + a + 1) = relocate b h (A.mul x (a + 1))
      rcases grow with hx0 | hg
      · rw [hx0, show relocate b h 0 = 0 by rfl, B.zero_mul, A.zero_mul,
          Nat.mod_eq_of_lt (by change _ < 2 ^ (v + 1); omega),
          Nat.mod_eq_of_lt (by change _ < 2 ^ (t + 1); omega),
          relocate, if_neg (by omega), if_pos (by omega)]
        omega
      · by_cases small : x < b
        · rw [show relocate b h x = h - b + x by
            simp only [relocate, if_neg (by omega : x ≠ 0), if_pos (Nat.le_of_lt small)]]
          have hn : A.mul x b = 0 := positive_half_zero F t x (by omega) hx
          have align : A.mul x (h - b + a + 1) = A.mul x (a + 1) := by
            obtain ⟨q, hd⟩ := hoff
            rw [Nat.add_assoc, hd, A.periodic_multiple hn q]
          rw [ih (b - x) (by omega) x rfl (by omega) small, align]
        · by_cases eqb : x = b
          · rw [eqb, relocate, if_neg (by omega), if_pos (Nat.le_refl _),
              Nat.sub_add_cancel ble]
            have mid_t (z : Nat) : A.mul b z = if z % b = 0 then 0 else b + z % b := by
              exact halfway (n := b) A (F t) z
            have mid_v (z : Nat) : B.mul h z = if z % h = 0 then 0 else h + z % h := by
              exact halfway (n := h) B (F v) z
            rw [mid_t, mid_v]
            by_cases atEnd : a + 1 = b
            · have hv : h - b + a + 1 = h := by omega
              simp [hv, atEnd, relocate]
            · rw [Nat.mod_eq_of_lt (by omega : a + 1 < b),
                Nat.mod_eq_of_lt (by omega : h - b + a + 1 < h),
                if_neg (by omega), if_neg (by omega), relocate, if_neg (by omega), if_neg (by omega)]
              omega
          · rw [show relocate b h x = 2 * (h - b) + x by
              simp only [relocate, if_neg (by omega : x ≠ 0), if_neg (by omega : ¬ x ≤ b)],
              Nat.add_assoc (h - b) a 1]
            exact upper_relocated F htv (by omega : b < x) hx

theorem biane_zero_iff (F : BinaryFamily) {t v : Nat} (htv : t ≤ v)
    {a : Nat} (ha : 0 < a) (hab : a < 2 ^ t) (y : Nat) :
    (F (v + 1)).mul (2 ^ v - 2 ^ t + a) y = 0 ↔ (F (t + 1)).mul a y = 0 := by
  rw [biane_relocate F htv a y ha hab, relocate_zero_iff]

end Gamma11
