import EndpointReduction

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

/-- In the last block of length 2^s, projection reflects zero: a nonzero
    multiple of 2^s cannot lie strictly between 2^m-2^s and 2^m. -/
theorem last_block_zero (F : BinaryFamily) {s m a : Nat} (hs : s ≤ m)
    (hlo : 2 ^ m - 2 ^ s ≤ a) (ha : a < 2 ^ m) (b : Nat) :
    (F m).mul a b = 0 ↔ (F s).mul a b = 0 := by
  have proj := (F m).projection (F s) (Nat.pow_dvd_pow 2 hs) a b
  constructor
  · intro hz
    simpa [hz] using proj.symm
  · intro hz
    rw [hz] at proj
    rcases (F m).row_grows a b ha with h | h
    · exact h
    · have hlt := (F m).mul_lt a b
      have hd := Nat.dvd_sub (Nat.pow_dvd_pow 2 hs) (Nat.dvd_of_mod_eq_zero proj)
      have := Nat.le_of_dvd (by omega : 0 < 2 ^ m - (F m).mul a b) hd
      omega

private theorem before_zero_lower {n a p : Nat} (A : FiniteTable n) (ha : a < n)
    (hp : A.FirstZero a p) (b : Nat) (hb : 0 < b) (hlt : b < p) :
    a + b ≤ A.mul a b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb0 : b = 0
    · subst b
      exact (A.row_grows a 1 ha).resolve_left (hp.2.2 1 (by decide) hlt)
    · have h := ih (by omega) (by omega)
      exact Nat.le_trans (Nat.succ_le_succ h)
        (A.firstZero_strict hp (by omega : 0 < b) (Nat.lt_succ_self b) hlt)

/-- Any nonzero row modulo 2^(s+1) returns to zero by column 2^s. -/
theorem positive_half_zero (F : BinaryFamily) (s a : Nat) (ha : 0 < a)
    (hlt : a < 2 ^ (s + 1)) : (F (s + 1)).mul a (2 ^ s) = 0 := by
  obtain ⟨p, hp⟩ := (F (s + 1)).exists_firstZero a
  obtain ⟨k, hk, rfl⟩ := period_is_power_two F (s + 1) a p hp
  apply ((F (s + 1)).firstZero_iff_mod hp _).mpr
  apply (pow_mod_zero_iff _ _).mpr
  apply Classical.byContradiction
  intro h
  have hks : k = s + 1 := by omega
  subst k
  have hsize : 1 < 2 ^ (s + 1) := Nat.one_lt_two_pow (by omega)
  have h := before_zero_lower _ hlt hp (2 ^ (s + 1) - 1) (by omega) (by omega)
  have := (F (s + 1)).mul_lt a (2 ^ (s + 1) - 1)
  omega

theorem double_zero (F : BinaryFamily) (m a b : Nat) (hz : (F m).mul a b = 0) :
    (F (m + 1)).mul a (2 * b) = 0 := by
  obtain ⟨p, hp⟩ := (F m).exists_firstZero a
  obtain ⟨q, hq⟩ := (F (m + 1)).exists_firstZero a
  have hd := Nat.dvd_of_mod_eq_zero (((F m).firstZero_iff_mod hp b).mp hz)
  apply ((F (m + 1)).firstZero_iff_mod hq _).mpr
  apply Nat.mod_eq_zero_of_dvd
  rcases period_stays_or_doubles (F (m + 1)) (F m) hq hp with h | h
  · rw [h]; exact Nat.dvd_trans hd (Nat.dvd_mul_left _ _)
  · rw [h]; exact Nat.mul_dvd_mul_left 2 hd

private theorem gap_dvd (s m : Nat) (hs : s ≤ m) : 2 ^ s ∣ 2 ^ m - 2 ^ s :=
  Nat.dvd_sub (Nat.pow_dvd_pow 2 hs) (Nat.dvd_refl _)

/-- At the first missing high bit, the row 2^m-2^s in degree m+1 has
    the literal additive prefix of length 2^s, including its endpoint. -/
theorem gap_prefix (F : BinaryFamily) {s m : Nat} (hsm : s < m)
    (b : Nat) (hb : 0 < b) (hb' : b ≤ 2 ^ s) :
    (F (m + 1)).mul (2 ^ m - 2 ^ s) b = 2 ^ m - 2 ^ s + b := by
  let a := 2 ^ m - 2 ^ s
  have hp := Nat.two_pow_pos s
  have hsize := Nat.two_pow_pos m
  have hp_le : 2 ^ s ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have hdiv : 2 ^ s ∣ a := gap_dvd s m (by omega)
  change (F (m + 1)).mul a b = a + b
  have hab : a + 2 ^ s = 2 ^ m := Nat.sub_add_cancel hp_le
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb0 : b = 0
    · subst b
      rw [(F (m + 1)).mul_one, Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega)]
    · have hbpos : 0 < b := by omega
      have hblt : b < 2 ^ s := by omega
      have prev := ih hbpos (by omega)
      have hz : (F (m + 1)).mul (a + b) (2 ^ s) = 0 := by
        cases s with
        | zero => simp at hblt; omega
        | succ r =>
          have hh : (F (r + 1)).mul (a + b) (2 ^ r) = 0 := by
            rw [← (F (r + 1)).mul_mod_left (a + b), Nat.add_mod,
              Nat.mod_eq_zero_of_dvd hdiv, Nat.zero_add,
              Nat.mod_mod, Nat.mod_eq_of_lt hblt]
            exact positive_half_zero F r b hbpos hblt
          have old := (last_block_zero F (s := r + 1) (m := m) (a := a + b)
            (by omega) (by dsimp [a]; omega) (by omega) (2 ^ r)).mpr hh
          simpa only [Nat.pow_succ, Nat.mul_comm] using double_zero F m (a + b) (2 ^ r) old
      obtain ⟨q, hq⟩ := hdiv
      have align : (F (m + 1)).mul (a + b) (a + 1) = (F (m + 1)).mul (a + b) 1 := by
        simpa only [hq] using (F (m + 1)).periodic_multiple hz q 1
      rw [(F (m + 1)).row_recurrence a b, prev, align, (F (m + 1)).mul_one,
        Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega)]
      omega

private theorem low_gap_not_square_zero (F : BinaryFamily) {s m : Nat} (hs : s < m) :
    (F (m + 1)).mul (2 ^ m - 2 ^ s) (2 ^ m - 2 ^ s) ≠ 0 := by
  let a := 2 ^ m - 2 ^ s
  let h := 2 ^ s
  have hn : 0 < h := Nat.two_pow_pos _
  have hle : h ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have hab : a + h = 2 ^ m := Nat.sub_add_cancel hle
  have mid : (F (m + 1)).mul a h = 2 ^ m :=
    (gap_prefix F hs h hn (Nat.le_refl _)).trans hab
  have half : 2 * h ∣ 2 ^ m := by
    have := Nat.pow_dvd_pow 2 (show s + 1 ≤ m by omega)
    simpa only [Nat.pow_succ, Nat.mul_comm] using this
  change (F (m + 1)).mul a a ≠ 0
  intro hz
  obtain ⟨p, hp⟩ := (F (m + 1)).exists_firstZero a
  obtain ⟨k, _, rfl⟩ := period_is_power_two F (m + 1) a p hp
  have hks : ¬ k ≤ s := by
    intro h
    have h0 := ((F (m + 1)).firstZero_iff_mod hp (2 ^ s)).mpr ((pow_mod_zero_iff _ _).mpr h)
    exact (Nat.ne_of_gt (Nat.two_pow_pos m)) (mid.symm.trans h0)
  have hd1 := Nat.pow_dvd_pow 2 (show s + 1 ≤ k by omega)
  have hd2 := Nat.dvd_of_mod_eq_zero (((F (m + 1)).firstZero_iff_mod hp a).mp hz)
  have ha : 2 * h ∣ a := by
    simpa only [h, Nat.pow_succ, Nat.mul_comm] using Nat.dvd_trans hd1 hd2
  have hdif := Nat.dvd_sub half ha
  rw [show 2 ^ m - a = h by omega] at hdif
  have := Nat.le_of_dvd hn hdif
  omega

/-- The nonzero square-zero elements are precisely the terminal dyadic
    intervals. This is the forward-table version of Biane's Proposition 5.5. -/
theorem square_zero_iff (F : BinaryFamily) (m a : Nat) (ha : a < 2 ^ m) :
    (F m).mul a a = 0 ↔ a = 0 ∨ ∃ s, s < m ∧ a = 2 ^ m - 2 ^ s := by
  constructor
  · induction m generalizing a with
    | zero =>
      intro _
      simp at ha
      exact Or.inl (by omega)
    | succ m ih =>
      intro hz
      let n := 2 ^ m
      have hn : 0 < n := Nat.two_pow_pos m
      have h2n : 2 ^ (m + 1) = n * 2 := Nat.pow_succ ..
      have hlo : (F m).mul (a % n) (a % n) = 0 := by
        rw [(F m).mul_mod_left, (F m).mul_mod_right,
          ← (F (m + 1)).projection (F m) (Nat.pow_dvd_pow 2 (Nat.le_succ m)), hz,
          Nat.zero_mod]
      rcases ih _ (Nat.mod_lt a hn) hlo with hzero | ⟨s, hs, hv⟩
      · rcases multiple_below_twice (show a < n * 2 by omega) hzero with h | h
        · exact Or.inl h
        · exact Or.inr ⟨m, by omega, by omega⟩
      · have hlt : 2 ^ s ≤ n := Nat.pow_le_pow_right (by decide) (by omega)
        change a % n = n - 2 ^ s at hv
        by_cases hal : a < n
        · rw [Nat.mod_eq_of_lt hal] at hv
          rw [hv] at hz
          exact False.elim (low_gap_not_square_zero F hs hz)
        · rw [Nat.mod_eq_sub_mod (by omega : n ≤ a), Nat.mod_eq_of_lt (by omega)] at hv
          exact Or.inr ⟨s, by omega, by omega⟩
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact (F m).mul_zero 0
    · apply (last_block_zero F (Nat.le_of_lt hs) (Nat.le_refl _) ha _).mpr
      rw [← (F s).mul_mod_left, Nat.mod_eq_zero_of_dvd (gap_dvd s m (by omega)),
        (F s).zero_mul, Nat.mod_eq_zero_of_dvd (gap_dvd s m (by omega))]

private theorem negative_half_mod {n h : Nat} (hn : 0 < n) (hh : 0 < h)
    (hd : 2 * h ∣ n) : (n - h) % (2 * h) = h := by
  obtain ⟨q, rfl⟩ := hd
  cases q with
  | zero => simp at hn
  | succ q =>
    rw [Nat.mul_succ, show 2 * h * q + 2 * h - h = 2 * h * q + h by omega,
      Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _), Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

theorem dyadic_tail_signature (Fcap m s : Nat) (hs : s < m) (hm : m ≤ Fcap) :
    signature Fcap (2 ^ m - 2 ^ s) = s := by
  have hlow := (le_signature Fcap (2 ^ m - 2 ^ s) s (by omega)).mpr
    (Nat.mod_eq_zero_of_dvd (gap_dvd s m (by omega)))
  have hmod : (2 ^ m - 2 ^ s) % (2 ^ (s + 1)) = 2 ^ s := by
    have hd := Nat.pow_dvd_pow 2 (show s + 1 ≤ m by omega)
    simpa only [Nat.pow_succ 2 s, Nat.mul_comm] using
      negative_half_mod (Nat.two_pow_pos m) (Nat.two_pow_pos s)
        (show 2 * 2 ^ s ∣ 2 ^ m by simpa only [Nat.pow_succ 2 s, Nat.mul_comm] using hd)
  have hhi : ¬ s + 1 ≤ signature Fcap (2 ^ m - 2 ^ s) := by
    intro h
    have hz := (le_signature Fcap _ (s + 1) (by omega)).mp h
    exact Nat.ne_of_gt (Nat.two_pow_pos s) (hmod.symm.trans hz)
  omega

/-- When the row returns at column 2^(r+1), the preceding dyadic midpoint
    squares to zero. This holds even when the period divides 2^r. -/
theorem midpoint_square_zero (F : BinaryFamily) {m a r : Nat} (hr : r < m)
    (hz : (F m).mul a (2 ^ (r + 1)) = 0) :
    (F m).mul ((F m).mul a (2 ^ r)) ((F m).mul a (2 ^ r)) = 0 := by
  let b := 2 ^ m - 2 ^ r
  have hb : b < 2 ^ m := by dsimp [b]; have := Nat.two_pow_pos m; have := Nat.two_pow_pos r; omega
  have hd := Nat.pow_dvd_pow 2 (show r + 1 ≤ m by omega)
  have hmod : b % (2 ^ (r + 1)) = 2 ^ r := by
    simpa only [b, Nat.pow_succ 2 r, Nat.mul_comm] using
      negative_half_mod (Nat.two_pow_pos m) (Nat.two_pow_pos r)
        (show 2 * 2 ^ r ∣ 2 ^ m by simpa only [Nat.pow_succ 2 r, Nat.mul_comm] using hd)
  have eqv : (F m).mul a b = (F m).mul a (2 ^ r) :=
    ((F m).reduce_period hz b).trans (congrArg _ hmod)
  have sqb : (F m).mul b b = 0 := (square_zero_iff F _ _ hb).mpr (Or.inr ⟨r, hr, rfl⟩)
  rw [← eqv, ← (F m).mul_distrib, sqb, (F m).mul_zero]

/-- Given a zero in the old degree, its new lift is read from the preceding
    dyadic midpoint. The lower-half test works in every degree. -/
theorem lift_iff_lower_midpoint (F : BinaryFamily) (m a r : Nat) (hr : r ≤ m)
    (old : (F m).mul a (2 ^ (r + 1)) = 0) :
    (F (m + 1)).mul a (2 ^ (r + 1)) = 2 ^ m ↔
    0 < (F (m + 1)).mul a (2 ^ r) ∧ (F (m + 1)).mul a (2 ^ r) < 2 ^ m := by
  let A := F (m + 1)
  have hsize := Nat.two_pow_pos m
  have hpow := Nat.two_pow_pos r
  have hstep : 2 ^ r < 2 ^ (r + 1) := by rw [Nat.pow_succ]; omega
  constructor
  · intro he
    obtain ⟨p, hp⟩ := A.exists_firstZero a
    obtain ⟨k, _, rfl⟩ := period_is_power_two F (m + 1) a p hp
    have hk : r + 1 < k := by
      apply Nat.lt_of_not_ge
      intro h
      have hz := (A.firstZero_iff_mod hp (2 ^ (r + 1))).mpr ((pow_mod_zero_iff _ _).mpr h)
      exact (Nat.ne_of_gt hsize) (he.symm.trans hz)
    have hend := Nat.pow_lt_pow_right (by decide : 1 < 2) hk
    exact ⟨Nat.pos_of_ne_zero (hp.2.2 _ hpow (Nat.lt_trans hstep hend)),
      Nat.lt_of_lt_of_le (A.firstZero_strict hp hpow hstep hend) (Nat.le_of_eq he)⟩
  · rintro ⟨hpos, hlt⟩
    have nonzero : A.mul a (2 ^ (r + 1)) ≠ 0 := by
      intro hz
      have sq := midpoint_square_zero F (m := m + 1) (a := a) (r := r) (by omega) hz
      rcases (square_zero_iff F _ _ (A.mul_lt _ _)).mp sq with h | ⟨s, hs, he⟩
      · exact Nat.ne_of_gt hpos h
      · have hpowle : 2 ^ s ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
        change (F (m + 1)).mul a (2 ^ r) = _ at he
        have hsize' : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ ..
        omega
    have hproj := A.projection (F m) (Nat.pow_dvd_pow 2 (Nat.le_succ m)) a (2 ^ (r + 1))
    rw [old] at hproj
    exact (multiple_below_twice (A.mul_lt _ _) hproj).resolve_left nonzero

end Gamma11
