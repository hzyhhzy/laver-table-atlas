import EndpointArithmetic

/-! Construction of the ordinary tables by finite recursion. The successive
degrees supply the projection used to prove that the rows wrap correctly;
left distributivity is then a descending-row induction. Cf. Dougherty–Jech,
Finite left-distributive algebras and embedding algebras, §3. -/

set_option autoImplicit false

namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem aux_next (n fuel a b : Nat) (h : a ≠ 0) :
    rowAux n (fuel + 1) a (b + 1) =
      if rowAux n (fuel + 1) a b = 0 then (a + 1) % n
      else rowAux n fuel (rowAux n (fuel + 1) a b) (a + 1) := by
  simp only [rowAux, if_neg h]

private theorem aux_bounds (n fuel a b : Nat) (ha : a < n) :
    rowAux n fuel a b < n ∧ (rowAux n fuel a b = 0 ∨ a < rowAux n fuel a b) := by
  have hn : 0 < n := by omega
  induction fuel generalizing a b with
  | zero => exact ⟨hn, Or.inl rfl⟩
  | succ fuel ih =>
    by_cases h : a = 0
    · subst a
      simp only [rowAux, if_true]
      exact ⟨Nat.mod_lt _ hn, by omega⟩
    · induction b with
      | zero =>
        simp only [rowAux, if_neg h]
        exact ⟨hn, Or.inl rfl⟩
      | succ b hb =>
        rw [aux_next n fuel a b h]
        by_cases hv : rowAux n (fuel + 1) a b = 0
        · simp only [if_pos hv]
          refine ⟨Nat.mod_lt _ hn, ?_⟩
          by_cases he : a + 1 = n
          · simp [he]
          · rw [Nat.mod_eq_of_lt (by omega)]; omega
        · simp only [if_neg hv]
          have hval := ih _ (a + 1) hb.1
          exact ⟨hval.1, hval.2.imp_right (Nat.lt_trans (hb.2.resolve_left hv))⟩

private theorem aux_stable (n fuel more a b : Nat) (ha : a < n)
    (hf : n - a ≤ fuel) (hg : n - a ≤ more) :
    rowAux n fuel a b = rowAux n more a b := by
  induction fuel generalizing more a b with
  | zero => omega
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      by_cases h : a = 0
      · simp [rowAux, h]
      · induction b with
        | zero => simp only [rowAux, if_neg h]; rfl
        | succ b hb =>
          rw [aux_next n fuel a b h, aux_next n more a b h, ← hb]
          by_cases hv : rowAux n (fuel + 1) a b = 0
          · simp [hv]
          · simp only [if_neg hv]
            have hbnd := aux_bounds n (fuel + 1) a b ha
            have hs := hbnd.2.resolve_left hv
            exact ih more _ (a + 1) hbnd.1 (by omega) (by omega)

private def raw (n a b : Nat) := rowAux n (n - a) a b

private theorem raw_bounds {n a : Nat} (ha : a < n) (b : Nat) :
    raw n a b < n ∧ (raw n a b = 0 ∨ a < raw n a b) := aux_bounds _ _ _ _ ha

private theorem raw_zero (n : Nat) (hn : 0 < n) (b : Nat) : raw n 0 b = b % n := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem raw_at_zero {n a : Nat} (ha : a < n) : raw n a 0 = 0 := by
  unfold raw
  cases hf : n - a with
  | zero => omega
  | succ k => by_cases h : a = 0 <;> simp [rowAux, h] <;> rfl

private theorem raw_at_one {n a : Nat} (ha : a < n) : raw n a 1 = (a + 1) % n := by
  unfold raw
  cases hf : n - a with
  | zero => omega
  | succ k => by_cases h : a = 0 <;> simp [rowAux, h] <;> rfl

private theorem raw_succ {n a : Nat} (ha : a < n) (b : Nat) :
    raw n a (b + 1) = raw n (raw n a b) (a + 1) := by
  have hn : 0 < n := by omega
  by_cases ha0 : a = 0
  · subst a
    rw [raw_zero n hn, raw_zero n hn, raw_at_one (Nat.mod_lt _ hn), Nat.mod_add_mod]
  · obtain ⟨k, hk⟩ : ∃ k, n - a = k + 1 := ⟨n - a - 1, by omega⟩
    have init : raw n a (b + 1) =
        if raw n a b = 0 then (a + 1) % n else rowAux n k (raw n a b) (a + 1) := by
      unfold raw
      rw [hk]
      simp only [rowAux, if_neg ha0]
    rw [init]
    by_cases hv : raw n a b = 0
    · rw [if_pos hv, hv, raw_zero n hn]
    · rw [if_neg hv]
      have bounds := raw_bounds ha b
      have hl := bounds.2.resolve_left hv
      exact aux_stable n k _ _ _ bounds.1 (by omega) (Nat.le_refl _)

private theorem row_induction {n : Nat} (P : Nat → Prop) (z : P 0)
    (step : ∀ a, a < n → a ≠ 0 →
      (∀ v, v < n → (v = 0 ∨ a < v) → P v) → P a) (a : Nat) (ha : a < n) : P a := by
  suffices ∀ k a, n - a = k → a < n → P a from this _ a rfl ha
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro a hk ha
    by_cases h : a = 0
    · exact h ▸ z
    · apply step a ha h
      intro v hv hg
      rcases hg with rfl | hgt
      · exact z
      · exact ih (n - v) (by omega) v rfl hv

private theorem raw_periodic {n a p : Nat} (ha : a < n) (hz : raw n a p = 0) (b : Nat) :
    raw n a (p + b) = raw n a b := by
  induction b with
  | zero => simpa only [Nat.add_zero, raw_at_zero ha] using hz
  | succ b ih => rw [Nat.add_succ, raw_succ ha (p + b), raw_succ ha b, ih]

private theorem raw_reduce {n a p : Nat} (ha : a < n) (hz : raw n a p = 0) (b : Nat) :
    raw n a b = raw n a (b % p) := by
  have rep : ∀ k l, raw n a (p * k + l) = raw n a l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro l
      rw [Nat.mul_succ, show p * k + p + l = p + (p * k + l) by omega, raw_periodic ha hz, ih]
  have he := rep (b / p) (b % p)
  rwa [Nat.div_add_mod] at he

private theorem raw_projection {n : Nat} (B : FiniteTable n) {a : Nat} (ha : a < n * 2)
    (b : Nat) : raw (n * 2) a b % n = B.mul a b := by
  have hdiv : n ∣ n * 2 := ⟨2, rfl⟩
  have hn := B.positive
  apply row_induction (fun a => ∀ b, raw (n * 2) a b % n = B.mul a b) (a := a) (ha := ha) _ _ b
  · intro b
    rw [raw_zero _ (by omega), B.zero_mul, Nat.mod_mod_of_dvd _ hdiv]
  · intro a ha _ ih b
    induction b with
    | zero => rw [raw_at_zero ha, B.mul_zero, Nat.zero_mod]
    | succ b hb =>
      have bounds := raw_bounds ha b
      rw [raw_succ ha b, ih _ bounds.1 bounds.2, B.row_recurrence a b,
        ← hb, B.mul_mod_left]

private theorem raw_double_return {n : Nat} (B : FiniteTable n) {a : Nat} (ha : a < n * 2) :
    raw (n * 2) a (n * 2) = 0 := by
  obtain ⟨p, hp⟩ := B.exists_firstZero a
  have hpos := hp.1
  have end0 (b : Nat) (hz : B.mul a b = 0) :
      raw (n * 2) a b = 0 ∨ raw (n * 2) a b = n :=
    multiple_below_twice (raw_bounds ha b).1 ((raw_projection B ha b).trans hz)
  have hpd := B.firstZero_dvd_size hp
  have reset {q : Nat} (hd : q ∣ n * 2) (hz : raw (n * 2) a q = 0) :
      raw (n * 2) a (n * 2) = 0 := by
    rw [raw_reduce ha hz, Nat.mod_eq_zero_of_dvd hd, raw_at_zero ha]
  rcases end0 p hp.2.1 with hz | hmid
  · exact reset (Nat.dvd_trans hpd (Nat.dvd_mul_right _ _)) hz
  · have twice : B.mul a (p + p) = 0 := (B.periodic_of_zero hp.2.1 p).trans hp.2.1
    rcases end0 (p + p) twice with hz | hlast
    · apply reset _ hz
      simpa only [Nat.mul_two] using Nat.mul_dvd_mul_right hpd 2
    · have allpos : ∀ k, k ≤ p → raw (n * 2) a (p + k) ≠ 0 := by
        intro k hk hzero
        have he := raw_projection B ha (p + k)
        rw [hzero, Nat.zero_mod, B.periodic_of_zero hp.2.1] at he
        by_cases hk0 : k = 0
        · subst k; simp [hmid, Nat.ne_of_gt B.positive] at hzero
        · by_cases hke : k = p
          · subst k; rw [hlast] at hzero; exact Nat.ne_of_gt B.positive hzero
          · exact hp.2.2 k (by omega) (by omega) he.symm
      have inc : ∀ k, k ≤ p → n + k ≤ raw (n * 2) a (p + k) := by
        intro k
        induction k with
        | zero => simp [hmid]
        | succ k ih =>
          intro hk
          have hold := ih (by omega)
          have hnext := (raw_bounds (raw_bounds ha (p + k)).1 (a + 1)).2
          rw [← raw_succ ha (p + k)] at hnext
          have hlt := hnext.resolve_left (allpos (k + 1) hk)
          exact Nat.le_trans (Nat.succ_le_succ hold) hlt
      have hbad := inc p (Nat.le_refl _)
      rw [hlast] at hbad
      omega

private theorem raw_ld {n : Nat} (hn : 0 < n)
    (wrap : ∀ a, a < n → raw n a n = 0) (a b c : Nat) (ha : a < n) (hb : b < n) :
    raw n a (raw n b c) = raw n (raw n a b) (raw n a c) := by
  let P := fun a b c => raw n a (raw n b c) = raw n (raw n a b) (raw n a c)
  have za : ∀ b, b < n → ∀ c, P 0 b c := by
    intro b hb c
    dsimp [P]
    rw [raw_zero _ hn, raw_zero _ hn, raw_zero _ hn,
      Nat.mod_eq_of_lt (raw_bounds hb c).1, Nat.mod_eq_of_lt hb,
      ← raw_reduce hb (wrap _ hb)]
  apply row_induction (fun a => ∀ b, b < n → ∀ c, P a b c) za _ a ha b hb c
  intro a ha _ higher
  have zb : ∀ c, P a 0 c := by
    intro c
    dsimp [P]
    rw [raw_zero _ hn, raw_at_zero ha, raw_zero _ hn, Nat.mod_eq_of_lt (raw_bounds ha c).1,
      ← raw_reduce ha (wrap _ ha)]
  intro b hb c
  apply row_induction (fun b => ∀ c, P a b c) zb _ b hb c
  intro b hb _ later c
  induction c with
  | zero => simp [P, raw_at_zero hb, raw_at_zero ha, raw_at_zero (raw_bounds ha b).1]
  | succ c hc =>
    have u := raw_bounds hb c
    have v := raw_bounds ha b
    change raw n a (raw n b (c + 1)) = raw n (raw n a b) (raw n a (c + 1))
    rw [raw_succ hb c, later _ u.1 u.2 (b + 1), hc, raw_succ ha b,
      ← higher _ v.1 v.2 _ (raw_bounds ha c).1 (a + 1), ← raw_succ ha c]

private def unitTable : FiniteTable 1 where
  positive := by decide
  op _ _ := 0
  left_distrib _ _ _ := rfl
  right_one _ := Fin.ext (by simp)

private def doubleTable {n : Nat} (B : FiniteTable n) : FiniteTable (n * 2) where
  positive := by have := B.positive; omega
  op a b := ⟨raw (n * 2) a b, (raw_bounds a.isLt b).1⟩
  left_distrib a b c := Fin.ext
    (raw_ld (by have := B.positive; omega) (fun _ h => raw_double_return B h)
      a b c a.isLt b.isLt)
  right_one a := by
    apply Fin.ext
    change raw (n * 2) a (1 % (n * 2)) = _
    have hn := B.positive
    rw [Nat.mod_eq_of_lt (by omega : 1 < n * 2), raw_at_one a.isLt]

/-- All ordinary binary Laver tables, constructed without any assumption. -/
def tables : BinaryFamily
  | 0 => unitTable
  | d + 1 => doubleTable (tables d)

theorem canonical_mul (d a b : Nat) : (tables d).mul a b = entry d a b :=
  (entry_eq_mul d (tables d) a b).symm

end Gamma11
