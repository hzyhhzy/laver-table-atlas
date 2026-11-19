import Gamma11Endpoint
import LaverLowerBounds.FiniteCongruence

/-! Two of the changes of cut in Appendix A.3, derived inside the
ordinary tables. The source cut is the (possibly capped) second image of
11. Its actual numerical value is not required. -/

set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

private theorem raw_four (F : BinaryFamily) (n a : Nat) (fit : a+4 < 2^n)
    (modOne : (a+1)%4 = 1) (zero : ∀ i, 1≤i → i<4 → (F n).mul (a+i) 4 = 0) :
    (F n).mul a 4 = a+4 := by
  have prefixAt (i : Nat) (within : i<4) : (F n).mul a (i+1) = a+(i+1) := by
    induction i with
    | zero => exact ((F n).mul_one a).trans (Nat.mod_eq_of_lt (by omega))
    | succ i ih =>
      rw [(F n).row_recurrence,ih (by omega),(F n).reduce_period (zero _ (by omega) (by omega)),
        modOne,(F n).mul_one,Nat.add_assoc,Nat.mod_eq_of_lt (by omega)]
  exact prefixAt 3 (by decide)

/-- As long as row 11 vanishes at column 4, row 1 has its raw second
entry 12 (projected to the size of the table). -/
theorem one_two_before_eleven_second (F : BinaryFamily) (n : Nat) (h : (F n).mul 11 4 = 0) :
    (F n).mul 1 2 = 12 % 2^n := by
  by_cases small : n ≤ 9
  · rw [← (F 9).projection (F n) (Nat.pow_dvd_pow 2 small),LowProducts.v1_2]
  have h9 : 9 ≤ n := by omega
  have size : 512 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0<2) h9
  have j1 := act_from_low F n 1 1 12 2 h9 (LowProducts.v1_2 (F 9)) (by decide) (by decide)
  have j2 := act_from_low F n 1 2 240 4 h9 (LowProducts.v1_4 (F 9)) (by decide) (by decide)
  have pass (a x y k : Nat) (lo : a≤10) (gen : act F n 1 x = y)
      (start : k ≤ act F n a x) (next : act F n (a+1) k = n) : act F n a y = n := by
    have cross := act_application F n a 1 x
    rw [(F n).mul_one,Nat.mod_eq_of_lt (by omega : a+1<2^n),gen] at cross
    have up := act_mono F n (a+1) start
    rw [next,cross] at up
    exact Nat.le_antisymm (act_le ..) up
  have start2 (a v : Nat) (known : (F 9).mul a 2 = v) (div : v%4=0) : 2 ≤ act F n a 1 := by
    apply (le_act_iff F n a 1 2 (by omega)).mpr
    change (F 2).mul a 2 = 0
    rw [← (F 9).projection (F 2) (Nat.pow_dvd_pow 2 (by decide : 2≤9)),known]
    exact div
  have h11 := Nat.le_antisymm (act_le F n 11 2) ((le_act_iff F n 11 2 n (Nat.le_refl _)).mpr h)
  have h10 := pass 10 1 2 2 (by decide) j1 (start2 _ _ (LowProducts.v10_2 _) (by decide)) h11
  have h09 := pass 9 1 2 2 (by decide) j1 (start2 _ _ (LowProducts.v9_2 _) (by decide)) h10
  have h08 := pass 8 2 4 2 (by decide) j2 (le_act F n 8 2 (by omega)) h09
  have seven := act_from_low F n 7 1 496 4 h9 (LowProducts.v7_2 _) (by decide) (by decide)
  have h07 := pass 7 1 2 4 (by decide) j1 (Nat.le_of_eq seven.symm) h08
  have h06 := pass 6 1 2 2 (by decide) j1 (start2 _ _ (LowProducts.v6_2 _) (by decide)) h07
  have h05 := pass 5 1 2 2 (by decide) j1 (start2 _ _ (LowProducts.v5_2 _) (by decide)) h06
  have four (a : Nat) (atCap : act F n a 2 = n) : (F n).mul a 4 = 0 :=
    (le_act_iff F n a 2 n (Nat.le_refl _)).mp (Nat.le_of_eq atCap.symm)
  have first := raw_four F n 4 (by omega) (by decide) (by
    intro i lo hi
    rcases (show i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl
    · exact four _ h05
    · exact four _ h06
    · exact four _ h07)
  have second := raw_four F n 8 (by omega) (by decide) (by
    intro i lo hi
    rcases (show i=1 ∨ i=2 ∨ i=3 by omega) with rfl|rfl|rfl
    · exact four _ h09
    · exact four _ h10
    · exact h)
  have successor (a : Nat) (bound : a≤3) : (F n).mul a 1 = a+1 :=
    ((F n).mul_one _).trans (Nat.mod_eq_of_lt (by omega))
  have p3 : (F n).mul 3 2 = 8 := by
    rw [(F n).row_recurrence 3 1,successor 3 (by decide)]; exact first
  have p33 : (F n).mul 3 3 = 12 := by
    rw [(F n).row_recurrence 3 2,p3]; exact second
  have p22 : (F n).mul 2 2 = 12 := by
    rw [(F n).row_recurrence 2 1,successor 2 (by decide)]; exact p33
  rw [(F n).row_recurrence 1 1,successor 1 (by decide),Nat.mod_eq_of_lt (by omega : 12<2^n)]
  exact p22

theorem one_two_at_256 (F : BinaryFamily) : (F 256).mul 1 2 = 12 := by
  apply one_two_before_eleven_second F 256
  apply (le_act_iff F 256 11 2 256 (Nat.le_refl _)).mp
  exact Nat.le_of_not_gt (fun h => (Nat.not_lt_of_ge (eleven_second_lower F 256 (by decide) h)) h)

/-- At the source cut u=f_11(2), 12 represents 1*2, and 11
represents the ordinary composition of 1 with itself. -/
theorem twelve_source_cut (F : BinaryFamily) (d : Nat) :
    let u := act F d 11 2
    congruent d u 12 ((F d).mul 1 2) ∧ congruent d u 11 ((F d).comp 1 1) := by
  let u := act F d 11 2
  have within : u≤d := act_le .. 
  have hit := one_two_before_eleven_second F u
    ((le_act_iff F d 11 2 u within).mp (Nat.le_refl _))
  dsimp only
  change congruent d u 12 _ ∧ congruent d u 11 _
  unfold congruent
  rw [Nat.min_eq_left within,(F d).projection (F u) (Nat.pow_dvd_pow 2 within),
    (F d).comp_projection (F u) (Nat.pow_dvd_pow 2 within),hit]
  refine ⟨rfl,?_⟩
  change 11%2^u = ((F u).mul 1 2 + 2^u - 1)%2^u
  rw [hit]
  exact ((F u).predecessor_successor 11).symm

/-- Both 12 and 13 send u to the cap, without an exact evaluation of u.
The comparison u ≤ f_1(4) follows by reading the composition 1∘1
at index 2 in the source cut. -/
theorem twelve_thirteen_reach (F : BinaryFamily) (d : Nat) (old : 9≤d) (upper : d≤targetIndex+1) :
    let u := act F d 11 2
    act F d 12 u = d ∧ act F d 13 u = d := by
  let u := act F d 11 2
  have j1 := act_from_low F d 1 1 12 2 old (LowProducts.v1_2 _) (by decide) (by decide)
  have j2 := act_from_low F d 1 2 240 4 old (LowProducts.v1_4 _) (by decide) (by decide)
  have k1 := act_from_low F d 11 1 496 4 old (LowProducts.v11_2 _) (by decide) (by decide)
  have size : 512 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0<2) old
  have step (a : Nat) (small : a≤12) : (F d).mul a 1 = a+1 :=
    ((F d).mul_one _).trans (Nat.mod_eq_of_lt (by omega))
  have b4 : act F d 12 4 = u := by
    have h := act_application F d 11 1 1
    rw [step 11 (by decide),k1,j1] at h
    exact h
  have fourth : act F d 11 4 = d := by
    apply Nat.le_antisymm (act_le ..)
    apply Nat.le_of_not_gt
    intro vis
    have strict := act_strict_below_cap F d 11 3 4 (by decide) vis
    have bound := eleven_third_lower F d old (Nat.lt_trans strict vis)
    omega
  have b : act F d 12 u = d := by
    have h := act_application F d 11 1 2
    rw [step 11 (by decide),j2,fourth] at h
    exact h
  have j4 := congruent_action_ge F d ((twelve_source_cut F d).2) (x:=2) (Nat.le_refl u)
  rw [act_composition,j2] at j4
  have c := act_application F d 12 1 4
  rw [step 12 (by decide),b4] at c
  have bound := act_mono F d 12 j4
  change act F d 12 u ≤ _ at bound
  rw [b,← c] at bound
  exact ⟨b,Nat.le_antisymm (act_le ..) bound⟩

/-- At the target degree these are respectively the S, P and U equations
of (A3), with D0 still written as its actual row 13*3. -/
theorem normal_transports (F : BinaryFamily) (d : Nat) (lower : 9≤d) (upper : d≤targetIndex+1) :
    let T := F d
    let D := T.mul 13 3
    let S := T.mul 13 12
    let P := T.mul 13 13
    S = T.mul D D ∧ P = T.mul S 14 ∧ T.mul 12 12 = T.mul P P := by
  let T := F d
  let u := act F d 11 2
  have size : 512 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0<2) lower
  have step (a : Nat) (small : a≤13) : T.mul a 1 = a+1 :=
    (T.mul_one _).trans (Nat.mod_eq_of_lt (by omega))
  obtain ⟨b,c⟩ := twelve_thirteen_reach F d lower upper
  have move (a : Nat) (reach : act F d a u = d) : T.mul a 12 = T.mul a (T.mul 1 2) := by
    have h := congruent_transport F d ((twelve_source_cut F d).1) a
    change congruent d (act F d a u) (T.mul a 12) (T.mul a (T.mul 1 2)) at h
    simpa only [reach,congruent,Nat.min_self,Nat.mod_eq_of_lt (T.mul_lt _ _)] using h
  have j : T.mul 1 2 = T.mul 3 3 := by
    have a := T.mul_distrib 1 1 1
    have b' := T.mul_distrib 2 1 1
    rw [step 1 (by decide)] at a
    rw [step 1 (by decide),step 2 (by decide)] at b'
    exact a.trans b'
  have P : T.mul 12 2 = T.mul 13 13 := by
    have h := T.mul_distrib 12 1 1
    rwa [step 1 (by decide),step 12 (by decide)] at h
  have first := move 13 c
  rw [j,T.mul_distrib] at first
  have second := T.mul_distrib 13 12 1
  rw [step 12 (by decide),step 13 (by decide)] at second
  have last := move 12 b
  rw [T.mul_distrib,step 12 (by decide),P,T.mul_distrib] at last
  exact ⟨first,second,last⟩

#print axioms one_two_at_256
#print axioms twelve_thirteen_reach
#print axioms normal_transports

end Gamma11
