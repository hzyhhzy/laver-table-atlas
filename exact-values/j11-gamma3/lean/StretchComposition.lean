import DoubleWidths

/-! Compose repeated-digit maps, retaining one bit beyond the old
target degree. That bit suffices to read the last visible image. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

theorem testBit_repeatBits {w : Nat} (pos : 0<w) (n x j : Nat) :
    (repeatBits w n x).testBit j = if j/w<n then x.testBit (j/w) else false := by
  induction n generalizing x j with
  | zero => simp [repeatBits]
  | succ n ih =>
    let digit := if x%2=0 then 0 else 2^w-1
    have small : digit<2^w := by
      dsimp [digit]; have p:=Nat.two_pow_pos w; split <;> omega
    change (digit+2^w*repeatBits w n (x/2)).testBit j=_
    rw [Nat.add_comm digit,Nat.testBit_two_pow_mul_add _ small]
    by_cases low : j<w
    · have zero := Nat.div_eq_of_lt low
      rw [if_pos low,zero,if_pos (Nat.zero_lt_succ _),Nat.testBit_zero]
      dsimp [digit]
      split
      next eqv => simp [eqv]
      next neq =>
        have odd : x%2=1 := by omega
        simp [Nat.testBit_two_pow_sub_one,low,odd]
    · have div : j/w=(j-w)/w+1 := by
        have add : j-w+w=j := by omega
        exact (congrArg (fun t => t/w) add).symm.trans (Nat.add_div_right (j-w) pos)
      rw [if_neg low,ih,div,Nat.testBit_div_two]
      by_cases bound : (j-w)/w<n
      · rw [if_pos bound,if_pos (by omega)]
      · rw [if_neg bound,if_neg (by omega)]

theorem repeatBits_compose {u v : Nat} (up : 0<u) (vp : 0<v) (k x : Nat) :
    repeatBits v (k*u) (repeatBits u k x)=repeatBits (u*v) k x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_repeatBits vp,testBit_repeatBits (Nat.mul_pos up vp)]
  have div : i/v/u=i/(u*v) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm v u]
  have cut : i/v < k*u ↔ i/(u*v)<k := by rw [← div,Nat.div_lt_iff_lt_mul up]
  by_cases small : i/v<k*u
  · rw [if_pos small,testBit_repeatBits up,div,if_pos (cut.mp small)]
  · rw [if_neg small,if_neg (fun h => small (cut.mpr h))]

theorem stretch_hom_compose {u v k : Nat} (up : 0<u) (vp : 0<v)
    (first : StretchHomAt u k) (second : StretchHomAt v (k*u)) : StretchHomAt (u*v) k := by
  intro a b aa bb
  rw [← repeatBits_compose up vp,first a b aa bb,
    second _ _ (repeatBits_lt u k a) (repeatBits_lt u k b),repeatBits_compose up vp,
    repeatBits_compose up vp,Nat.mul_assoc]

/-- The homomorphism is from degree k+1 to degree kw+1. Below the
middle column its row is digit repetition; the middle maps to the
single upper bit. No values in the second half have to be specified. -/
def StretchWithTop (w k : Nat) : Prop := ∃ f : Nat → Nat,
  (∀ a, a<2^(k+1) → f a<2^(k*w+1)) ∧
  (∀ a b, a<2^(k+1) → b<2^(k+1) →
    f ((tables (k+1)).mul a b)=(tables (k*w+1)).mul (f a) (f b)) ∧
  (∀ a, a<2^k → f a=repeatBits w k a) ∧ f (2^k)=2^(k*w)

theorem native_stretch_with_top (H : FirstRowUnbounded) (law : FiniteBlockLaw)
    {v k : Nat} (dyadic : IsDyadic v) (wide : 2≤v) (sources : AllUpperBridges v)
    (fit : k≤v) : StretchWithTop v k := by
  let d := k*v+1
  let h := v*v+1
  let L := 2^v-2
  have bound := Nat.mul_le_mul_right v fit
  have dh : d≤h := by dsimp [d,h]; omega
  have room := Nat.mul_le_mul_left v wide
  rw [Nat.mul_two] at room
  have br := sources h (by dsimp [h]; omega)
  have high := native_stretch_actions H law dyadic wide br (Nat.lt_succ_self (v*v)) fit
  have reduced := act_at_smaller_degree tables dh L k
  change act tables h L k=k*v at high
  rw [high,Nat.min_eq_right (Nat.le_succ _)] at reduced
  have after := act_next tables d L k (by rw [reduced]; exact Nat.lt_succ_self _)
  have zero := (le_act_iff tables d L (k+1) d (Nat.le_refl _)).mp
    (by rw [reduced] at after; exact after)
  have kd : k+1≤d := by
    have p := Nat.mul_le_mul_left k (show 1≤v by omega)
    rw [Nat.mul_one] at p; dsimp [d]; omega
  refine ⟨(tables d).mul L,fun a _ => (tables d).mul_lt L a,?_,?_,?_⟩
  · intro a b _ _
    have pr := (tables d).projection (tables (k+1)) (Nat.pow_dvd_pow 2 kd) a b
    have per := (tables d).reduce_period zero ((tables d).mul a b)
    rw [pr] at per
    exact per.symm.trans ((tables d).mul_distrib L a b)
  · intro a small
    cases a with
    | zero => rw [(tables _).mul_zero,repeatBits_zero]
    | succ a =>
      have row := native_stretch_prefix H law dyadic wide br a
        (Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) fit))
      change (tables h).mul L (a+1)=_ at row
      rw [repeatBits_padding v k v (a+1) fit small] at row
      have proj := (tables h).projection (tables d) (Nat.pow_dvd_pow 2 dh) L (a+1)
      have native := Nat.lt_trans (repeatBits_lt v k (a+1)) (Nat.pow_lt_pow_succ (by decide : 1<2))
      rw [row,Nat.mod_eq_of_lt native] at proj
      exact proj.symm
  · exact (canonical_mul d L (2^k)).symm.trans ((exact_iff_act tables L k (k*v)).mpr reduced)

#print axioms native_stretch_with_top

theorem compose_stretch_with_top {u v k : Nat} (up : 0<u) (vp : 0<v)
    (s₁ : StretchWithTop u k) (s₂ : StretchWithTop v (k*u)) : StretchWithTop (u*v) k := by
  obtain ⟨f,ff,fhom,flow,ftop⟩ := s₁
  obtain ⟨g,gg,ghom,glow,gtop⟩ := s₂
  refine ⟨fun x => g (f x),?_,?_,?_,?_⟩
  · intro a fit
    rw [← Nat.mul_assoc]
    exact gg _ (ff _ fit)
  · intro a b aa bb
    dsimp only
    rw [fhom a b aa bb,ghom _ _ (ff _ aa) (ff _ bb),Nat.mul_assoc]
  · intro a small
    dsimp only
    rw [flow a small,glow _ (repeatBits_lt ..),repeatBits_compose up vp]
  · dsimp only
    rw [ftop,gtop,Nat.mul_assoc]

private theorem parameter_caps (H : FirstRowUnbounded) (law : FiniteBlockLaw) (e k : Nat)
    (fit : k≤256^(2^e)) :
    StretchHomAt (256^(2^e)) k ∧ StretchWithTop (256^(2^e)) k := by
  have old := auxiliary_stretches_from_blocks H law (2^e) ⟨e,rfl⟩ k fit
  refine ⟨old,?_⟩
  have power : 256^(2^e)=2^(2^(e+3)) := by
    rw [show 256=2^8 by decide,← Nat.pow_mul,Nat.pow_add 2 e 3,Nat.mul_comm 8]
  rw [power] at fit ⊢
  exact native_stretch_with_top H law ⟨_,rfl⟩
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.two_pow_pos _))
    (double_width_bridges H law (e+3)) fit

/-- Factor 256^m at the leading binary digit of m. Every subsequent
special-width map accepts the whole preceding source, including its
extra top bit. -/
theorem all_width_caps (H : FirstRowUnbounded) (law : FiniteBlockLaw) (m : Nat) (mp : 0<m) :
    StretchHomAt (256^m) 256 ∧ StretchWithTop (256^m) 256 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    let b := 2^m.log2
    have bp : 0<b := Nat.two_pow_pos _
    have bm : b≤m := Nat.log2_self_le (by omega)
    have limit := Nat.lt_log2_self (n:=m)
    rw [Nat.pow_succ] at limit
    change m<b*2 at limit
    by_cases last : m=b
    · have ge : 256≤256^b := Nat.pow_le_pow_right (by decide : 0<256) bp
      exact last ▸ parameter_caps H law m.log2 256 ge
    · let r := m-b
      have rp : 0<r := by dsimp [r]; omega
      have low := ih r (by dsimp [r]; omega) rp
      have permitted : 256*256^r≤256^b := by
        rw [Nat.mul_comm,← Nat.pow_succ]
        exact Nat.pow_le_pow_right (by decide) (by dsimp [r]; omega)
      have high := parameter_caps H law m.log2 (256*256^r) permitted
      have product : 256^r*256^b=256^m := by
        rw [← Nat.pow_add,Nat.sub_add_cancel bm]
      have up : 0<256^r := Nat.pow_pos (by decide)
      have vp : 0<256^b := Nat.pow_pos (by decide)
      exact product ▸ And.intro (stretch_hom_compose up vp low.1 high.1)
        (compose_stretch_with_top up vp low.2 high.2)

theorem capped_stretch_row {w k : Nat} (wp : 0<w) (kp : 0<k) (stretch : StretchWithTop w k) :
    (∀ y, y<2^k → (tables (k*w+1)).mul (2^w-2) y=repeatBits w k y) ∧
    (tables (k*w+1)).mul (2^w-2) (2^k)=2^(k*w) := by
  obtain ⟨f,_,hom,lo,top⟩ := stretch
  have one : 1<2^k := Nat.one_lt_two_pow (by omega)
  have one' := Nat.lt_trans one (Nat.pow_lt_pow_succ (by decide : 1<2))
  have size : 2≤2^w := Nat.pow_le_pow_right (by decide : 0<2) wp
  have lift : 2^w-2+1=2^w-1 := by omega
  have row (y : Nat) (fit : y<2^(k+1)) : (tables (k*w+1)).mul (2^w-2) y=f y := by
    induction y with
    | zero => rw [(tables _).mul_zero,lo 0 (Nat.two_pow_pos _),repeatBits_zero]
    | succ y ih =>
      have h := hom y 1 (by omega) one'
      rw [(tables _).mul_one,Nat.mod_eq_of_lt fit,lo 1 one,repeatBits_one w k kp] at h
      rw [(tables _).row_recurrence,ih (by omega),lift,← h]
  refine ⟨fun y fit => (row y (Nat.lt_trans fit (Nat.pow_lt_pow_succ (by decide)))).trans (lo y fit),?_⟩
  exact (row _ (Nat.pow_lt_pow_succ (by decide))).trans top

theorem capped_stretch_action {w k : Nat} (wp : 0<w) (kp : 0<k) (stretch : StretchWithTop w k) :
    act tables (k*w+1) (2^w-2) k=k*w := by
  apply (exact_iff_act tables (2^w-2) k (k*w)).mp
  rw [← canonical_mul,(capped_stretch_row wp kp stretch).2]

/-- The two actual readings needed in the older diagonal route, derived
from the block law and ordinary first-row unboundedness. -/
theorem licensed_readings (H : FirstRowUnbounded) (law : FiniteBlockLaw) (m : Nat) (mp : 0<m) :
    StretchHomAt (256^m) 256 ∧ image H (2^(256^m)-2) 256=256*256^m := by
  obtain ⟨old,top⟩ := all_width_caps H law m mp
  have read := capped_stretch_action (Nat.pow_pos (by decide : 0<256)) (by decide : 0<256) top
  rw [numeral_cap_eq_min H] at read
  exact ⟨old,by omega⟩

#print axioms all_width_caps
#print axioms licensed_readings
end Gamma11
