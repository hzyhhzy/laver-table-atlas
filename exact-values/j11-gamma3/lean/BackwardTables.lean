import BianeRelocation
import CanonicalTables
import LaverLowerBounds.StandardLine

/-! Dougherty's backwards algebra on the natural numbers, constructed
from the same canonical finite tables used at the endpoint. -/
set_option autoImplicit false
namespace Gamma11.Backward
open LaverLowerBounds LaverLowerBounds.FiniteTable

def neg (d x : Nat) : Nat := if x%2^d=0 then 0 else 2^d-x%2^d

theorem neg_lt (d x : Nat) : neg d x<2^d := by
  have p := Nat.two_pow_pos d
  unfold neg; split <;> omega

theorem neg_zero (d : Nat) : neg d 0=0 := by simp [neg]

theorem neg_small {d x : Nat} (pos : 0<x) (small : x<2^d) : neg d x=2^d-x := by
  simp [neg,Nat.mod_eq_of_lt small,Nat.ne_of_gt pos]

theorem neg_neg (d x : Nat) : neg d (neg d x)=x%2^d := by
  by_cases z : x%2^d=0
  · simp [neg,z]
  · have r := Nat.mod_lt x (Nat.two_pow_pos d)
    have n : neg d x=2^d-x%2^d := if_neg z
    have nz : 0<neg d x := by omega
    rw [neg_small nz (neg_lt d x),n]; omega

theorem neg_is_inverse (d x : Nat) : (x+neg d x)%2^d=0 := by
  rw [Nat.add_mod,Nat.mod_eq_of_lt (neg_lt d x)]
  by_cases eqv : x%2^d=0
  · rw [show neg d x=0 from if_pos eqv,eqv,Nat.zero_add,Nat.zero_mod]
  · have small := Nat.mod_lt x (Nat.two_pow_pos d)
    rw [show neg d x=2^d-x%2^d from if_neg eqv,show x%2^d+(2^d-x%2^d)=2^d by omega,Nat.mod_self]

theorem unique_inverse {d x y : Nat} (fit : y<2^d) (sum : (x+y)%2^d=0) : y=neg d x := by
  have adjust := Nat.mod_add_mod_eq (a:=x) (b:=y) (c:=2^d)
  rw [Nat.mod_eq_of_lt fit,sum,Nat.zero_add] at adjust
  have xx := Nat.mod_lt x (Nat.two_pow_pos d)
  unfold neg
  split <;> split at adjust <;> omega

theorem neg_project {s d : Nat} (within : s≤d) (x : Nat) : neg d x%2^s=neg s x := by
  apply unique_inverse (Nat.mod_lt _ (Nat.two_pow_pos s))
  rw [Nat.add_mod_mod,← Nat.mod_mod_of_dvd (x+neg d x) (Nat.pow_dvd_pow 2 within),
    neg_is_inverse,Nat.zero_mod]

def finite (d x y : Nat) := neg d ((tables d).mul (neg d x) (neg d y))

theorem finite_zero_left (d y : Nat) : finite d 0 y=y%2^d := by
  rw [finite,neg_zero,(tables _).zero_mul,Nat.mod_eq_of_lt (neg_lt ..),neg_neg]

theorem finite_zero_right (d x : Nat) : finite d x 0=0 := by
  rw [finite,neg_zero,(tables _).mul_zero,neg_zero]

theorem finite_projects {s d : Nat} (within : s≤d) (x y : Nat) :
    finite d x y%2^s=finite s x y := by
  have modNeg (a : Nat) : neg s a=neg s (a%2^s) := by simp only [neg,Nat.mod_mod]
  rw [finite,neg_project within,modNeg, (tables d).projection (tables s) (Nat.pow_dvd_pow 2 within)]
  unfold finite
  rw [← (tables s).mul_mod_left (neg d x),← (tables s).mul_mod_right _ (neg d y),
    neg_project within,neg_project within]

/-- A nonzero left argument bounds its entire row independently of the
ambient degree. This is what permits a union of ordinary finite sets. -/
theorem finite_below_left {d x : Nat} (pos : 0<x) (fit : x<2^d) (y : Nat) : finite d x y<x := by
  let a := neg d x
  let b := (tables d).mul a (neg d y)
  have below : b<2^d := (tables d).mul_lt .. 
  have grow := (tables d).row_grows a (neg d y) (neg_lt ..)
  change b=0 ∨ a<b at grow
  change neg d b<x
  rcases grow with z|gt
  · rw [z,neg_zero]; exact pos
  · have av : a=2^d-x := neg_small pos fit
    rw [neg_small (by omega : 0<b) below]; omega

theorem finite_stable {s d x : Nat} (within : s≤d) (pos : 0<x) (fit : x<2^s) (y : Nat) :
    finite d x y=finite s x y := by
  have large := Nat.lt_of_lt_of_le fit (Nat.pow_le_pow_right (by decide) within)
  have less := Nat.lt_trans (finite_below_left pos large y) fit
  exact (Nat.mod_eq_of_lt less).symm.trans (finite_projects within x y)

/-- Row zero is the identity; for every positive left argument even an
arbitrarily large right argument can be read in the same finite table. -/
def mul (x y : Nat) : Nat := if x=0 then y else finite (x.log2+1) x y

theorem at_degree {d x : Nat} (pos : 0<x) (fit : x<2^d) (y : Nat) : mul x y=finite d x y := by
  rw [mul,if_neg (Nat.ne_of_gt pos)]
  have minimal : x.log2<d := (Nat.log2_lt (by omega)).mpr fit
  exact (finite_stable minimal pos (Nat.lt_log2_self (n:=x)) y).symm

theorem mul_projects (d x y : Nat) : mul x y%2^d=finite d x y := by
  by_cases zero : x=0
  · subst x; rw [mul,if_pos rfl,finite_zero_left]
  · let h := max d (x.log2+1)
    have fit : x<2^h := Nat.lt_of_lt_of_le (Nat.lt_log2_self (n:=x))
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..))
    rw [at_degree (Nat.pos_of_ne_zero zero) fit,finite_projects (Nat.le_max_left ..)]

theorem mul_zero_right (x : Nat) : mul x 0=0 := by simp [mul,finite_zero_right]

theorem mul_zero_left (y : Nat) : mul 0 y=y := by simp [mul]

theorem mul_lt_left {x : Nat} (pos : 0<x) (y : Nat) : mul x y<x := by
  rw [at_degree pos (Nat.lt_log2_self (n:=x))]
  exact finite_below_left pos (Nat.lt_log2_self (n:=x)) y

theorem mul_distrib (x y z : Nat) : mul x (mul y z)=mul (mul x y) (mul x z) := by
  let u := mul x (mul y z)
  let v := mul (mul x y) (mul x z)
  let d := (max u v).log2+1
  have room : max u v<2^d := Nat.lt_log2_self
  have proj (a : Nat) : neg d a=neg d (a%2^d) := by simp [neg]
  have core (a b : Nat) :
      neg d (mul a b)=(tables d).mul (neg d a) (neg d b) := by
    rw [proj (mul a b),mul_projects,finite,neg_neg,Nat.mod_eq_of_lt ((tables d).mul_lt ..)]
  have eqv : neg d u=neg d v := by
    dsimp only [u,v]
    rw [core,core,core,core,core,(tables d).mul_distrib]
  have double := congrArg (neg d) eqv
  change neg d (neg d u)=neg d (neg d v) at double
  rwa [neg_neg,neg_neg,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_left ..) room),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_right ..) room)] at double

#print axioms mul_projects
#print axioms mul_distrib

theorem neg_eq_zero_iff (d x : Nat) : neg d x=0 ↔ x%2^d=0 := by
  have fit := Nat.mod_lt x (Nat.two_pow_pos d)
  unfold neg
  split <;> omega

theorem finite_zero_iff (d x y : Nat) :
    finite d x y=0 ↔ (tables d).mul (neg d x) y=0 := by
  rw [finite,neg_eq_zero_iff,Nat.mod_eq_of_lt ((tables d).mul_lt ..)]
  obtain ⟨p,hp⟩ := (tables d).exists_firstZero (neg d x)
  rw [(tables d).firstZero_iff_mod hp,(tables d).firstZero_iff_mod hp,
    ← Nat.dvd_iff_mod_eq_zero,← Nat.dvd_iff_mod_eq_zero]
  have dv := Nat.dvd_trans ((tables d).firstZero_dvd_size hp)
    (Nat.dvd_of_mod_eq_zero (neg_is_inverse d y))
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr dv,fun h => (Nat.dvd_add_iff_right h).mpr dv⟩

/-- The least zero is a power of two. This predicate characterizes its
exponent without depending on a choice of a containing finite table. -/
def PeriodExp (x l : Nat) : Prop := ∀ q, mul x (2^q)=0 ↔ l≤q

theorem has_period_exp {x : Nat} (pos : 0<x) : ∃ l, PeriodExp x l := by
  let d := x.log2+1
  have fit : x<2^d := Nat.lt_log2_self
  obtain ⟨p,hp⟩ := (tables d).exists_firstZero (neg d x)
  obtain ⟨l,_,rfl⟩ := period_is_power_two tables d _ _ hp
  refine ⟨l,fun q => ?_⟩
  rw [at_degree pos fit,finite_zero_iff,(tables d).firstZero_iff_mod hp,pow_mod_zero_iff]

theorem zero_at_width {x k : Nat} (pos : 0<x) (fits : x≤2^k) : mul x (2^k)=0 := by
  have pr := mul_projects k x (2^k)
  have zero : neg k (2^k)=0 := (neg_eq_zero_iff ..).mpr (Nat.mod_self _)
  rw [finite,zero,(tables _).mul_zero,neg_zero,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_left pos _) fits)] at pr
  exact pr

/-- Dougherty II, Lemma 4.5, obtained from the ordinary finite-table
dyadic crossing bound. A nonzero low digit suffices for any two-block
word, irrespective of its upper digit. -/
theorem two_block_period {e x : Nat} (fit : x<2^(2*2^e)) (low : x%2^(2^e)≠0) :
    mul x (2^(2^e))=0 := by
  let n := 2^e
  let d := 2*n
  have xy : 0<x := by
    apply Nat.pos_of_ne_zero
    intro h
    exact low (by rw [h,Nat.zero_mod])
  rw [at_degree xy fit,finite_zero_iff]
  have nle : n≤d := by dsimp [d]; omega
  have grow := anchors_to_bound tables (d+1) e (Nat.lt_succ_self _)
    (dyadic_anchors tables e (d+1) (by dsimp [d,n] at *; omega))
  have nz : neg d x%2^n≠0 := by
    rw [neg_project nle]; exact fun bad => low ((neg_eq_zero_iff ..).mp bad)
  have reached := (grow (neg d x) nz).1
  exact (le_act_iff tables (d+1) (neg d x) n d (Nat.le_succ d)).mp reached

#print axioms has_period_exp
#print axioms two_block_period

theorem of_forward_zero {d x a k : Nat} (pos : 0<x) (fit : x<2^d)
    (opposites : (x+a)%2^d=0) (zero : act tables d a k=d) : mul x (2^k)=0 := by
  have eqv : a%2^d=neg d x := unique_inverse (Nat.mod_lt _ (Nat.two_pow_pos d)) (by rwa [Nat.add_mod_mod])
  rw [at_degree pos fit,finite_zero_iff,← eqv,(tables _).mul_mod_left]
  exact (le_act_iff tables d a k d (Nat.le_refl _)).mp (Nat.le_of_eq zero.symm)

theorem to_forward_zero {d x a k : Nat} (opposites : (x+a)%2^d=0) (zero : mul x (2^k)=0) :
    act tables d a k=d := by
  have eqv : a%2^d=neg d x := unique_inverse (Nat.mod_lt _ (Nat.two_pow_pos d)) (by rwa [Nat.add_mod_mod])
  have pr := mul_projects d x (2^k)
  rw [zero,Nat.zero_mod] at pr
  have eq0 := (finite_zero_iff d x (2^k)).mp pr.symm
  rw [← eqv,(tables _).mul_mod_left] at eq0
  exact Nat.le_antisymm (act_le ..) ((le_act_iff tables d a k d (Nat.le_refl d)).mpr eq0)

theorem neg_mul (d x y : Nat) : neg d (mul x y)=(tables d).mul (neg d x) (neg d y) := by
  have same : neg d (mul x y)=neg d (mul x y%2^d) := by simp only [neg,Nat.mod_mod]
  rw [same,mul_projects,finite,neg_neg,Nat.mod_eq_of_lt ((tables d).mul_lt ..)]

theorem negate_succ (d x : Nat) : (neg d (x+1)+1)%2^d=neg d x := by
  apply unique_inverse (Nat.mod_lt _ (Nat.two_pow_pos d))
  rw [Nat.add_mod_mod,show x+(neg d (x+1)+1)=x+1+neg d (x+1) by omega,neg_is_inverse]

theorem eq_of_neg_all {x y : Nat} (same : ∀ d, neg d x=neg d y) : x=y := by
  let d := (max x y).log2+1
  have bound : max x y<2^d := Nat.lt_log2_self
  have pr := congrArg (neg d) (same d)
  change neg d (neg d x)=neg d (neg d y) at pr
  rwa [neg_neg,neg_neg,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_left ..) bound),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_max_right ..) bound)] at pr

/-- A generated row is the composite of its representing rows. This is
the backward form of composition in the ordinary finite table. -/
theorem compose_rows (x p y : Nat) : mul (mul x p+1) y=mul x (mul (p+1) y) := by
  apply eq_of_neg_all
  intro d
  let T := tables d
  let a := neg d x
  let b := neg d (p+1)
  have next : (T.comp a b+1)%2^d=neg d (mul x p) := by
    rw [← T.mul_one,T.comp_one,← T.mul_mod_right a (b+1)]
    change T.mul a ((neg d (p+1)+1)%2^d)=_
    rw [negate_succ,neg_mul]
  have same := (negate_succ d (mul x p)).trans next.symm
  have back := congrArg (fun n => (n+2^d-1)%2^d) same
  change (((neg d (mul x p+1)+1)%2^d+2^d-1)%2^d)=(((T.comp a b+1)%2^d+2^d-1)%2^d) at back
  have small : T.comp a b<2^d := Nat.mod_lt _ (Nat.two_pow_pos d)
  rw [T.predecessor_successor,T.predecessor_successor,Nat.mod_eq_of_lt (neg_lt ..),
    Nat.mod_eq_of_lt small] at back
  rw [neg_mul,back,T.comp_mul,neg_mul,neg_mul]

theorem zero_iff_period {x l : Nat} (pos : 0<x) (period : PeriodExp x l) (y : Nat) :
    mul x y=0 ↔ y%2^l=0 := by
  let d := x.log2+1
  have fit : x<2^d := Nat.lt_log2_self
  obtain ⟨p,hp⟩ := (tables d).exists_firstZero (neg d x)
  obtain ⟨s,_,rfl⟩ := period_is_power_two tables d _ _ hp
  have alt (b : Nat) : mul x b=0 ↔ b%2^s=0 := by
    rw [at_degree pos fit,finite_zero_iff,(tables d).firstZero_iff_mod hp]
  have eql (q : Nat) : s≤q ↔ l≤q := by rw [← pow_mod_zero_iff,← alt,period]
  have eqv := Nat.le_antisymm ((eql l).mpr (Nat.le_refl _)) ((eql s).mp (Nat.le_refl _))
  exact eqv ▸ alt y

theorem period_last (x l : Nat) (period : PeriodExp (x+1) l) : mul (x+1) (2^l-1)=x := by
  let d := max (x+1) l+1
  have room : l≤d := Nat.le_trans (Nat.le_max_right ..) (Nat.le_succ _)
  have fit : x+1<2^d := Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left ..) (Nat.le_succ _))
    (Nat.lt_two_pow_self (n:=d))
  have top := (period l).mpr (Nat.le_refl _)
  rw [at_degree (Nat.zero_lt_succ _) fit,finite_zero_iff] at top
  have idx : neg d (2^l-1)%2^l=1%2^l := by
    rw [neg_project room]
    symm
    apply unique_inverse (Nat.mod_lt _ (Nat.two_pow_pos _))
    rw [Nat.add_mod_mod,Nat.sub_add_cancel (Nat.two_pow_pos l),Nat.mod_self]
  have v := neg_mul d (x+1) (2^l-1)
  rw [(tables _).reduce_period top,idx,← (tables _).reduce_period top 1,(tables _).mul_one,negate_succ] at v
  have iv := congrArg (neg d) v
  change neg d (neg d (mul (x+1) (2^l-1)))=neg d (neg d x) at iv
  rwa [neg_neg,neg_neg,Nat.mod_eq_of_lt (Nat.lt_trans (mul_lt_left (Nat.zero_lt_succ _) _) fit),
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self _) fit)] at iv

#print axioms compose_rows
#print axioms period_last

end Gamma11.Backward
