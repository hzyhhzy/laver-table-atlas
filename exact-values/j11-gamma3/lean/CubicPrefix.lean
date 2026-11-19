import CubicSquare
import IntervalCut

/-! The first eight entries of the cubic seed. The sixth uses the
period of a relocated positive row and left distributivity. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 16777217
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

set_option linter.unusedSimpArgs false in
theorem seven_from_two_products (F : BinaryFamily) {n q s : Nat}
    (width : 2≤n) (nq : n<q) (qs : q<s)
    (square : (F (s+1)).mul (2^n-2) (2^n-2)=2^q-2^n)
    (four : (F (s+1)).mul (2^q-2) (2^n-2)=2^s-2^q)
    (add : ∀ A, 0<A → 2^n∣A → A+(2^n-2)<2^(s+1) →
      (F (s+1)).mul A (2^n-2)=A+(2^n-2))
    {f : Nat → Nat} (f0 : f 0=1) (f1 : f 1=n) (f2 : f 2=q) (f3 : f 3=s)
    (y : Nat) (below : y<8) : (F (s+1)).mul (2^n-3) y=intervalWord f 0 3 y := by
  let L := F (s+1)
  let p := 2^n
  let Z := 2^q
  let U := 2^s
  let g := p-3
  let a := p-2
  let V := Z-p
  let K := U-Z
  have pp : 4≤p := Nat.pow_le_pow_right (by decide : 0<2) width
  have pZ : p<Z := Nat.pow_lt_pow_right (by decide) nq
  have ZU : Z<U := Nat.pow_lt_pow_right (by decide) qs
  have top : U<2^(s+1) := Nat.pow_lt_pow_succ (by decide)
  have aa : 0<a := by dsimp [a]; omega
  have az : a<Z := by dsimp [a]; omega
  have ga : g+1=a := by dsimp [g,a]; omega
  have Vp : 2^n∣V := Nat.dvd_sub (Nat.pow_dvd_pow 2 (Nat.le_of_lt nq)) (Nat.dvd_refl _)
  have Kz : Z∣K := Nat.dvd_sub (Nat.pow_dvd_pow 2 (Nat.le_of_lt qs)) (Nat.dvd_refl _)
  have up : p∣U-p := Nat.dvd_sub (Nat.pow_dvd_pow 2 (Nat.le_of_lt (Nat.lt_trans nq qs))) (Nat.dvd_refl _)
  have vadd : L.mul V a=Z-2 := (add V (by dsimp [V]; omega) Vp (by dsimp [V]; change Z-p+(p-2)<_; omega)).trans
    (by change Z-p+(p-2)=Z-2; omega)
  have ka : L.mul K a=K+a := gap_prefix F qs a aa (Nat.le_of_lt az)
  have kv : L.mul K V=K+V := gap_prefix F qs V (by dsimp [V]; omega) (Nat.sub_le ..)
  have zero : L.mul (K+a) Z=0 := (biane_zero_iff F (Nat.le_of_lt qs) aa az Z).mpr
    (positive_half_zero F q a aa (Nat.lt_trans az (Nat.pow_lt_pow_succ (by decide))))
  have modK : (K+a)%Z=a := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd Kz,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt az]
  have reduce := L.reduce_period zero (K+a)
  rw [modK] at reduce
  have ld := L.mul_distrib K a a
  change L.mul a a=V at square
  rw [square,kv,ka,reduce] at ld
  have sixth : L.mul (K+a) a=U-p := ld.symm.trans (by change U-Z+(Z-p)=U-p; omega)
  have seventh : L.mul (U-p) a=U-2 := (add _ (by omega) up (by change U-p+(p-2)<_; omega)).trans
    (by change U-p+(p-2)=U-2; omega)
  have next (b : Nat) : L.mul g (b+1)=L.mul (L.mul g b) a := by rw [L.row_recurrence,ga]
  have e0 : L.mul g 0=0 := L.mul_zero g
  have e1 : L.mul g 1=a := by rw [L.mul_one,ga,Nat.mod_eq_of_lt (show a<2^(s+1) by omega)]
  have e2 : L.mul g 2=V := by rw [next 1,e1,square]
  have e3 : L.mul g 3=Z-2 := by rw [next 2,e2,vadd]
  have e4 : L.mul g 4=K := by rw [next 3,e3]; exact four
  have e5 : L.mul g 5=K+a := by rw [next 4,e4,ka]
  have e6 : L.mul g 6=U-p := by rw [next 5,e5,sixth]
  have e7 : L.mul g 7=U-2 := by rw [next 6,e6,seventh]
  change L.mul g y=_
  have ys : y=0 ∨ y=1 ∨ y=2 ∨ y=3 ∨ y=4 ∨ y=5 ∨ y=6 ∨ y=7 := by omega
  rcases ys with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [e0,e1,e2,e3,e4,e5,e6,e7,intervalWord,Nat.reduceAdd,Nat.reduceMod,Nat.reduceDiv,
      f0,f1,f2,f3,Nat.pow_one,if_pos,if_neg,if_false,if_true,Nat.one_ne_zero,Nat.zero_add,Nat.add_zero]
    <;> dsimp only [K,V,a,p,Z,U] at * <;> omega

def CubicPrefix : Prop := ∀ y, y<8 →
  (tables seedDegree).mul geometricRow y=intervalWord (fun i : Nat => 256^i) 0 3 y

private theorem addition_for_seed {u d : Nat} (wide : WidePeriodEstimates u) (limit : d≤u+1) :
    ∀ A, 0<A → 2^256∣A → A+(2^256-2)<2^d → (tables d).mul A (2^256-2)=A+(2^256-2) :=
  fun _ pos dv fits => wide_add_projection wide limit dv pos (by decide : 0<2^256-2) (Nat.le_refl _) fits

private theorem fourth_product {n q s : Nat} (np : 0<n) (qp : 0<q) (scale : n*q=s)
    (stretch : StretchWithTop q n) : (tables (s+1)).mul (2^q-2) (2^n-2)=2^s-2^q := by
  subst s
  have pos := Nat.two_pow_pos n
  exact ((capped_stretch_row qp np stretch).1 _ (show 2^n-2<2^n by omega)).trans (repeatBits_penultimate q n np)

private theorem second_product {n q d : Nat} (scale : n*n=q)
    (square : (tables d).mul (2^n-2) (2^n-2)=2^(n*n)-2^n) :
    (tables d).mul (2^n-2) (2^n-2)=2^q-2^n := scale ▸ square

private theorem concrete_second (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) :
    (tables (256^3+1)).mul (2^256-2) (2^256-2)=2^(256^2)-2^256 := by
  have h := square_at_cubic_degree H wide
  unfold CubicSquare seedDegree at h
  exact second_product (n:=256) (q:=256^2) (d:=256^3+1) (by decide) h

theorem cubic_prefix (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) : CubicPrefix := by
  have law : FiniteBlockLaw := finite_block_of_restore Backward.finite_restoration
  have limit : 256^3+1≤targetIndex+1 := Nat.succ_le_succ (targetIndex_eq.symm ▸
    Nat.pow_le_pow_right (by decide : 0<256) (by decide : 3≤256))
  unfold CubicPrefix seedDegree geometricRow
  intro y fit
  refine seven_from_two_products tables (f:=fun i : Nat => 256^i) (n:=256) (q:=256^2) (s:=256^3)
    (by decide) (by decide) (by decide) ?_ ?_ ?_ rfl rfl rfl rfl y fit
  · exact concrete_second H wide
  · exact fourth_product (n:=256) (q:=256^2) (s:=256^3) (by decide) (by decide) (by decide)
      (all_width_caps H law 2 (by decide)).2
  · exact addition_for_seed (u:=targetIndex) (d:=256^3+1) wide limit

#print axioms cubic_prefix
end Gamma11
