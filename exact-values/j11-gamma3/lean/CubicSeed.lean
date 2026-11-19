import CubicPrefix

/-! At exact degree 256^3 the first eight columns already describe
the entire row. At the next degree its midpoint 4 stays below the
cut, which forces the doubled period and determines the new bit. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 16777217
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem seed_from_prefix {n s g : Nat} (F : BinaryFamily)
    (sEq : s=n^3) (many : 3≤n)
    (zero : (F s).mul g 8=0)
    (entries : ∀ y, y<8 → (F (s+1)).mul g y=intervalWord (fun i => n^i) 0 3 y) :
    ∀ y, (F s).mul g y=diagonalWord n (y%2^n)%2^s := by
  let f := fun i : Nat => n^i
  have mono (i j : Nat) (ij : i≤j) : f i≤f j := Nat.pow_le_pow_right (by omega) ij
  intro y
  have small : y%8<8 := Nat.mod_lt _ (by decide)
  have low := entries (y%8) small
  have bound := intervalWord_bound mono 0 3 (y%8)
  change intervalWord f 0 3 (y%8)+2≤2^(n^3) at bound
  rw [←sEq] at bound
  have pr := (F (s+1)).projection (F s) (Nat.pow_dvd_pow 2 (Nat.le_succ _)) g (y%8)
  change (F (s+1)).mul g (y%8)=intervalWord f 0 3 (y%8) at low
  rw [low,Nat.mod_eq_of_lt (show intervalWord f 0 3 (y%8)<2^s by omega)] at pr
  have cut := intervalWord_cut mono 0 3 n (y%2^n) many
  change diagonalWord n (y%2^n)%2^(n^3)=intervalWord f 0 3 ((y%2^n)%8) at cut
  rw [←sEq,Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 many)] at cut
  exact ((F s).reduce_period zero y).trans (pr.symm.trans cut.symm)

theorem geometric_cubic_seed (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) :
    GeometricAt seedDegree := by
  let s := 256^3
  have more : 257≤s := by decide
  have pref := cubic_prefix H wide
  have zero := geometric_row_zero tables s 256 3 (by decide) more (Nat.le_refl _)
  have old : GeometricAt s := seed_from_prefix (n:=256) tables rfl (by decide) zero pref
  have first := prior_geometric_period H old more (k:=2) (by decide) (by decide) (Nat.le_refl _)
  have middle := pref 4 (by decide)
  have known := geometric_untruncated (t:=s) (k:=3) (y:=4) old (Nat.le_refl _) (by decide) (by decide)
  change (tables s).mul geometricRow 4=_ at known
  have same : (tables (s+1)).mul geometricRow 4=(tables s).mul geometricRow 4 := middle.trans known.symm
  have nz := first.2.2 4 (by decide) (by decide)
  have mid : 0<(tables (s+1)).mul geometricRow 4 ∧ (tables (s+1)).mul geometricRow 4<2^s := by
    rw [same]; exact ⟨Nat.pos_of_ne_zero nz,(tables s).mul_lt ..⟩
  have lift := doubled_period_lift tables (by decide : 2≤s) first mid
  exact geometric_step_from_bit old lift (by decide) (Nat.le_refl _) (by decide)

theorem diagonal_from_first_row (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex) :
    DiagonalHomAt 256 targetIndex := diagonal_from_cubic_seed H wide (geometric_cubic_seed H wide)

#print axioms geometric_cubic_seed
#print axioms diagonal_from_first_row
end Gamma11
