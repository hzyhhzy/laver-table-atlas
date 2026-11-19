import RankEarlySource
import WidePeriods

/-! At the actual target degree the same three mathematical inputs as
in B.3 suffice for the strict bounds of Appendix C, including arbitrary
representatives of rows and the old degree boundary. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def MovedBelow256 (m : Nat) : Prop := ∀ r e, 16≤r → r<256 → signature m e=r →
  256≤act tables m e r → act tables m e 256=m

private theorem at_arbitrary_degree {t : Nat} (scale : t=256^256) (stretch : SixteenRowData)
    (prefixes : AdditionPrefix16 (t+1)) (four : act tables (t+1) 14 4=16)
    (thirteen : act tables (t+1) 13 4≤256) (source : entry (t+1) 13 3=65534) :
    MovedBelow256 (t+1) := by
  let d := t+1
  have room : 272≤d := by dsimp [d]; rw [scale]; decide
  have roomN : 256≤d := by omega
  have pr := (tables d).projection (tables 256) (Nat.pow_dvd_pow 2 roomN) 13 3
  have sourceN : (tables 256).mul 13 3=65534 := by
    rw [← pr,canonical_mul,source]
  apply critical_sixteen_to_255 room stretch four
  intro a sig jump
  let e := a%2^d
  have fit : e<2^d := Nat.mod_lt a (Nat.two_pow_pos _)
  have actEq (i : Nat) : act tables d e i=act tables d a i :=
    congrArg (signature d) ((tables d).mul_mod_left a (2^i))
  have es : signature d e=16 := (signature_mod_eq (Nat.mod_mod a (2^d))).trans sig
  have ej : 256≤act tables d e 16 := (actEq 16).symm ▸ jump
  have addM := prefixes e fit es ej 65519 (by decide)
  exact (actEq 256).symm.trans (critical_sixteen scale stretch sourceN thirteen fit es ej addM)

theorem appendix_C2 {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) (h16 : SixteenRowData) :
    MovedBelow256 (targetIndex+1) :=
  at_arbitrary_degree targetIndex_eq h16 (appendix_B3 hj H law h16)
    (fourteen_at_target hj H law) (thirteen_four_target_bound hj H law h16) (two_target_constants hj H law).2

#print axioms appendix_C2

private theorem wide_from_small {t : Nat} (scale : t=256^256) (hom : SixteenRowData)
    (four : act tables (t+1) 14 4=16) (two : act tables (t+1) 13 2=16) (src : act tables (t+1) 13 4≤256)
    (small : ∀ {r a}, 4≤r → r<16 → signature (t+1) a=r → 256≤act tables (t+1) a r → act tables (t+1) a 256=t+1)
    (wide : MovedBelow256 (t+1)) : WidePeriodEstimates t := by
  apply periods_from_equality_case (by rw [scale]; decide)
  intro a lo hi vis
  exact visible_wide scale hom four two src (fun r row minR maxR sig first => by
    by_cases h : r<16
    · exact small minR h sig first
    · exact wide r row (by omega) maxR sig first) lo hi vis

theorem thirteen_two_at_target {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) : act tables (targetIndex+1) 13 2=16 := by
  have idx := (dyadicPoint_strict hj).injective
    ((native_image_of_index hj H (a:=13) (by decide) 2).symm.trans (thirteen_second_image hj H law))
  have cap : 16≤targetIndex := Nat.pow_le_pow_right (by decide : 0<2) (by decide : 4≤2048)
  rw [numeral_cap_eq_min H,idx,Nat.min_eq_right (Nat.le_trans cap (Nat.le_succ _))]

theorem appendix_E {height : Ordinal.{u}} {j : Emb height} (hj : IsWitness j)
    (H : FirstRowUnbounded) (law : FiniteBlockLaw) (h16 : SixteenRowData) :
    WidePeriodEstimates targetIndex := by
  exact wide_from_small targetIndex_eq h16 (fourteen_at_target hj H law) (thirteen_two_at_target hj H law)
    (thirteen_four_target_bound hj H law h16)
    (@full_small_critical_bound _ _ hj H law h16) (appendix_C2 hj H law h16)

#print axioms appendix_E
end Gamma11.RankI3
