import RankSmallSections
import RankComposition
import ManuscriptEndpoint

/-! Dougherty II (8.3) and (8.4) for ordinary sets in the rank model.
The arithmetic inputs are first-row growth and the finite, right-endpoint
case of Lemma 6.3. The same proof works for every set below delta_4. -/

set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement
variable {height : Ordinal.{u}}

theorem native_image_of_index {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    {a : Nat} (pos : 0<a) (x : Nat) :
    ordinalImage (powerEmb hj.1 j a) (dyadicPoint hj x) = dyadicPoint hj (image H a x) := by
  apply native_read_act hj (m:=image H a x+1) pos _ (Nat.lt_succ_self _)
  rw [numeral_cap_eq_min H,Nat.min_eq_right (Nat.le_succ _)]

private theorem power_reduction {j : Emb height} (hj : IsWitness j) (m a : Nat) :
    TraceEq (dyadicPoint hj m) (powerEmb hj.1 j a) (powerEmb hj.1 j (a%2^m)) := by
  cases a with
  | zero => rw [Nat.zero_mod]
  | succ a =>
    change TraceEq _ ((Word.power a).embedding hj.1 j) _
    simpa only [Word.residue_power] using dyadic_trace hj (Word.power a) m

private theorem power_composition {j : Emb height} (hj : IsWitness j) (m a b : Nat) :
    TraceEq (dyadicPoint hj m) ((powerEmb hj.1 j a).comp (powerEmb hj.1 j b))
      (powerEmb hj.1 j ((tables m).comp a b)) := by
  cases a with
  | zero => rw [(tables m).zero_comp]; exact power_reduction hj m b
  | succ a =>
    cases b with
    | zero => rw [(tables m).comp_zero]; exact power_reduction hj m (a+1)
    | succ b =>
      change TraceEq _ (((Word.power a).embedding hj.1 j).comp ((Word.power b).embedding hj.1 j)) _
      simpa only [Word.residue_power,(tables m).comp_mod_left,(tables m).comp_mod_right] using
        word_composition_trace hj m (Word.power a) (Word.power b)

private theorem fixes_dyadic_rank {j : Emb height} (hj : IsWitness j) {X n : Nat} (div : 2^n ∣ X)
    {x : Rank height} (small : x.val.rank < (dyadicPoint hj n).val) : powerEmb hj.1 j X x = x := by
  have tr := power_reduction hj n X
  rw [Nat.mod_eq_zero_of_dvd div] at tr
  exact fixes_set_below hj.1 _ _ ((trace_identity_iff hj.1 _ _).mp tr) x small

theorem block_action_8_3 {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {X p : Nat} (aligned : 4 ∣ p) (div : 2^p ∣ X)
    (x : Rank height) (small : x.val.rank < (dyadicPoint hj 4).val) :
    powerEmb hj.1 j (X+2^p-1) x = powerEmb hj.1 j X (powerEmb hj.1 j (2^p-1) x) := by
  let r := X+2^p-1
  by_cases zero : r=0
  · have pp := Nat.two_pow_pos p
    have xz : X=0 := by dsimp [r] at zero; omega
    subst X; rw [Nat.zero_add]; rfl
  let z := image H r 4
  let R := powerEmb hj.1 j r
  have read : ordinalImage R (dyadicPoint hj 4) = dyadicPoint hj z :=
    native_image_of_index hj H (Nat.pos_of_ne_zero zero) 4
  have long : dyadicPoint hj 4 ≤ dyadicPoint hj z := read ▸ (ordinalImage_strictMono R).le_apply
  have seen : (R x).val.rank < (dyadicPoint hj z).val := by
    rw [map_set_rank hj.1 R x,← read]
    exact (ordinalImage_strictMono R) (show (⟨x.val.rank,x.property⟩ : Below height)<dyadicPoint hj 4 from small)
  have cap := ((finite_block_iff_boundary H).mp law (w:=4) (p:=p) (X:=X) (d:=z)
    ⟨2,rfl⟩ aligned div (Nat.le_refl _)).2
  change (tables z).comp (X%2^z) ((2^p-1)%2^z) = r%2^z at cap
  rw [(tables z).comp_mod_left,(tables z).comp_mod_right] at cap
  have tr := power_composition hj z X (2^p-1)
  rw [cap] at tr
  exact ((power_reduction hj z r).trans tr.symm).read_set hj.1 (small.trans_le long) seen

theorem block_action_8_4 {j : Emb height} (hj : IsWitness j) (H : FirstRowUnbounded)
    (law : FiniteBlockLaw) {X p : Nat} (aligned : 4 ∣ p) (div : 2^(p+4) ∣ X)
    (x : Rank height) (small : x.val.rank < (dyadicPoint hj 4).val) :
    powerEmb hj.1 j (X+2^p-1) x = powerEmb hj.1 j (2^p-1) x := by
  rw [block_action_8_3 hj H law aligned ((Nat.pow_dvd_pow 2 (Nat.le_add_right p 4)).trans div) x small]
  apply fixes_dyadic_rank hj div
  by_cases empty : p=0
  · subst p; exact small
  have ones := ones_shift_of_boundary H ((finite_block_iff_boundary H).mp law)
    (w:=4) (p:=p) ⟨2,rfl⟩ aligned
  have pp := Nat.one_lt_two_pow empty
  have reach := (native_image_of_index hj H (a:=2^p-1) (by omega) 4).trans
    (congrArg (dyadicPoint hj) ones)
  rw [map_set_rank hj.1,← reach]
  exact (ordinalImage_strictMono _) (show (⟨x.val.rank,x.property⟩ : Below height)<dyadicPoint hj 4 from small)

#print axioms block_action_8_3
#print axioms block_action_8_4
end Gamma11.RankI3
