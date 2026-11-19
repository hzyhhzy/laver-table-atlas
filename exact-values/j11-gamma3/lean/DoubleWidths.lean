import NativeStretch

/-! Repeated squaring of a width transports its crossing triples by
the native repeated-digit row. The final interval is covered by
ordinary dyadic triples, and the induction starts at width two. -/
set_option autoImplicit false
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

def AllUpperBridges (n : Nat) : Prop := ∀ m, n<m → UpperBridges tables m n

private theorem input_before_cap {m a b k : Nat} (value : act tables m a b=k) (fit : k<m) : b≤k := by
  by_cases small : b≤m
  · exact value ▸ le_act tables m a b small
  · have hit := Nat.le_trans (le_act tables m a m (Nat.le_refl _)) (act_mono tables m a (by omega : m≤b))
    rw [value] at hit; omega

private theorem square_bridges (H : FirstRowUnbounded) (law : FiniteBlockLaw) {n : Nat}
    (dyadic : IsDyadic n) (width : 2≤n) (old : AllUpperBridges n) : AllUpperBridges (n*n) := by
  intro m room r start stop
  have pos : 0<n := by omega
  have nn := Nat.mul_le_mul_left n width
  rw [Nat.mul_two] at nn
  have br := old (n*n+1) (by omega)
  let L := 2^n-2
  have stretch (i : Nat) (bound : i≤n) : act tables m L i=i*n :=
    native_stretch_actions H law dyadic width br room bound
  by_cases first : r≤n
  · have sig : signature m L=1 := dyadic_tail_signature m n 1 (by omega) (by omega)
    exact ⟨1,n,L,Nat.le_refl _,start,first,sig,(stretch 1 (by omega)).trans (Nat.one_mul _),stretch n (Nat.le_refl _)⟩
  by_cases last : n*n-n<r
  · obtain ⟨e,eqv⟩ := dyadic
    have ep : 0<e := by
      apply Nat.pos_of_ne_zero
      intro zero
      rw [zero] at eqv; omega
    have es : e-1+1=e := Nat.sub_add_cancel ep
    have square : 2^(e+e)=n*n := by rw [Nat.pow_add,← eqv]
    have last' : n*n-2^((e-1)+1)<r := by rw [es,← eqv]; exact last
    obtain ⟨i,ie,l,u⟩ := dyadic_interval (n:=n*n) (e-1) last' stop
    have next := Nat.pow_le_pow_right (by decide : 0<2) (show i+1≤e by omega)
    rw [← eqv] at next
    obtain ⟨c,data⟩ := dyadic_anchors tables (e+e) m (square ▸ room) i (by omega)
    rw [square] at data
    exact ⟨_,_,c,by omega,l,u,data⟩
  · let j := (r-1)/n+1
    have left : (r-1)/n*n≤r-1 := Nat.div_mul_le_self .. 
    have right : r-1<j*n := (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self _)
    have pre := Nat.succ_mul (n-1) n
    rw [show (n-1).succ=n by omega] at pre
    have jm : (r-1)/n<n-1 := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
    have jn : j<n := by dsimp [j]; omega
    have jp : 1<j := by
      apply Nat.lt_of_not_ge; intro nope
      have small := Nat.mul_le_mul_right n nope
      rw [Nat.one_mul] at small
      omega
    obtain ⟨α,β,c,ap,al,bu,sig,ab,bn⟩ := old m (by omega) j jp jn
    have beta := input_before_cap bn (by omega : n<m)
    have zs := signature_mul tables m L c
    have z1 := act_application tables m L c α
    have z2 := act_application tables m L c β
    rw [sig,stretch α (by omega)] at zs
    rw [ab,stretch α (by omega),stretch β beta] at z1
    rw [bn,stretch β beta,stretch n (Nat.le_refl _)] at z2
    have aFits : α≤(r-1)/n := by change α<(r-1)/n+1 at al; omega
    have aBound := Nat.mul_le_mul_right n aFits
    have bBound := Nat.mul_le_mul_right n bu
    exact ⟨α*n,β*n,_,Nat.mul_pos ap pos,by omega,by omega,zs,z1,z2⟩

theorem double_width_bridges (H : FirstRowUnbounded) (law : FiniteBlockLaw) (e : Nat) :
    AllUpperBridges (2^(2^e)) := by
  induction e with
  | zero => intro m _ r lo hi; change r<2 at hi; omega
  | succ e ih =>
    let n := 2^(2^e)
    have np : 2≤n := Nat.pow_le_pow_right (by decide : 0<2) (Nat.two_pow_pos e)
    have eqv : 2^(2^(e+1))=n*n := by
      rw [Nat.pow_succ 2 e,Nat.mul_two,Nat.pow_add]
    rw [eqv]
    exact square_bridges H law ⟨2^e,rfl⟩ np ih

private theorem parameter_width (e : Nat) : 256^(2^e)=2^(2^(e+3)) := by
  rw [show 256=2^8 by decide,← Nat.pow_mul,Nat.pow_add 2 e 3,Nat.mul_comm 8]

theorem auxiliary_stretches_from_blocks (H : FirstRowUnbounded) (law : FiniteBlockLaw) : AuxiliaryStretches := by
  rintro b ⟨e,rfl⟩ k fit
  rw [parameter_width] at fit ⊢
  let n := 2^(2^(e+3))
  have np : 2≤n := Nat.pow_le_pow_right (by decide : 0<2) (Nat.two_pow_pos (e+3))
  have space := Nat.mul_le_mul_left n np
  rw [Nat.mul_two] at space
  exact native_stretch_hom H law ⟨_,rfl⟩ np (double_width_bridges H law (e+3) (n*n+1) (by omega)) fit

theorem special_last_image (H : FirstRowUnbounded) (law : FiniteBlockLaw) (e : Nat) :
    let n := 2^(2^e)
    image H (2^n-2) n=n*n := by
  let n := 2^(2^e)
  have np : 2≤n := Nat.pow_le_pow_right (by decide : 0<2) (Nat.two_pow_pos e)
  have sq := Nat.mul_le_mul_left n np
  rw [Nat.mul_two] at sq
  have br := double_width_bridges H law e (n*n+1) (by omega)
  have value := native_stretch_actions H law (show IsDyadic n from ⟨_,rfl⟩) np br
    (Nat.lt_succ_self (n*n)) (Nat.le_refl n)
  rw [numeral_cap_eq_min H] at value
  change image H (2^n-2) n=n*n
  omega

theorem sixteen_data_from_blocks (H : FirstRowUnbounded) (law : FiniteBlockLaw) : SixteenRowData := by
  have br := double_width_bridges H law 1 17 (by decide)
  have four := native_stretch_actions (n:=4) (m:=257) (i:=4) H law
    (show IsDyadic 4 from ⟨2,rfl⟩) (by decide) br (by decide) (Nat.le_refl 4)
  exact sixteen_data_from_crossings H law four

#print axioms double_width_bridges
#print axioms auxiliary_stretches_from_blocks
#print axioms special_last_image
#print axioms sixteen_data_from_blocks
end Gamma11
