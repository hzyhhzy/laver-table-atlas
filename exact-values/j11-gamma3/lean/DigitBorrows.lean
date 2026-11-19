import BackwardRows
import BackwardShift

/-! A whole reversed full block is equivalent to the two predecessor
rules, with and without a borrow. The descending induction starts at
an explicitly chosen common zero. -/
set_option autoImplicit false
namespace Gamma11.Backward

def DigitRow (X z b : Nat) : Prop := ∀ i r, r<2^b →
  mul (X+2^z*(2^b-1)+1) (2^b*i+r) = mul (X+1) i+2^z*r

def InnerPredecessor (X z b : Nat) : Prop := ∀ i r, r+1<2^b →
  mul (mul (X+1) i+2^z*(r+1)) (X+2^z*(2^b-1))=mul (X+1) i+2^z*r

def BoundaryPredecessor (X z b : Nat) : Prop := ∀ i,
  mul (mul (X+1) (i+1)) (X+2^z*(2^b-1))=mul (X+1) i+2^z*(2^b-1)

private def predicted (X z b y : Nat) := mul (X+1) (y/2^b)+2^z*(y%2^b)

private theorem predicted_digit {X z b i r : Nat} (fit : r<2^b) :
    predicted X z b (2^b*i+r)=mul (X+1) i+2^z*r := by
  rw [predicted,Nat.mul_add_div (Nat.two_pow_pos b),Nat.div_eq_of_lt fit,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt fit]
  rfl

private theorem predicted_previous {X z b : Nat} (inner : InnerPredecessor X z b)
    (boundary : BoundaryPredecessor X z b) (y : Nat) :
    predicted X z b y=mul (predicted X z b (y+1)) (X+2^z*(2^b-1)) := by
  let p := 2^b
  let i := y/p
  let r := y%p
  have pPos : 0<p := Nat.two_pow_pos b
  have lo : r<p := Nat.mod_lt _ pPos
  have dec : p*i+r=y := Nat.div_add_mod y p
  by_cases inside : r+1<p
  · have next : p*i+(r+1)=y+1 := by omega
    rw [← dec,predicted_digit lo,dec,← next,predicted_digit inside]
    exact (inner i r inside).symm
  · have last : r=p-1 := by omega
    have succEq : p*(i+1)+0=y+1 := by rw [Nat.mul_succ]; omega
    rw [← dec,predicted_digit lo,dec,← succEq,predicted_digit pPos,Nat.mul_zero,Nat.add_zero,last]
    exact (boundary i).symm

theorem digit_row_iff_predecessors (X z b : Nat) :
    DigitRow X z b ↔ InnerPredecessor X z b ∧ BoundaryPredecessor X z b := by
  let p := 2^b
  let a := X+2^z*(p-1)
  have pPos : 0<p := Nat.two_pow_pos b
  constructor
  · intro formula
    constructor
    · intro i r fit
      have prev := previous_column a (p*i+r)
      have same : p*i+r+1=p*i+(r+1) := Nat.add_assoc .. 
      rw [same,formula _ _ fit,formula _ _ (by omega : r<p)] at prev
      exact prev.symm
    · intro i
      have prev := previous_column a (p*i+(p-1))
      have same : p*i+(p-1)+1=p*(i+1)+0 := by rw [Nat.mul_succ]; omega
      rw [same,formula _ _ pPos,Nat.mul_zero,Nat.add_zero,formula _ _ (by omega : p-1<p)] at prev
      exact prev.symm
  · rintro ⟨inner,boundary⟩ i r rf
    let y := p*i+r
    let h := a+X+y+2
    let K := p*2^h
    have bound : h<2^h := Nat.lt_two_pow_self
    have larger : 2^h≤K := Nat.le_mul_of_pos_left _ pPos
    have aSmall : a+1≤h := by dsimp only [h]; omega
    have xSmall : X+1≤h := by dsimp only [h]; omega
    have ySmall : y≤h := by dsimp only [h]; omega
    have top : mul (a+1) K=0 := by
      change mul (a+1) (2^b*2^h)=0
      rw [← Nat.pow_add]; apply zero_at_width (Nat.zero_lt_succ _)
      rw [Nat.pow_add]; exact Nat.le_trans aSmall (Nat.le_trans (Nat.le_of_lt bound) larger)
    have base : mul (X+1) (2^h)=0 := zero_at_width (Nat.zero_lt_succ _) (Nat.le_trans xSmall (Nat.le_of_lt bound))
    have predTop : predicted X z b K=0 := by
      have form := predicted_digit (X:=X) (z:=z) (i:=2^h) (r:=0) pPos
      rw [Nat.add_zero,base,Nat.mul_zero,Nat.add_zero] at form
      exact form
    have descend (n : Nat) (fit : n≤K) : mul (a+1) (K-n)=predicted X z b (K-n) := by
      induction n with
      | zero => simpa using top.trans predTop.symm
      | succ n ih =>
        have inc : K-(n+1)+1=K-n := by omega
        have actual := previous_column a (K-(n+1))
        have expected := predicted_previous inner boundary (K-(n+1))
        rw [inc,ih (by omega)] at actual
        rw [inc] at expected
        exact actual.trans expected.symm
    have space : y≤K := Nat.le_trans ySmall (Nat.le_trans (Nat.le_of_lt bound) larger)
    have reached := descend (K-y) (Nat.sub_le _ _)
    rw [show K-(K-y)=y by omega] at reached
    exact reached.trans (predicted_digit rf)

#print axioms digit_row_iff_predecessors
end Gamma11.Backward
