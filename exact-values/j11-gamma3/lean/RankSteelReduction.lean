import RankSteelBridge
import LaverTables.Algebra.Iterates

/-! The constant application chain from Steel is the sequence of
positive left powers. Its critical points cross every generator image
of a dyadic critical point, which supplies first-row unboundedness. -/
set_option autoImplicit false
universe u
namespace Gamma11.RankI3
open TableElement
variable {height : Ordinal.{u}} {j : Emb height}

private theorem power_is_dyadic (hj : IsWitness j) (n : Nat) :
    ∃ i, IsCritical (graphOf (powerEmb hj.1 j (n+1))) (dyadicPoint hj i) := by
  let w := Word.power n
  have bound (m : Nat) : m<2^m := by
    induction m with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos m; omega
  have nz : w.residue (n+1)≠0 := by
    rw [Word.residue_power,Nat.mod_eq_of_lt (bound (n+1))]; omega
  obtain ⟨i,_,hit⟩ := w.first_nonzero nz
  refine ⟨i,?_⟩
  rw [powerEmb_graph,←Word.realize_power]
  exact word_at_first_nonzero hj (dyadicPoint_strict hj) w i hit

private theorem chain_eq_power (hj : IsWitness j) (n : Nat) :
    LaverTables.appChain (fun _ => asSteelFn j) n=asSteelFn (powerEmb hj.1 j (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LaverTables.appChain,ih,steel_app_eq hj.1,apply_generator]

theorem first_row_of_steel_crossings (hj : IsWitness j)
    (cross : ∀ b, LaverTables.IterMem (asSteelFn j) b → ∃ n,
      LaverTables.critOf b<LaverTables.critOf (LaverTables.appChain (fun _ => asSteelFn j) n)) :
    FirstRowUnbounded := by
  intro x
  let c := fun _ : Nat => asSteelFn j
  have gen (n : Nat) : LaverTables.IterMem (asSteelFn j) (c n) := LaverTables.IterMem.base
  let b := powerEmb hj.1 j (2^x)
  let θ := ordinalImage j (dyadicPoint hj x)
  have pos := Nat.two_pow_pos x
  have wb : LaverTables.IterMem (asSteelFn j) (asSteelFn b) := by
    have hc := LaverTables.IterMem.appChain gen (2^x-1)
    change LaverTables.IterMem (asSteelFn j) (LaverTables.appChain (fun _ => asSteelFn j) (2^x-1)) at hc
    rwa [chain_eq_power hj,Nat.sub_add_cancel pos] at hc
  have wa := LaverTables.IterMem.app (LaverTables.IterMem.base (j:=asSteelFn j)) wb
  rw [steel_app_eq hj.1] at wa
  have isθ : IsCritical (graphOf (applyEmb hj.1 j b)) θ := applyEmb_critical hj.1 j b (dyadicPoint_critical hj x)
  obtain ⟨n,greater⟩ := cross _ wa
  obtain ⟨i,hi⟩ := power_is_dyadic hj n
  rw [steel_critical_eq _ isθ,chain_eq_power hj,steel_critical_eq _ hi] at greater
  refine ⟨i,fun zero => greater.not_ge ?_⟩
  exact (native_cut hj (by decide : 0<1) x i).mp zero

#print axioms first_row_of_steel_crossings
end Gamma11.RankI3
