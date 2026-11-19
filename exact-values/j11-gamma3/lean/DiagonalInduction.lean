import DiagonalDigits
import GeometricCarry

/-! Each intermediate table degree is determined by the preceding one.
The argument uses the old row only at smaller degrees. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable TableElement

private theorem signature_run_mod {a b t : Nat} (low : a<t) (rises : a<b) :
    signature t ((2^b-2^a)%2^t)=a := by
  have pos := Nat.two_pow_pos a
  have growing := Nat.pow_lt_pow_right (by decide : 1<2) rises
  by_cases fits : b≤t
  · have up := Nat.pow_le_pow_right (by decide : 0<2) fits
    rw [Nat.mod_eq_of_lt (show 2^b-2^a<2^t by omega)]
    exact dyadic_tail_signature t b a rises fits
  · have aq := Nat.pow_lt_pow_right (by decide : 1<2) rises
    have cut := Nat.pow_lt_pow_right (by decide : 1<2) low
    have eqv := Backward.unique_inverse (d:=t) (x:=2^a) (y:=(2^b-2^a)%2^t)
      (Nat.mod_lt _ (Nat.two_pow_pos _)) (by
        rw [Nat.add_mod_mod,show 2^a+(2^b-2^a)=2^b by omega]
        exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega)))
    rw [eqv,Backward.neg_small pos cut]; exact dyadic_tail_signature t t a low (Nat.le_refl _)

theorem prior_geometric_image (H : FirstRowUnbounded) {t k : Nat} (old : GeometricAt t)
    (source : k<256) (visible : 256^k<t) : image H geometricRow k=256^k := by
  have fits := Nat.pow_lt_pow_right (by decide : 1<2) source
  have row := old (2^k)
  rw [Nat.mod_eq_of_lt fits,diagonalWord,intervalWord_single _ _ _ _ source] at row
  simp only [Nat.zero_add] at row
  have actual : act tables t geometricRow k=256^k := by
    rw [act,row]; exact signature_run_mod visible (Nat.pow_lt_pow_succ (by decide))
  rw [numeral_cap_eq_min H] at actual; omega

theorem prior_geometric_period (H : FirstRowUnbounded) {t k : Nat} (old : GeometricAt t)
    (degree : 257≤t) (source : k<256) (visible : 256^k<t) (endAt : t≤256^(k+1)) :
    (tables t).FirstZero geometricRow (2^(k+1)) := by
  have idx := prior_geometric_image H old source visible
  apply first_zero_from_half tables (geometric_row_zero tables t 256 (k+1) (by decide) degree endAt)
  intro zero
  have high := (numeral_zero_iff H geometricRow t k).mp ((canonical_mul ..).symm.trans zero)
  change t≤image H geometricRow k at high; omega

private theorem odd_ends_at {t k r : Nat} (old : GeometricAt t) (kt : 256^k≤t)
    (kn : k≤256) (odd : r%2=1) (fit : r+1<2^k) : Nonempty (OddColumnEndpoints t r) := by
  let f := fun i : Nat => 256^i
  have mono (a b : Nat) (le : a≤b) : f a≤f b := Nat.pow_le_pow_right (by decide) le
  obtain ⟨m,D,mk,positive,aligned,prev,next⟩ := intervalWord_carry f mono 0 k r fit
  simp only [Nat.zero_add] at aligned prev next
  have scale : f (m+1)=256*256^m := by dsimp [f]; rw [Nat.pow_succ,Nat.mul_comm]
  rw [scale] at aligned next
  have win : 256*256^m≤t := Nat.le_trans (scale ▸ mono (m+1) k mk) kt
  refine ⟨⟨m,positive odd,D,win,aligned,?_,?_⟩⟩
  · exact (geometric_untruncated old kt kn (show r<2^k by omega)).trans prev
  · rw [show geometricRow+1=2^256-2 by decide,repeatBits_penultimate _ _ (by decide : 0<256)]
    exact (geometric_untruncated old kt kn fit).trans next

private theorem even_ends_at {t k r : Nat} (old : GeometricAt t) (kt : 256^k≤t)
    (kn : k≤256) (even : r%2=0) (fit : r+1<2^k) :
    2^256∣oldEntry t geometricRow r ∧ oldEntry t geometricRow (r+1)=oldEntry t geometricRow r+(geometricRow+1) := by
  cases k with
  | zero => simp at fit
  | succ k =>
    let f := fun i : Nat => 256^i
    have dv := intervalWord_dvd f (fun _ _ => Nat.pow_le_pow_right (by decide)) 1 k (r/2)
    have odd : (r+1)%2≠0 := by omega
    have eqv : (r+1)/2=r/2 := by omega
    rw [geometric_untruncated old kt kn (show r<2^(k+1) by omega),geometric_untruncated old kt kn fit,
      intervalWord,if_pos even,Nat.zero_add,intervalWord,if_neg odd,eqv]
    exact ⟨dv,Nat.add_comm ..⟩

theorem protect_geometric_prefix (H : FirstRowUnbounded) (wide : WidePeriodEstimates targetIndex)
    {t h k : Nat} (old : GeometricAt t) (degree : 257≤t) (top : t≤targetIndex)
    (hMin : 4≤h) (hMax : h≤256) (visible : 256^(h-1)<t) (endAt : t≤256^h)
    (kn : k≤256) (tk : 256^k≤t) (y : Nat) (win : y<2^k) (stop : y≤2^(h-1)) :
    (tables (t+1)).mul geometricRow y=(tables t).mul geometricRow y := by
  have lower := prior_geometric_image H old (k:=h-1) (by omega) visible
  have bound := Nat.pow_le_pow_right (by decide : 0<256) (show h-1≤256 by omega)
  have img : image H geometricRow (h-1)≤targetIndex := by rw [lower,targetIndex_eq]; exact bound
  have seq := prior_geometric_period H old degree (k:=h-1) (by omega) visible
    (by rwa [Nat.sub_add_cancel (show 1≤h by omega)])
  induction y with
  | zero => rw [(tables _).mul_zero,(tables _).mul_zero]
  | succ r ih =>
    have prev := ih (by omega) (by omega)
    rw [(tables (t+1)).row_recurrence,prev]
    by_cases first : r=0
    · subst r; rw [(tables t).mul_zero,(tables (t+1)).zero_mul,(tables t).mul_one]
      have base : geometricRow+1<2^256 := by decide
      have limit := Nat.pow_le_pow_right (by decide : 0<2) (show 256≤t by omega)
      have strict := Nat.pow_lt_pow_succ (n:=t) (by decide : 1<2)
      rw [Nat.mod_eq_of_lt (by omega : geometricRow+1<2^(t+1)),Nat.mod_eq_of_lt (by omega : geometricRow+1<2^t)]
    · have rp := Nat.pos_of_ne_zero first
      by_cases even : r%2=0
      · obtain ⟨div,next⟩ := even_ends_at old tk kn even win
        have below := Nat.pow_lt_pow_succ (n:=h-1) (by decide : 1<2)
        have positive := Nat.pos_of_ne_zero (seq.2.2 r rp (by omega))
        exact protected_even_at_height wide top positive ((tables t).mul_lt ..) div next
      · have odd : r%2=1 := by omega
        obtain ⟨ends⟩ := odd_ends_at old tk kn odd win
        exact protected_odd_at_height H wide hMin hMax degree endAt img rp odd (by omega) ends

#print axioms protect_geometric_prefix
end Gamma11
