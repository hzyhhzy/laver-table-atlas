import BinarySlices

/-! Fill a one-bit by a run between two successive marked positions.
    Unlike uniform stretching, the diagonal uses positions 256^i.
    Only ordinary homomorphisms at specified old degrees are inputs. -/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
namespace Gamma11
open LaverLowerBounds LaverLowerBounds.FiniteTable

def intervalWord (f : Nat → Nat) (s : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x => (if x%2=0 then 0 else 2^(f (s+1))-2^(f s)) + intervalWord f (s+1) n (x/2)

theorem intervalWord_zero (f : Nat → Nat) (s n : Nat) : intervalWord f s n 0 = 0 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [intervalWord, ih]

theorem intervalWord_one (f : Nat → Nat) (s n : Nat) (pos : 0 < n) :
    intervalWord f s n 1 = 2^(f (s+1))-2^(f s) := by
  cases n with
  | zero => omega
  | succ n => simp [intervalWord,intervalWord_zero]

theorem intervalWord_dvd (f : Nat → Nat) (mono : ∀ i j, i ≤ j → f i ≤ f j) (s n x : Nat) :
    2^(f s) ∣ intervalWord f s n x := by
  induction n generalizing s x with
  | zero => exact Nat.dvd_zero _
  | succ n ih =>
    have div := Nat.pow_dvd_pow 2 (mono s (s+1) (Nat.le_succ s))
    rw [intervalWord]
    apply Nat.dvd_add _ (Nat.dvd_trans div (ih (s+1) (x/2)))
    split
    · exact Nat.dvd_zero _
    · exact Nat.dvd_sub div (Nat.dvd_refl _)

/-- The ordinary binary carry for arbitrary increasing positions.
    All upper bits are a common multiple D of the cut following the carry. -/
theorem intervalWord_carry (f : Nat → Nat) (mono : ∀ i j, i ≤ j → f i ≤ f j)
    (s n x : Nat) (fits : x+1 < 2^n) :
    ∃ m D, m<n ∧ (x%2=1 → 0<m) ∧ 2^(f (s+m+1)) ∣ D ∧
      intervalWord f s n x = D+(2^(f (s+m))-2^(f s)) ∧
      intervalWord f s n (x+1) = D+(2^(f (s+m+1))-2^(f (s+m))) := by
  induction n generalizing s x with
  | zero => simp at fits
  | succ n ih =>
    let q := x/2
    by_cases even : x%2=0
    · refine ⟨0,intervalWord f (s+1) n q,by omega,by omega,intervalWord_dvd f mono _ _ _,?_,?_⟩
      · rw [intervalWord,if_pos even]; simp only [Nat.zero_add, Nat.add_zero, Nat.sub_self, q]
      · have odd : (x+1)%2≠0 := by omega
        have same : (x+1)/2=q := by dsimp [q]; omega
        rw [intervalWord,if_neg odd,same,Nat.add_comm]
        simp only [Nat.add_zero]
    · rw [Nat.pow_succ] at fits
      obtain ⟨m,D,mn,_,div,old,newVal⟩ := ih (s+1) q (by dsimp [q]; omega)
      have shift : s+(m+1)=s+1+m := by omega
      refine ⟨m+1,D,by omega,by omega,shift ▸ div,?_,?_⟩
      · have le1 := Nat.pow_le_pow_right (by decide : 0 < 2) (mono s (s+1) (by omega))
        have le2 := Nat.pow_le_pow_right (by decide : 0 < 2) (mono (s+1) (s+1+m) (by omega))
        rw [intervalWord,if_neg even,show x/2=q from rfl,old,shift]
        omega
      · have evenSucc : (x+1)%2=0 := by omega
        have half : (x+1)/2=q+1 := by dsimp [q]; omega
        rw [intervalWord,if_pos evenSucc,Nat.zero_add,half,shift,newVal]

theorem repeatBits_last (w n : Nat) : repeatBits w n (2^n-1) = 2^(n*w)-1 := by
  induction n with
  | zero => simp [repeatBits]
  | succ n ih =>
    have pos := Nat.two_pow_pos n
    have weight := Nat.two_pow_pos (n*w)
    rw [Nat.pow_succ 2 n,repeatBits,if_neg (by omega : (2^n*2-1)%2≠0),
      show (2^n*2-1)/2=2^n-1 by omega,ih,Nat.succ_mul,Nat.pow_add]
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2^w)]
    have bound : 2^w ≤ 2^(n*w)*2^w := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^w) weight
    have := Nat.two_pow_pos w
    omega

theorem repeatBits_penultimate (w n : Nat) (pos : 0<n) :
    repeatBits w n (2^n-2) = 2^(n*w)-2^w := by
  cases n with
  | zero => omega
  | succ n =>
    have hp := Nat.two_pow_pos n
    rw [Nat.pow_succ 2 n,repeatBits,if_pos (by omega : (2^n*2-2)%2=0),Nat.zero_add,
      show (2^n*2-2)/2=2^n-1 by omega,repeatBits_last,Nat.mul_sub,Nat.mul_one,
      Nat.succ_mul,Nat.pow_add,Nat.mul_comm (2^w)]

def diagonalWord (N : Nat) := intervalWord (fun i => N^i) 0 N

/-- Exactly preservation of ordinary products at the old diagonal; it
    says nothing about the lift by one degree. -/
def DiagonalHomAt (N t : Nat) : Prop := ∀ a b, a < 2^N → b < 2^N →
  diagonalWord N ((tables N).mul a b) =
    (tables t).mul (diagonalWord N a) (diagonalWord N b)

theorem diagonal_row {N t : Nat} (two : 2 ≤ N) (hom : DiagonalHomAt N t)
    (r : Nat) (fits : r < 2^N) : (tables t).mul (2^N-3) r = diagonalWord N r := by
  have size : 4 ≤ 2^N := Nat.pow_le_pow_right (by decide : 0 < 2) two
  have one : diagonalWord N 1 = 2^N-2 := by
    unfold diagonalWord
    rw [intervalWord_one _ _ _ (by omega), Nat.zero_add, Nat.pow_one, Nat.pow_zero]
  induction r with
  | zero => exact ((tables t).mul_zero _).trans (intervalWord_zero _ _ _).symm
  | succ r ih =>
    have he := hom r 1 (by omega) (by omega)
    rw [(tables N).mul_one, Nat.mod_eq_of_lt fits, one] at he
    rw [(tables t).row_recurrence, ih (by omega), show 2^N-3+1 = 2^N-2 by omega, ← he]

/-- The third-level diagonal supplies the two endpoints of every odd
    outer step, with the window and the alignment required by the lift. -/
theorem endpoints_of_diagonal {t : Nat} (scale : t=256^256) (hom : DiagonalHomAt 256 t)
    (r : Nat) (bound : r < midpointColumn) (odd : r%2=1) :
    Nonempty (OddColumnEndpoints t r) := by
  have limit : midpointColumn < 2^256 := Nat.pow_lt_pow_succ (by decide : 1 < 2)
  have fits : r+1 < 2^256 := by omega
  let f := fun i : Nat => 256^i
  have mono (a b : Nat) (le : a ≤ b) : f a ≤ f b := Nat.pow_le_pow_right (by decide) le
  obtain ⟨m,D,mn,positive,div,old,newVal⟩ := intervalWord_carry f mono 0 256 r fits
  let w := 256^m
  have step : f (m+1) = 256*w := by dsimp [f,w]; rw [Nat.pow_succ, Nat.mul_comm]
  simp only [Nat.zero_add] at div old newVal
  rw [step] at div newVal
  have window : 256*w ≤ t := by rw [← step,scale]; exact mono _ _ (by omega)
  have g1 : geometricRow+1 = 2^256-2 := by decide
  refine ⟨⟨m,positive odd,D,window,div,?_,?_⟩⟩
  · exact (diagonal_row (by decide) hom r (by omega)).trans old
  · rw [g1,repeatBits_penultimate _ _ (by decide)]
    exact (diagonal_row (by decide) hom (r+1) fits).trans newVal

theorem odd_corners_of_homomorphisms {t : Nat} (scale : t=256^256) (diagonal : DiagonalHomAt 256 t)
    (stretch : ∀ m, 0 < m → StretchHomAt (256^m) 256) : OddCornersAt t := by
  intro r _ bound odd i ipos iup
  obtain ⟨ends⟩ := endpoints_of_diagonal scale diagonal r bound odd
  exact corners_of_endpoints ends stretch i ipos iup

#print axioms odd_corners_of_homomorphisms
theorem intervalWord_single (f : Nat → Nat) (s n k : Nat) (fit : k<n) :
    intervalWord f s n (2^k) = 2^(f (s+k+1))-2^(f (s+k)) := by
  induction n generalizing s k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [intervalWord_one]
    | succ k =>
      have dbl := Nat.two_pow_pos k
      rw [Nat.pow_succ,intervalWord,if_pos (by omega : 2^k*2%2=0),Nat.zero_add,
        show 2^k*2/2 = 2^k by omega,ih (s+1) k (by omega),show s+1+k=s+(k+1) by omega]

theorem repeatBits_single (w n k : Nat) (fit : k<n) :
    repeatBits w n (2^k) = 2^((k+1)*w)-2^(k*w) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [repeatBits_one]
    | succ k =>
      rw [Nat.pow_succ,repeatBits,if_pos (by omega : 2^k*2%2=0),Nat.zero_add,
        show 2^k*2/2 = 2^k by omega,ih k (by omega), Nat.mul_sub]
      have up (v : Nat) : 2^w * 2^(v*w) = 2^((v+1)*w) := by
        rw [← Nat.pow_add, Nat.succ_mul, Nat.add_comm w]
      rw [up,up]

/-- Read any visible index below a computed finite cap. -/
private theorem image_of_visible_cap (H : TableElement.FirstRowUnbounded) {a x r d : Nat}
    (visible : r<d) (read : act tables d a x = r) : image H a x = r := by
  have h := (TableElement.numeral a).cap_eq_min (TableElement.numeral_total H a) d x
  change signature d ((tables d).mul (a%2^d) (2^x)) = min d (image H a x) at h
  rw [(tables d).mul_mod_left] at h
  change act tables d a x = _ at h
  omega

theorem diagonal_image (H : TableElement.FirstRowUnbounded) {N t k : Nat} (two : 2 ≤ N)
    (scale : t=N^N) (diag : DiagonalHomAt N t) (fit : k<N) :
    image H (2^N-3) k = N^k := by
  have strict : N^k < N^(k+1) := Nat.pow_lt_pow_succ (by omega)
  have upper : N^(k+1) ≤ t := by rw [scale]; exact Nat.pow_le_pow_right (by omega) fit
  apply image_of_visible_cap H (Nat.lt_of_lt_of_le strict upper)
  unfold act
  rw [diagonal_row two diag _ (Nat.pow_lt_pow_right (by decide) fit),diagonalWord,
    intervalWord_single _ _ _ _ fit]
  simp only [Nat.zero_add]
  exact dyadic_tail_signature _ _ _ strict upper

theorem stretch_image (H : TableElement.FirstRowUnbounded) {w n : Nat} (pw : 0<w)
    (hom : StretchHomAt w (n+1)) : image H (2^w-2) n = n*w := by
  have inc : n*w < (n+1)*w := by rw [Nat.succ_mul]; omega
  apply image_of_visible_cap H inc
  unfold act
  rw [stretch_row pw (Nat.zero_lt_succ _) hom _ (Nat.pow_lt_pow_succ (by decide)),
    repeatBits_single _ _ _ (Nat.lt_succ_self n)]
  exact dyadic_tail_signature _ _ _ inc (Nat.le_refl _)

/-- The remaining period bounds are zero tests on ordinary finite
    tables. The geometric upper row of the background family is derived. -/
structure PeriodGuardsAt (t : Nat) : Prop where
  native : ∀ b, 1 ≤ b → b < geometricRow → entry t b (2^256) = 0
  background : ∀ A, 0 < A → A < 2^t → 2^256 ∣ A → ∀ b, 1 ≤ b → b < geometricRow →
    entry (t+1) (A+b) (2^256) = 0
  short : ∀ m, 0 < m → let w := 256^m; ∀ b, 1 ≤ b → b < 2^w-2 → entry (256*w) b (2^w) = 0

abbrev PeriodGuards := PeriodGuardsAt targetIndex

def LicensedStretches : Prop := ∀ m, 0<m → ∀ n, n=256 ∨ n=257 → StretchHomAt (256^m) n

/-- No corner data, positivity at the midpoint, exact stretched image, or
    comparison to the last outer image is assumed by this theorem. -/
theorem target_of_table_readings (H : TableElement.FirstRowUnbounded) (blocks : FiniteBlockLaw)
    (diag : DiagonalHomAt 256 targetIndex) (hom : ∀ m, 0<m → StretchHomAt (256^m) 256)
    (endImage : ∀ m, 0<m → image H (2^(256^m)-2) 256=256*256^m) (guards : PeriodGuards)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow) : Target := by
  have corners := odd_corners_of_homomorphisms targetIndex_eq diag hom
  apply target_of_odd_corners H blocks _ corners nf
  constructor
  · intro i pos fit
    rw [show image H geometricRow 255=256^255 from diagonal_image H (by decide) targetIndex_eq diag (by decide)]
    have up : 256^255 ≤ targetIndex := by rw [targetIndex_eq]; exact Nat.pow_le_pow_right (by decide) (by decide)
    exact Nat.le_trans up ((TableElement.numeral_zero_iff H _ _ _).mp (guards.native i pos fit))
  · intro A pos small aligned b low high
    exact (TableElement.numeral_zero_iff H _ _ _).mp (guards.background A pos small aligned b low high)
  · intro m hm
    exact endImage m hm
  · intro m hm
    dsimp only
    intro b low high
    exact (TableElement.numeral_zero_iff H _ _ _).mp (guards.short m hm b low high)

theorem target_of_table_laws (H : TableElement.FirstRowUnbounded) (blocks : FiniteBlockLaw)
    (diag : DiagonalHomAt 256 targetIndex) (stretches : LicensedStretches) (guards : PeriodGuards)
    (nf : entry (targetIndex+1) (entry (targetIndex+1) 11 3) 1 = geometricRow) : Target :=
  target_of_table_readings H blocks diag (fun m hm => stretches m hm 256 (Or.inl rfl))
    (fun m hm => stretch_image H (Nat.pow_pos (by decide : 0<256)) (stretches m hm 257 (Or.inr rfl)))
    guards nf

#print axioms target_of_table_laws

end Gamma11
