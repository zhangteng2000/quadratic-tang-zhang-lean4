import QuadraticTangZhang.BetaBounds
import QuadraticTangZhang.RhoBounds

/-! # The two polar tests used by every finite certificate record -/

namespace QuadraticTangZhang
open MeasureTheory

theorem chord_polar_bound_at {a x s h : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hxs : x^2 ≤ s) {m : ℕ} (hm : 0 < m) (hh : 0 ≤ h)
    (hrh : rho a x s ≤ h)
    (hpolar : 1 ≤ ∫ t in (0:ℝ)..1, polarQuadratic a x s t^((m:ℝ)/2)) :
    0 ≤ (1+(1-a^2)*h)^((m:ℝ)/2+1)-a^(m+2)-
      ((m:ℝ)/2+1)*(1-a^2)*(1+h) := by
  have hs : 0 ≤ s := (sq_nonneg _).trans hxs
  have he : (0:ℝ) < m/2 := by positivity
  have ha2 : 0 < 1-a^2 := by nlinarith
  let d := (1-a^2)*(1+h)
  have hd : 0 < d := mul_pos ha2 (by linarith)
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcPow := (Real.continuous_rpow_const he.le).comp hc
  have hl : Continuous fun t : ℝ => (a^2+d*t)^((m:ℝ)/2) :=
    (Real.continuous_rpow_const he.le).comp (by fun_prop)
  have hi : 1 ≤ ∫ t in (0:ℝ)..1, (a^2+d*t)^((m:ℝ)/2) := by
    apply hpolar.trans
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hcPow.intervalIntegrable _ _) (hl.intervalIntegrable _ _)
    intro t ht
    apply Real.rpow_le_rpow (polarQuadratic_nonneg hxs) _ he.le
    have hch := polar_le_chord (a := a) (x := x) hs ht.1 ht.2
    have hmul := mul_nonneg (mul_nonneg ha2.le ht.1) (sub_nonneg.mpr hrh)
    dsimp [d]
    nlinarith
  have heval := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t : ℝ => t^((m:ℝ)/2)) (a := 0) (b := 1) d (a^2)
  rw [integral_rpow (Or.inl (by linarith : (-1:ℝ)<(m:ℝ)/2))] at heval
  simp only [mul_one, mul_zero, add_zero] at heval
  have hpow : (a^2)^((m:ℝ)/2+1) = a^(m+2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_natCast a (m+2)]
    congr 1
    push_cast
    ring
  have hend : a^2+d = 1+(1-a^2)*h := by dsimp [d]; ring
  rw [hpow,hend] at heval
  have hmul := mul_le_mul_of_nonneg_left hi hd.le
  rw [mul_one,heval,le_div_iff₀ (by linarith : (0:ℝ)<(m:ℝ)/2+1)] at hmul
  dsimp [d] at hmul
  nlinarith

theorem rectangle_rational_gap {a x s A h : ℝ} {m M : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ≤ 1) (hxs : x^2 ≤ s) (hs : s ≤ 1)
    (hm : 0 < m) (hmM : m ≤ M) (hA : 0 ≤ A) (hAa : A ≤ a)
    (htest : h ≤ 1/(1+(M:ℝ)/2*(1-A^2)))
    (hpolar : 1 ≤ ∫ t in (0:ℝ)..1, polarQuadratic a x s t^((m:ℝ)/2)) :
    h < 1-beta a x 1 := by
  have hb := (beta_rational_bound ha ha1 hx hxs hs hm hpolar).2.1
  have hα : 0 < (m:ℝ)/2*(1-a^2) := mul_pos (by positivity) (by nlinarith)
  have hαM : (m:ℝ)/2*(1-a^2) ≤ (M:ℝ)/2*(1-A^2) := by
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hmM) (by norm_num)
    · nlinarith
    · nlinarith
    · positivity
  have hrecip : 1/(1+(M:ℝ)/2*(1-A^2)) ≤ 1/(1+(m:ℝ)/2*(1-a^2)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have heq : 1/(1+(m:ℝ)/2*(1-a^2)) = 1-((m:ℝ)/2*(1-a^2))/(1+(m:ℝ)/2*(1-a^2)) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self (by linarith)]
  rw [heq] at hrecip
  exact (htest.trans hrecip).trans_lt (by linarith)

theorem rectangle_chord_gap {a x s A Z h : ℝ} {m L M : ℕ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hxs : x^2 ≤ s) (hs : s ≤ 1)
    (hm : 0 < m) (hLm : L ≤ m) (hmM : m ≤ M)
    (hA : 0 ≤ A) (hAa : A ≤ a) (haZ : a ≤ Z) (hZ : Z ≤ 1) (hh : 0 ≤ h)
    (htest : (1+(1-A^2)*h)^((M:ℝ)/2+1)-A^(M+2)-
      ((L:ℝ)/2+1)*(1-Z^2)*(1+h) < 0)
    (hpolar : 1 ≤ ∫ t in (0:ℝ)..1, polarQuadratic a x s t^((m:ℝ)/2)) :
    h < 1-beta a x 1 := by
  have hgap := rho_le_gap (a := a) (x := x) (s := s) (by nlinarith : a^2 ≤ 1) hs
  by_contra hfalse
  have hrh : rho a x s ≤ h := hgap.trans (le_of_not_gt hfalse)
  have hc := chord_polar_bound_at ha ha1 hxs hm hh hrh hpolar
  have hAa2 : A^2 ≤ a^2 := by nlinarith
  have haZ2 : a^2 ≤ Z^2 := by nlinarith
  have hA1 : A ≤ 1 := hAa.trans ha1.le
  have hbase : 1+(1-a^2)*h ≤ 1+(1-A^2)*h := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAa2) hh]
  have hbase1 : 1 ≤ 1+(1-A^2)*h := by nlinarith [mul_nonneg (by nlinarith : 0 ≤ 1-A^2) hh]
  have hp : (1+(1-a^2)*h)^((m:ℝ)/2+1) ≤ (1+(1-A^2)*h)^((M:ℝ)/2+1) := by
    apply (Real.rpow_le_rpow (by nlinarith [mul_nonneg (by nlinarith : 0 ≤ 1-a^2) hh]) hbase (by positivity)).trans
    apply Real.rpow_le_rpow_of_exponent_le hbase1
    have hmcast : (m:ℝ) ≤ M := by exact_mod_cast hmM
    linarith
  have hpow : A^(M+2) ≤ a^(m+2) := by
    calc
      A^(M+2) ≤ A^(m+2) := pow_le_pow_of_le_one hA hA1 (by omega)
      _ ≤ a^(m+2) := pow_le_pow_left₀ hA hAa _
  have hlin : ((L:ℝ)/2+1)*(1-Z^2)*(1+h) ≤ ((m:ℝ)/2+1)*(1-a^2)*(1+h) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul
    · have : (L:ℝ) ≤ m := by exact_mod_cast hLm
      linarith
    · linarith
    · nlinarith
    · positivity
  linarith

end QuadraticTangZhang
