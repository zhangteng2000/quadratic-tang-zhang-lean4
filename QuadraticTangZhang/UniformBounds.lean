import QuadraticTangZhang.RectangleBounds
import QuadraticTangZhang.FiniteQuadrature

namespace QuadraticTangZhang
open MeasureTheory

structure ScalarConditions (m : ℕ) (a x s r : ℝ) : Prop where
  degree : 5 ≤ m
  a_pos : 0 < a
  a_lt_one : a < 1
  x_le_one : x ≤ 1
  moment_lower : x^2 ≤ s
  moment_upper : s ≤ 1
  r_nonneg : 0 ≤ r
  r_le_one : r ≤ 1
  polar : 1 ≤ ∫ t in (0:ℝ)..1, polarQuadratic a x s t^((m:ℝ)/2)
  centered : 1 ≤ a*r+centerCoefficient m a x*r*(1-r^2)+beta a x 1^(((m+1:ℕ):ℝ)/2)
  direct : 1 ≤ beta a x 1^((m:ℝ)/2)+(m:ℝ)*a/(m+1)+(5/3:ℝ)*a^2*m*directIntegral m a x

theorem affine_denominator_pos {d t : ℝ} (hd : d < 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 < 1-d*t := by
  by_cases h : 0 ≤ d
  · nlinarith [mul_nonneg h (sub_nonneg.mpr ht.2)]
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) ht.1
    linarith

theorem envelope_quotient_continuous {A h R d : ℝ} (hR : 0 ≤ R) (hd : d < 1) :
    ContinuousOn (fun t : ℝ => boxEnvelope A h t^R/(1-d*t)) (Set.Icc (0:ℝ) 1) := by
  have hc : Continuous fun t : ℝ => boxEnvelope A h t := by unfold boxEnvelope; fun_prop
  exact ((Real.continuous_rpow_const hR).comp hc).continuousOn.div
    (by fun_prop) (fun t ht => (affine_denominator_pos hd ht).ne')

theorem uniform_integral_bounds {m L : ℕ} {a x A Z h : ℝ}
    (hm : 5 ≤ m) (hL : 5 ≤ L) (hLm : L ≤ m)
    (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (hA : 0 ≤ A) (hAa : A ≤ a) (haZ : a ≤ Z)
    (hh0 : 0 ≤ h) (hh : h ≤ 1-beta a x 1) (hsmall : (Z^2+h)/2 < 1) :
    directIntegral m a x ≤ ∫ t in (0:ℝ)..1, t*boxEnvelope A h t^(((L-1:ℕ):ℝ)/2) ∧
    centerIntegral m a x ≤ ∫ t in (0:ℝ)..1, t^2*(boxEnvelope A h t^(((L-1:ℕ):ℝ)/2)/(1-(Z^2+h)/2*t)) := by
  have hR : (0:ℝ) ≤ ((L-1:ℕ):ℝ)/2 := by positivity
  have hRr : ((L-1:ℕ):ℝ)/2 ≤ ((m-1:ℕ):ℝ)/2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hLm 1) (by norm_num)
  have hr : (1:ℝ) ≤ ((m-1:ℕ):ℝ)/2 := by
    have : (2:ℝ) ≤ (m-1:ℕ) := by exact_mod_cast (show 2 ≤ m-1 by omega)
    linarith
  have hcB : Continuous fun t : ℝ => boxEnvelope A h t := by unfold boxEnvelope; fun_prop
  have hcβ : Continuous fun t : ℝ => beta a x t := by unfold beta; fun_prop
  have hpowB := (Real.continuous_rpow_const hR).comp hcB
  have hpowβ := (Real.continuous_rpow_const (show (0:ℝ) ≤ ((m-1:ℕ):ℝ)/2 by positivity)).comp hcβ
  constructor
  · apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_id.mul hpowβ).intervalIntegrable _ _) ((continuous_id.mul hpowB).intervalIntegrable _ _)
    intro t ht
    exact mul_le_mul_of_nonneg_left (rectangle_envelope_power_bound ha ha1 hx hA hAa hh0 hh ht hR hRr) ht.1
  · apply intervalIntegral.integral_mono_on (by norm_num)
      (centerIntegral_integrable ha ha1 hx m)
      (((continuous_id.pow 2).continuousOn.mul (envelope_quotient_continuous hR hsmall)).intervalIntegrable_of_Icc (by norm_num))
    intro t ht
    have hhq := rectangle_envelope_quotient_bound ha ha1 hx hA hAa haZ hh0 hh ht hr hR hRr hsmall
    simpa only [mul_div_assoc,Pi.mul_apply,Pi.pow_apply,id_eq] using mul_le_mul_of_nonneg_left hhq (sq_nonneg t)

theorem uniform_coefficient_bounds {m L M : ℕ} {a x A Z h J₁ J₂ : ℝ}
    (hm : 5 ≤ m) (hL : 5 ≤ L) (hLm : L ≤ m) (hmM : m ≤ M)
    (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (hA : 0 ≤ A) (hAa : A ≤ a) (haZ : a ≤ Z)
    (hh0 : 0 ≤ h) (hh : h ≤ 1-beta a x 1) (hsmall : (Z^2+h)/2 < 1)
    (hJ₁ : (∫ t in (0:ℝ)..1, t*boxEnvelope A h t^(((L-1:ℕ):ℝ)/2)) ≤ J₁)
    (hJ₂ : (∫ t in (0:ℝ)..1, t^2*(boxEnvelope A h t^(((L-1:ℕ):ℝ)/2)/(1-(Z^2+h)/2*t))) ≤ J₂) :
    (5/3:ℝ)*a^2*m*directIntegral m a x ≤ (5/3:ℝ)*Z^2*M*J₁ ∧
    centerCoefficient m a x ≤ (5/6:ℝ)*Z^3*((M:ℝ)+1)*M*J₂ := by
  have hi := uniform_integral_bounds hm hL hLm ha ha1 hx hA hAa haZ hh0 hh hsmall
  have hZ0 : 0 ≤ Z := ha.trans haZ
  have hmR : (m:ℝ) ≤ M := by exact_mod_cast hmM
  have hI₁ : 0 ≤ directIntegral m a x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg ht.1 (Real.rpow_nonneg (beta_pos_on_unit ha ha1 hx ht.1 ht.2).le _)
  have hI₂ := centerIntegral_nonneg ha ha1 hx m
  constructor
  · apply mul_le_mul _ (hi.1.trans hJ₁) hI₁ (by positivity)
    apply mul_le_mul _ hmR (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haZ 2) (by norm_num)
  · unfold centerCoefficient
    have hcoef : 5*a^3*((m:ℝ)+1)*m/6 ≤ (5/6:ℝ)*Z^3*((M:ℝ)+1)*M := by
      have h := mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haZ 3) (by norm_num : (0:ℝ)≤5/6))
          (add_le_add_right hmR 1) (by positivity) (by positivity)) hmR (by positivity) (by positivity)
      convert h using 1 <;> first | rfl | ring
    exact mul_le_mul hcoef (hi.2.trans hJ₂) hI₂ (by positivity)

theorem uniform_endpoint_bound {m L : ℕ} {a x A h : ℝ}
    (hLm : L ≤ m) (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (hA : 0 ≤ A) (hAa : A ≤ a) (hh0 : 0 ≤ h) (hh : h ≤ 1-beta a x 1) :
    beta a x 1^((m:ℝ)/2) ≤ (1-h)^((L:ℝ)/2) ∧
    beta a x 1^(((m+1:ℕ):ℝ)/2) ≤ (1-h)^(((L+1:ℕ):ℝ)/2) := by
  constructor
  · simpa [boxEnvelope] using rectangle_envelope_power_bound ha ha1 hx hA hAa hh0 hh
      (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) (by positivity : (0:ℝ)≤(L:ℝ)/2)
      (div_le_div_of_nonneg_right (by exact_mod_cast hLm) (by norm_num))
  · simpa [boxEnvelope] using rectangle_envelope_power_bound ha ha1 hx hA hAa hh0 hh
      (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) (by positivity : (0:ℝ)≤((L+1:ℕ):ℝ)/2)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hLm 1) (by norm_num))

end QuadraticTangZhang
