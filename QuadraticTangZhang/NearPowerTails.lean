import QuadraticTangZhang.ExponentialIntegrals
import QuadraticTangZhang.LogGrowth

namespace QuadraticTangZhang

theorem exp_neg_four_log {m : ℝ} (hm : 0 < m) : Real.exp (-4*Real.log m)=1/m^4 := by
  have heq : Real.exp (-4*Real.log m)=m^(-(4:ℝ)) := by
    rw [Real.rpow_def_of_pos hm]
    congr 1
    ring
  rw [heq,Real.rpow_neg hm.le]
  rw [show m^(4:ℝ)=m^(4:ℕ) from Real.rpow_natCast m 4,inv_eq_one_div]

theorem near_power_tails {m α B : ℝ} (hm : 1000000 ≤ m) (hα : 0 < α) (hαm : α ≤ m/20)
    (hB : 0 ≤ B) (hBrat : B < α/(1+α)) (hBlog : Real.log α/α < 1-B) :
    B^((m-3)/2) ≤ 1/m^4 ∧ ((133:ℝ)/160)^((m-3)/2) ≤ 1/m^4 := by
  let v := (m-3)/2
  have hm0 : 0 < m := by linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hvm : m/3 ≤ v := by dsimp [v]; linarith
  have hlog := large_log_bounds hm
  have hs0 := Real.sqrt_nonneg m
  have hspos := Real.sqrt_pos.mpr hm0
  have hsq := Real.sq_sqrt hm0.le
  have hs1000 : 1000 ≤ Real.sqrt m := by
    nlinarith [sq_nonneg (Real.sqrt m-1000)]
  have hden : 0 < 1+α := by linarith
  have hgap : 1/(1+α) < 1-B := by
    have hid : 1/(1+α)=1-α/(1+α) := by rw [eq_sub_iff_add_eq,← add_div,div_self hden.ne']
    rw [hid]
    linarith
  have hvgap : 4*Real.log m < v*(1-B) := by
    by_cases hsmall : α ≤ Real.sqrt m
    · have hvratio : Real.sqrt m/6 ≤ v/(1+α) := by
        rw [le_div_iff₀ hden]
        have hmul := mul_le_mul_of_nonneg_left hsmall hs0
        nlinarith
      have hg := mul_lt_mul_of_pos_left hgap hv
      have hg' : v/(1+α) < v*(1-B) := by simpa only [← mul_div_assoc,mul_one] using hg
      have hloglt : 4*Real.log m < Real.sqrt m/6 := by nlinarith [hlog.2.2]
      exact hloglt.trans_le (hvratio.trans hg'.le)
    · have hsα : Real.sqrt m ≤ α := le_of_lt (lt_of_not_ge hsmall)
      have hlα := Real.log_le_log hspos hsα
      rw [Real.log_sqrt hm0.le] at hlα
      have hlα0 : 0 ≤ Real.log α := by linarith [hlog.1]
      have hratio : 9 ≤ v/α := by rw [le_div_iff₀ hα]; dsimp [v]; linarith
      have hmul := mul_le_mul_of_nonneg_right hratio hlα0
      have hstrict := mul_lt_mul_of_pos_left hBlog hv
      have heq : (v/α)*Real.log α=v*(Real.log α/α) := by ring
      rw [heq] at hmul
      nlinarith [hlog.1]
  constructor
  · have hp := rpow_le_exp_gap hB (show B ≤ 1-(1-B) by linarith) hv.le
    apply hp.trans
    rw [← exp_neg_four_log hm0]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hp := rpow_le_exp_gap (by norm_num : (0:ℝ)≤133/160)
      (show (133:ℝ)/160 ≤ 1-27/160 by norm_num) hv.le
    apply hp.trans
    rw [← exp_neg_four_log hm0]
    apply Real.exp_le_exp.mpr
    nlinarith [hlog.2.1]

theorem scalar_near_power_tails {m : ℕ} {a x s r : ℝ} (hw : ScalarConditions m a x s r)
    (hm : 1000000 ≤ m) (hnear : 1-a^2 ≤ 1/10) :
    beta a x 1^(((m:ℝ)-3)/2) ≤ 1/(m:ℝ)^4 ∧
      ((133:ℝ)/160)^(((m:ℝ)-3)/2) ≤ 1/(m:ℝ)^4 := by
  have hm0 : 0 < m := by omega
  have hb := beta_rational_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper hm0 hw.polar
  apply near_power_tails (by exact_mod_cast hm)
    (mul_pos (by positivity) (by nlinarith [hw.a_pos,hw.a_lt_one]))
    (by have h := mul_le_mul_of_nonneg_left hnear (show (0:ℝ)≤(m:ℝ)/2 by positivity); linarith)
    hb.1.le hb.2.1
  exact beta_log_bound hw.a_pos hw.a_lt_one hw.x_le_one hw.moment_lower hw.moment_upper hm0 hw.polar

end QuadraticTangZhang
