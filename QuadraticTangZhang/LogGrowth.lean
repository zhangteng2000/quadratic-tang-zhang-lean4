import QuadraticTangZhang.AnalyticConstants
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace QuadraticTangZhang

theorem log_le_linear_scale {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (hbLog : 1 ≤ Real.log b) :
    Real.log t ≤ Real.log b*(t/b) := by
  have ht := hb.trans_le hbt
  have hratio : 1 ≤ t/b := (le_div_iff₀ hb).mpr (by simpa using hbt)
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hb)
  rw [Real.log_div ht.ne' hb.ne'] at hlog
  have hmul := mul_nonneg (sub_nonneg.mpr hbLog) (sub_nonneg.mpr hratio)
  nlinarith

theorem log_le_sqrt_scale {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (hbLog : 2 ≤ Real.log b) :
    Real.log t ≤ Real.log b*Real.sqrt (t/b) := by
  have ht := hb.trans_le hbt
  have hratio : 1 ≤ t/b := (le_div_iff₀ hb).mpr (by simpa using hbt)
  have hsqrt : 1 ≤ Real.sqrt (t/b) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hratio
  have hlog := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hsqrt)
  rw [Real.log_sqrt (div_nonneg ht.le hb.le),Real.log_div ht.ne' hb.ne'] at hlog
  have hmul := mul_nonneg (sub_nonneg.mpr hbLog) (sub_nonneg.mpr hsqrt)
  nlinarith

theorem large_log_bounds {m : ℝ} (hm : 1000000 ≤ m) :
    13 < Real.log m ∧ Real.log m ≤ 14*m/1000000 ∧ Real.log m ≤ 14*Real.sqrt m/1000 := by
  have hm0 : 0 < m := by linarith
  have hlower := log_million_bounds.1.trans_le (Real.log_le_log (by norm_num) hm)
  have h1 := log_le_linear_scale (by norm_num : (0:ℝ)<1000000) hm (by linarith [log_million_bounds.1])
  have h2 := log_le_sqrt_scale (by norm_num : (0:ℝ)<1000000) hm (by linarith [log_million_bounds.1])
  have hs : Real.sqrt (m/1000000)=Real.sqrt m/1000 := by
    rw [Real.sqrt_div hm0.le]
    norm_num
  rw [hs] at h2
  refine ⟨hlower,?_,?_⟩
  · have hp := mul_le_mul_of_nonneg_right log_million_bounds.2.le (show 0 ≤ m/1000000 by positivity)
    linarith
  · have hp := mul_le_mul_of_nonneg_right log_million_bounds.2.le (show 0 ≤ Real.sqrt m/1000 by positivity)
    linarith

theorem exp_small_correction {u : ℝ} (hu : u ≤ 56/1000000) :
    Real.exp u < (1001:ℝ)/1000 := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<1001/1000)
  apply (Real.lt_log_iff_exp_lt (by norm_num)).mp
  norm_num at hl
  linarith

theorem large_degree_power_correction {m : ℝ} (hm : 1000000 ≤ m) :
    m^(4/(m+2)) < (1001:ℝ)/1000 := by
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_def_of_pos hm0]
  apply exp_small_correction
  have hl := (large_log_bounds hm).2.1
  have hlog0 : 0 ≤ Real.log m := le_of_lt (lt_trans (by norm_num) (large_log_bounds hm).1)
  have hratio : 4/(m+2) ≤ 4/m := by gcongr; linarith
  have h := mul_le_mul_of_nonneg_left hratio hlog0
  have hh : Real.log m*(4/m) ≤ 56/1000000 := by
    rw [← mul_div_assoc,div_le_iff₀ hm0]
    nlinarith
  exact h.trans hh

/-- A direct consequence of exp(u-1) ≥ u; no optimization oracle is used. -/
theorem epsilon_power_bound {m e : ℝ} (hm : 1 < m) (he : 0 ≤ e) :
    e*m^(-e) ≤ 1/(Real.exp 1*Real.log m) := by
  have hm0 : 0 < m := by linarith
  have hlog : 0 < Real.log m := Real.log_pos hm
  have heuler : 0 < Real.exp 1 := Real.exp_pos _
  have h := Real.add_one_le_exp (e*Real.log m-1)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (1-e*Real.log m)).le
  rw [← Real.exp_add] at hmul
  have hzero : (e*Real.log m-1)+(1-e*Real.log m)=0 := by ring
  rw [hzero,Real.exp_zero] at hmul
  rw [Real.rpow_def_of_pos hm0,le_div_iff₀ (mul_pos heuler hlog)]
  have hexp : Real.exp 1*Real.exp (Real.log m*(-e))=Real.exp (1-e*Real.log m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : e*Real.exp (Real.log m*(-e))*(Real.exp 1*Real.log m)=
      (e*Real.log m)*Real.exp (1-e*Real.log m) := by rw [← hexp]; ring
  rw [hid]
  linarith

end QuadraticTangZhang
