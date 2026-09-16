import QuadraticTangZhang.UniformBounds

/-! Explicit finite-interval exponential moments for the analytic large-degree estimates. -/
namespace QuadraticTangZhang
open MeasureTheory

theorem integral_t_exp_neg_le {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) :
    (∫ t in (0:ℝ)..b, t*Real.exp (-c*t)) ≤ 1/c^2 := by
  let P : ℝ → ℝ := fun t => -((c*t+1)*Real.exp (-c*t))/c^2
  have hd (t : ℝ) : HasDerivAt P (t*Real.exp (-c*t)) t := by
    have h := (((hasDerivAt_id t).const_mul c).add_const 1).mul
      (((hasDerivAt_id t).const_mul (-c)).exp)
    convert h.neg.div_const (c^2) using 1 <;>
      first | rfl | (simp only [id_eq]; field_simp; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t*Real.exp (-c*t))).intervalIntegrable 0 b)
  rw [hi]
  dsimp [P]
  simp only [mul_zero,add_zero,zero_add,Real.exp_zero,mul_one]
  have hnonneg : 0 ≤ (c*b+1)*Real.exp (-c*b)/c^2 := by positivity
  simp only [neg_div]
  linarith

theorem integral_sq_exp_neg_le {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) :
    (∫ t in (0:ℝ)..b, t^2*Real.exp (-c*t)) ≤ 2/c^3 := by
  let P : ℝ → ℝ := fun t => -((c^2*t^2+2*c*t+2)*Real.exp (-c*t))/c^3
  have hd (t : ℝ) : HasDerivAt P (t^2*Real.exp (-c*t)) t := by
    have hpoly := ((((hasDerivAt_id t).pow 2).const_mul (c^2)).add
      ((hasDerivAt_id t).const_mul (2*c))).add_const 2
    have h := hpoly.mul (((hasDerivAt_id t).const_mul (-c)).exp)
    convert h.neg.div_const (c^3) using 1 <;>
      first | rfl | (simp only [id_eq,Pi.add_apply,Pi.pow_apply]; field_simp; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t^2*Real.exp (-c*t))).intervalIntegrable 0 b)
  rw [hi]
  dsimp [P]
  simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero,zero_add,Real.exp_zero,mul_one]
  have hnonneg : 0 ≤ (c^2*b^2+2*c*b+2)*Real.exp (-c*b)/c^3 := by positivity
  simp only [neg_div]
  linarith

theorem rpow_le_exp_gap {b v r : ℝ} (hb : 0 ≤ b) (hgap : b ≤ 1-v) (hr : 0 ≤ r) :
    b^r ≤ Real.exp (-r*v) := by
  have hbase : b ≤ Real.exp (-v) := by linarith [Real.add_one_le_exp (-v)]
  have h := Real.rpow_le_rpow hb hbase hr
  rw [← Real.exp_mul] at h
  convert h using 1 <;> first | rfl | ring

/-- A single pointwise estimate covers both the decreasing and increasing
parts of beta, including the case where its minimum lies beyond 1. -/
theorem beta_power_split_bound {a x t r : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hx : x ≤ 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) :
    beta a x t^r ≤ Real.exp (-r*a*x*t)+beta a x 1^r := by
  have hb := (beta_pos_on_unit ha ha1 hx ht.1 ht.2).le
  have hb1 := (beta_pos_on_unit ha ha1 hx (by norm_num : (0:ℝ)≤1) le_rfl).le
  by_cases htx : a*t ≤ x
  · have hlin : beta a x t ≤ 1-a*x*t := by
      have h := mul_nonneg (mul_nonneg ha ht.1) (sub_nonneg.mpr htx)
      unfold beta
      nlinarith
    have h := rpow_le_exp_gap hb hlin hr
    have hnonneg := Real.rpow_nonneg hb1 r
    convert h.trans (le_add_of_nonneg_right hnonneg) using 1 <;> first | rfl | ring
  · have hle : beta a x t ≤ beta a x 1 := by
      have h1 := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ht.2)) (sub_nonneg.mpr (le_of_not_ge htx))
      have h2 := mul_nonneg (sq_nonneg a) (sq_nonneg (1-t))
      unfold beta
      nlinarith
    have h := Real.rpow_le_rpow hb hle hr
    linarith [Real.exp_pos (-r*a*x*t)]

theorem direct_integral_split_bound {m : ℕ} (hm : 2 ≤ m) {a x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    directIntegral m a x ≤ 4/(((m-1:ℕ):ℝ)^2*a^2*x^2)+beta a x 1^(((m-1:ℕ):ℝ)/2) := by
  let r := ((m-1:ℕ):ℝ)/2
  have hrNat : 0 < m-1 := by omega
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (by exact_mod_cast hrNat) (by norm_num)
  have hc : Continuous fun t : ℝ => beta a x t := by unfold beta; fun_prop
  have hp := (Real.continuous_rpow_const hr.le).comp hc
  have hI : directIntegral m a x ≤ ∫ t in (0:ℝ)..1,
      t*Real.exp (-(r*a*x)*t)+t*beta a x 1^r := by
    apply intervalIntegral.integral_mono_on (by norm_num) ((continuous_id.mul hp).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => t*Real.exp (-(r*a*x)*t)+t*beta a x 1^r)).intervalIntegrable _ _)
    intro t ht
    have h := mul_le_mul_of_nonneg_left (beta_power_split_bound ha.le ha1 hx1 ht hr.le) ht.1
    convert h using 1 <;> first | rfl | ring
  rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ => t*Real.exp (-(r*a*x)*t))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => t*beta a x 1^r)).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const] at hI
  have htint : (∫ t in (0:ℝ)..1, t) = 1/2 := by simpa using integral_pow (a := (0:ℝ)) (b := 1) 1
  rw [htint] at hI
  have hExp := integral_t_exp_neg_le (mul_pos (mul_pos hr ha) hx0) (by norm_num : (0:ℝ)≤1)
  have heq : 1/(r*a*x)^2=4/(((m-1:ℕ):ℝ)^2*a^2*x^2) := by dsimp [r]; ring
  rw [heq] at hExp
  have hB := Real.rpow_nonneg (beta_pos_on_unit ha.le ha1 hx1 (by norm_num : (0:ℝ)≤1) le_rfl).le r
  dsimp [r] at *
  linarith

end QuadraticTangZhang
