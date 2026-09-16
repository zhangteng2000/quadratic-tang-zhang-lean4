import QuadraticTangZhang.Polar
import Sendov.Reduction.BetaBound

/-!
# Analytic bounds for beta from the exact second-moment polar inequality

The rational estimate follows from the stronger, independently proved
Sendov bound alpha/(3+alpha); see vendor/PROVENANCE.md.
-/

namespace QuadraticTangZhang
open MeasureTheory

theorem polar_le_linear {a x s t : ℝ} (hs : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    polarQuadratic a x s t ≤ 1 + (1-a^2)*(-1+(2-beta a x 1)*t) := by
  have h1 := mul_nonneg (sq_nonneg ((1-a^2)*t)) (sub_nonneg.mpr hs)
  have h2 := mul_nonneg (sq_nonneg (1-a^2)) (mul_nonneg ht (sub_nonneg.mpr ht1))
  dsimp [polarQuadratic, beta]
  nlinarith

theorem polar_exponential {a x s : ℝ} (hxs : x^2 ≤ s) (hs : s ≤ 1)
    {m : ℕ} (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
      Real.exp (((m:ℝ)/2*(1-a^2))*(-1+(2-beta a x 1)*t)) := by
  have he : (0 : ℝ) ≤ m / 2 := by positivity
  have hc : Continuous fun t : ℝ => polarQuadratic a x s t := by unfold polarQuadratic; fun_prop
  have hcPow := (Real.continuous_rpow_const he).comp hc
  have hce : Continuous fun t : ℝ =>
      Real.exp (((m:ℝ)/2*(1-a^2))*(-1+(2-beta a x 1)*t)) := by fun_prop
  apply hpolar.trans
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hcPow.intervalIntegrable _ _) (hce.intervalIntegrable _ _)
  intro t ht
  have hlin := polar_le_linear (a := a) (x := x) hs ht.1 ht.2
  have hexp := Real.add_one_le_exp ((1-a^2)*(-1+(2-beta a x 1)*t))
  have hle : polarQuadratic a x s t ≤ Real.exp ((1-a^2)*(-1+(2-beta a x 1)*t)) := by linarith
  have h := Real.rpow_le_rpow (polarQuadratic_nonneg hxs) hle he
  rw [← Real.exp_mul] at h
  refine h.trans_eq ?_
  congr 1
  ring

theorem beta_rational_bound {a x s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hxs : x^2 ≤ s) (hs : s ≤ 1) {m : ℕ} (hm : 0 < m)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2)) :
    let α := (m:ℝ)/2*(1-a^2)
    0 < beta a x 1 ∧ beta a x 1 < α/(1+α) ∧ α/(1+α) < 1 ∧ a/2 < x := by
  dsimp only
  let α := (m:ℝ)/2*(1-a^2)
  have hα : 0 < α := by
    dsimp [α]
    have : 0 < 1-a^2 := by nlinarith
    positivity
  have hxm : -1 ≤ x := by nlinarith [sq_nonneg (x+1)]
  have hB := beta_one_pos ha ha1 hxm hx
  have hb := Sendov.beta_le hα hB.le (polar_exponential hxs hs hpolar)
  have hden : α/(3+α) < α/(1+α) := by
    apply div_lt_div_of_pos_left hα <;> linarith
  have hrat : α/(1+α) < 1 := by
    rw [div_lt_one (by linarith : 0 < 1+α)]
    linarith
  have hlt := hb.trans_lt hden
  exact ⟨hB, hlt, hrat, x_gt_half_of_beta_lt_one ha (hlt.trans hrat)⟩

theorem beta_log_bound {a x s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hxs : x^2 ≤ s) (hs : s ≤ 1) {m : ℕ} (hm : 0 < m)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, polarQuadratic a x s t ^ ((m:ℝ)/2)) :
    let α := (m:ℝ)/2*(1-a^2)
    Real.log α / α < 1 - beta a x 1 := by
  dsimp only
  let α := (m:ℝ)/2*(1-a^2)
  have hα : 0 < α := by
    dsimp [α]
    have : 0 < 1-a^2 := by nlinarith
    positivity
  have hb := beta_rational_bound ha ha1 hx hxs hs hm hpolar
  have hB1 : beta a x 1 < 1 := hb.2.1.trans hb.2.2.1
  have h := polar_exponential hxs hs hpolar
  change 1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (α*(-1+(2-beta a x 1)*t)) at h
  rw [Sendov.integral_exp_eq' hα (by linarith : beta a x 1 < 2)] at h
  have hden : 0 < α*(2-beta a x 1) := mul_pos hα (by linarith)
  rw [le_div_iff₀ hden, one_mul] at h
  have hmul : α ≤ α*(2-beta a x 1) := by nlinarith
  have hexp : α < Real.exp (α*(1-beta a x 1)) := by linarith [Real.exp_pos (-α)]
  have hlog := (Real.log_lt_iff_lt_exp hα).mpr hexp
  rw [div_lt_iff₀ hα]
  nlinarith

end QuadraticTangZhang
