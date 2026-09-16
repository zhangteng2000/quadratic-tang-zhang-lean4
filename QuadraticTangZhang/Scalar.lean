import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic reductions in the quadratic Tang--Zhang manuscript

These lemmas prove the displayed scalar implications. The analytic hypotheses
are explicit; none of them is declared as an axiom.
-/

namespace QuadraticTangZhang

def beta (a x t : ℝ) : ℝ := 1 - 2 * a * t * x + a ^ 2 * t ^ 2
def betaS (a x s t : ℝ) : ℝ := 1 - 2 * a * t * x + a ^ 2 * s * t ^ 2
def rho (a x s : ℝ) : ℝ := (1 - a ^ 2) * s - 1 + 2 * a * x
def polarQuadratic (a x s t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * s * t ^ 2

theorem beta_decomposition (a x t : ℝ) :
    beta a x t = 1 - x ^ 2 + (x - a * t) ^ 2 := by
  unfold beta
  ring

theorem betaS_le_beta (a x s t : ℝ) (hs : s ≤ 1) : betaS a x s t ≤ beta a x t := by
  have h := mul_nonneg (sq_nonneg (a * t)) (sub_nonneg.mpr hs)
  dsimp [betaS, beta]
  nlinarith

theorem beta_one_pos {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (_hx : -1 ≤ x) (hx1 : x ≤ 1) : 0 < beta a x 1 := by
  have h := mul_nonneg (show 0 ≤ 2 * a by positivity) (sub_nonneg.mpr hx1)
  have hsq := sq_pos_of_pos (sub_pos.mpr ha1)
  dsimp [beta]
  nlinarith

theorem x_gt_half_of_beta_lt_one {a x : ℝ} (ha : 0 < a) (h : beta a x 1 < 1) :
    a / 2 < x := by
  dsimp [beta] at h
  nlinarith

theorem rho_identity (a x s : ℝ) :
    rho a x s = 1 - beta a x 1 - (1 - a ^ 2) * (1 - s) := by
  unfold rho beta
  ring

theorem rho_le_gap {a x s : ℝ} (ha : a ^ 2 ≤ 1) (hs : s ≤ 1) :
    rho a x s ≤ 1 - beta a x 1 := by
  rw [rho_identity]
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hs))

theorem rho_le_sq {a x s : ℝ} (ha : a ^ 2 ≤ 1) (hs : s ≤ 1) : rho a x s ≤ x ^ 2 := by
  have h := rho_le_gap (x := x) ha hs
  dsimp [beta] at h
  nlinarith [sq_nonneg (x - a)]

theorem betaS_endpoint (a x s : ℝ) : betaS a x s 1 = s - rho a x s := by
  unfold betaS rho
  ring

theorem betaS_endpoint_le {a x s : ℝ} (hs : s ≤ 1) :
    betaS a x s 1 ≤ 1 - rho a x s := by
  rw [betaS_endpoint]
  linarith

theorem polar_chord_gap (a x s t : ℝ) :
    a ^ 2 + (1 - a ^ 2) * (1 + rho a x s) * t - polarQuadratic a x s t =
      (1 - a ^ 2) ^ 2 * s * t * (1 - t) := by
  unfold polarQuadratic rho
  ring

theorem polar_le_chord {a x s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    polarQuadratic a x s t ≤ a ^ 2 + (1 - a ^ 2) * (1 + rho a x s) * t := by
  have h : 0 ≤ (1 - a ^ 2) ^ 2 * s * t * (1 - t) := by positivity
  rw [← polar_chord_gap a x s t] at h
  linarith

/-- The increasing branch of the cubic optimization, including its endpoints. -/
theorem cubic_le_a {a C r : ℝ} (hC : 0 ≤ C) (hCa : 2 * C ≤ a)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) : a * r + C * r * (1 - r ^ 2) ≤ a := by
  have hrr : r * (r + 1) ≤ 2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hCr : C * (r * (r + 1)) ≤ C * 2 := mul_le_mul_of_nonneg_left hrr hC
  have hprod := mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ a - C * (r * (r + 1)) by linarith)
  nlinarith

/-- A polynomial identity replacing the square-root optimization formula. -/
theorem cubic_discriminant_identity (b C r : ℝ) :
    4 * b ^ 3 - 27 * C * (b * r - C * r ^ 3) ^ 2 =
      (b - 3 * C * r ^ 2) ^ 2 * (4 * b - 3 * C * r ^ 2) := by ring

theorem cubic_discriminant_nonneg {a C r : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    27 * C * (a * r + C * r * (1 - r ^ 2)) ^ 2 ≤ 4 * (a + C) ^ 3 := by
  have hrsq : r ^ 2 ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hCrsq := mul_le_mul_of_nonneg_left hrsq hC
  have hp : 0 ≤ (a + C - 3 * C * r ^ 2) ^ 2 * (4 * (a + C) - 3 * C * r ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  rw [← cubic_discriminant_identity] at hp
  convert sub_nonneg.mp hp using 1; ring

/-- Soundness of the manuscript's cubic exclusion test, with an explicit scalar input. -/
theorem exclude_center_cubic {a C E r : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hE : E < 1)
    (htest : 4 * (a + C) ^ 3 < 27 * C * (1 - E) ^ 2)
    (hscalar : 1 ≤ a * r + C * r * (1 - r ^ 2) + E) : False := by
  let f := a * r + C * r * (1 - r ^ 2)
  have hf : 1 - E ≤ f := by dsimp [f]; linarith
  have hsq : (1 - E) ^ 2 ≤ f ^ 2 := sq_le_sq₀ (by linarith) (by linarith) |>.mpr hf
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 27 * C by positivity)
  have hbound := cubic_discriminant_nonneg ha hC.le hr hr1
  change 27 * C * f ^ 2 ≤ _ at hbound
  linarith

theorem exclude_center_monotone {a C E r : ℝ} (hC : 0 ≤ C) (hCa : 2 * C ≤ a)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (htest : a + E < 1)
    (hscalar : 1 ≤ a * r + C * r * (1 - r ^ 2) + E) : False := by
  have := cubic_le_a hC hCa hr hr1
  linarith

theorem boundary_margin {a : ℝ} (_ha : 0 ≤ a) (ha1 : a < 1) :
    a + (1 - a ^ 2) / 4 < 1 := by
  nlinarith [sq_nonneg (1 - a)]

theorem exclude_center_boundary {a C E r : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hC : 0 ≤ C) (hCa : 2 * C ≤ a) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hE : E < (1 - a ^ 2) / 4)
    (hscalar : 1 ≤ a * r + C * r * (1 - r ^ 2) + E) : False := by
  have := cubic_le_a hC hCa hr hr1
  have := boundary_margin ha ha1
  linarith

theorem exclude_direct {F R a m : ℝ}
    (htest : F + R + m * a / (m + 1) < 1)
    (hscalar : 1 ≤ F + m * a / (m + 1) + R) : False := by linarith

/-- The polynomial factor used in the small-degree argument is strictly positive. -/
theorem small_degree_factor_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hasq : a ^ 2 < 1 := by nlinarith
  have h := mul_pos (show 0 < 3 * a by positivity) (sub_pos.mpr hasq)
  nlinarith [sq_nonneg (a ^ 2)]

theorem small_degree_deficit_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < (1 - a) ^ 3 * (1 + a) / 5 * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  have := small_degree_factor_pos ha ha1
  positivity

end QuadraticTangZhang
