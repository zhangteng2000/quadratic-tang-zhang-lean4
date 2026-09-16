import QuadraticTangZhang.AnalyticConstants
import Sendov.Analytic.Maclaurin
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # Uniform AM--GM bounds for products with a factor deleted -/

namespace QuadraticTangZhang
open scoped BigOperators

theorem prod_norm_sq_le_mean {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∏ i ∈ s, f i‖ ^ 2 ≤ ((∑ i ∈ s, ‖f i‖ ^ 2) / s.card) ^ s.card := by
  have h := Sendov.Multiset.prod_le_mean_pow (s.val.map (fun i => ‖f i‖ ^ 2)) (by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact sq_nonneg _)
  simpa only [Multiset.card_map, ← Finset.prod_eq_multiset_prod, ← Finset.sum_eq_multiset_sum,
    ← Finset.prod_pow, norm_prod, Finset.card_def] using h

theorem norm_prod_le_moment {ι : Type*} (s : Finset ι) (hs : 0 < s.card)
    (f : ι → ℂ) {B : ℝ} (hB : 0 ≤ B) (hmean : (∑ i ∈ s, ‖f i‖ ^ 2) ≤ s.card * B) :
    ‖∏ i ∈ s, f i‖ ≤ B ^ ((s.card : ℝ) / 2) := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hmean0 : 0 ≤ (∑ i ∈ s, ‖f i‖ ^ 2) / s.card := by positivity
  have hm : (∑ i ∈ s, ‖f i‖ ^ 2) / s.card ≤ B :=
    (div_le_iff₀ hcard).mpr (by simpa only [mul_comm] using hmean)
  have hpow := pow_le_pow_left₀ hmean0 hm s.card
  have hsq := (prod_norm_sq_le_mean s f).trans hpow
  have hpow2 : (B ^ ((s.card : ℝ) / 2)) ^ 2 = B ^ s.card := by
    rw [← Real.rpow_natCast (B ^ ((s.card : ℝ) / 2)) 2, ← Real.rpow_mul hB,
      ← Real.rpow_natCast B s.card]
    congr 1
    norm_num
  rw [← hpow2] at hsq
  nlinarith [norm_nonneg (∏ i ∈ s, f i), Real.rpow_nonneg hB ((s.card:ℝ)/2)]

theorem deleted_amgm_coefficient {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) / (m - 1 : ℕ)) ^ (m - 1) ≤ Real.exp 1 := by
  have hk : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hmcast : (m : ℝ) = (m-1 : ℕ) + 1 := by exact_mod_cast (show m = (m-1)+1 by omega)
  have hb : (m : ℝ) / (m-1 : ℕ) ≤ Real.exp (1 / (m-1 : ℕ)) := by
    have h := Real.add_one_le_exp (1 / (m-1 : ℕ))
    rw [hmcast]
    have heq : ((m-1 : ℕ) + 1 : ℝ) / (m-1 : ℕ) = 1 / (m-1 : ℕ) + 1 := by field_simp; ring
    rwa [heq]
  have hp := pow_le_pow_left₀ (by positivity) hb (m-1)
  have he : Real.exp (1 / (m-1 : ℕ)) ^ (m-1) = Real.exp 1 := by
    rw [← Real.rpow_natCast, ← Real.exp_mul]
    congr 1
    field_simp
  rwa [he] at hp

/-- The constant 5/3 is uniform in the number of factors. -/
theorem norm_deleted_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : 2 ≤ s.card) (j : ι) (hj : j ∈ s) (f : ι → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hmean : (∑ i ∈ s, ‖f i‖ ^ 2) ≤ s.card * B) :
    ‖∏ i ∈ s.erase j, f i‖ ≤ (5/3:ℝ) * B ^ (((s.card - 1 : ℕ) : ℝ) / 2) := by
  have hcard : (s.erase j).card = s.card-1 := Finset.card_erase_of_mem hj
  have hk : (0:ℝ) < (s.card-1 : ℕ) := by exact_mod_cast (show 0 < s.card-1 by omega)
  have hsumle : (∑ i ∈ s.erase j, ‖f i‖^2) ≤ (∑ i ∈ s, ‖f i‖^2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => sq_nonneg _)
  have havg : (∑ i ∈ s.erase j, ‖f i‖^2) / (s.card-1 : ℕ) ≤
      (s.card:ℝ) / (s.card-1 : ℕ) * B := by
    apply (div_le_iff₀ hk).mpr
    have h := hsumle.trans hmean
    convert h using 1; field_simp
  have hsq := prod_norm_sq_le_mean (s.erase j) f
  rw [hcard] at hsq
  have hpow := pow_le_pow_left₀ (by positivity) havg (s.card-1)
  rw [mul_pow] at hpow
  have hcoef := deleted_amgm_coefficient hs
  have hexp : Real.exp 1 ≤ (5/3:ℝ)^2 := by linarith [exp_one_bounds.2]
  have hbound := mul_le_mul_of_nonneg_right (hcoef.trans hexp) (pow_nonneg hB (s.card-1))
  have hsqfinal := hsq.trans (hpow.trans hbound)
  have heq : ((5/3:ℝ) * B ^ (((s.card-1:ℕ):ℝ)/2))^2 =
      (5/3:ℝ)^2 * B^(s.card-1) := by
    rw [mul_pow, ← Real.rpow_natCast (B^(((s.card-1:ℕ):ℝ)/2)) 2, ← Real.rpow_mul hB,
      ← Real.rpow_natCast B (s.card-1)]
    congr 2
    norm_num
  rw [← heq] at hsqfinal
  nlinarith [norm_nonneg (∏ i ∈ s.erase j, f i), Real.rpow_nonneg hB (((s.card-1:ℕ):ℝ)/2)]

end QuadraticTangZhang
