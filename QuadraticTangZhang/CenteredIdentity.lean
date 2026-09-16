import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # The cancellation identity behind the centered interpolation

The identities are polynomial identities, so they are valid even if a factor
vanishes. This avoids dividing by individual factors of the product.
-/

namespace QuadraticTangZhang
open Polynomial
open scoped BigOperators

theorem weighted_product_split {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (D c : ℂ[X]) (w : ι → ℂ[X]) :
    D * (∑ j ∈ s, w j * ∏ k ∈ s.erase j, (D - c * w k)) =
      (∑ j ∈ s, w j) * (∏ k ∈ s, (D - c * w k)) +
        c * ∑ j ∈ s, w j ^ 2 * ∏ k ∈ s.erase j, (D - c * w k) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hprod := Finset.mul_prod_erase s (fun k => D - c * w k) hj
  rw [← hprod]
  ring

theorem centered_interpolation_polynomial {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (D c : ℂ) (w : ι → ℂ) (hw : ∑ j ∈ s, w j = 0) :
    C D * derivative (∏ j ∈ s, (C D - C c * X * C (w j))) =
      -C (c ^ 2) * X * ∑ j ∈ s, C (w j ^ 2) *
        ∏ k ∈ s.erase j, (C D - C c * X * C (w k)) := by
  have hsplit := weighted_product_split s (C D) (C c * X) (fun j => C (w j))
  have hwC : ∑ j ∈ s, C (w j) = (0 : ℂ[X]) := by rw [← map_sum, hw, map_zero]
  rw [hwC, zero_mul, zero_add] at hsplit
  have hd : derivative (∏ j ∈ s, (C D - C c * X * C (w j))) =
      -C c * (∑ j ∈ s, C (w j) * ∏ k ∈ s.erase j, (C D - C c * X * C (w k))) := by
    rw [derivative_prod_finset, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [derivative_sub, derivative_C, derivative_mul, derivative_X,
      zero_mul, zero_add, mul_one, zero_sub]
    ring
  rw [hd]
  calc
    _ = -C c * (C D * ∑ j ∈ s, C (w j) * ∏ k ∈ s.erase j,
        (C D - C c * X * C (w k))) := by ring
    _ = -C c * ((C c * X) * ∑ j ∈ s, C (w j) ^ 2 * ∏ k ∈ s.erase j,
        (C D - C c * X * C (w k))) := by rw [hsplit]
    _ = _ := by simp only [map_pow]; ring

/-- The differential origin identity before integration. -/
theorem origin_derivative_polynomial {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ℂ) (q : ι → ℂ) :
    derivative (∏ j ∈ s, (1 - C a * X * C (q j))) =
      -C a * C (∑ j ∈ s, q j) * (∏ k ∈ s, (1 - C a * X * C (q k))) -
        C (a ^ 2) * X * ∑ j ∈ s, C (q j ^ 2) *
          ∏ k ∈ s.erase j, (1 - C a * X * C (q k)) := by
  have hsplit := weighted_product_split s 1 (C a * X) (fun j => C (q j))
  rw [one_mul] at hsplit
  rw [derivative_prod_finset]
  have hd : (∑ j ∈ s, (∏ k ∈ s.erase j, (1 - C a * X * C (q k))) *
      derivative (1 - C a * X * C (q j))) =
        -C a * ∑ j ∈ s, C (q j) * ∏ k ∈ s.erase j, (1 - C a * X * C (q k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [derivative_sub, derivative_one, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one, zero_sub]
    ring
  rw [hd, hsplit]
  simp only [map_sum, map_pow]
  ring

end QuadraticTangZhang
