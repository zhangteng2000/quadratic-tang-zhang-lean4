import QuadraticTangZhang.ConvexQuadrature
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # F. Directed dyadic rounding and certified binary powers

All executable operations use rational or integer arithmetic. Their
inequalities are proved here, before any certificate record is evaluated.
-/

namespace QuadraticTangZhang

def roundDown (S : ℕ) (x : ℚ) : ℚ := (⌊x*S⌋₊ : ℚ)/S
def roundUp (S : ℕ) (x : ℚ) : ℚ := (⌈x*S⌉₊ : ℚ)/S

theorem roundDown_nonneg (S : ℕ) (x : ℚ) : 0 ≤ roundDown S x := by unfold roundDown; positivity
theorem roundUp_nonneg (S : ℕ) (x : ℚ) : 0 ≤ roundUp S x := by unfold roundUp; positivity

theorem roundDown_le {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) : roundDown S x ≤ x := by
  unfold roundDown
  apply (div_le_iff₀ (by positivity : (0:ℚ)<S)).mpr
  exact Nat.floor_le (mul_nonneg hx (Nat.cast_nonneg S))

theorem le_roundUp {S : ℕ} (hS : 0 < S) (x : ℚ) : x ≤ roundUp S x := by
  unfold roundUp
  apply (le_div_iff₀ (by positivity : (0:ℚ)<S)).mpr
  exact Nat.le_ceil _

theorem roundDown_cast_le {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) :
    (roundDown S x : ℝ) ≤ (x:ℝ) := by exact_mod_cast roundDown_le hS hx

theorem cast_le_roundUp {S : ℕ} (hS : 0 < S) (x : ℚ) :
    (x:ℝ) ≤ (roundUp S x : ℝ) := by exact_mod_cast le_roundUp hS x

def roundedPowLower (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if hn : n=0 then 1 else
    let z := roundedPowLower S x (n/2)
    let zz := roundDown S (z*z)
    if n%2=0 then zz else roundDown S (zz*x)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

def roundedPowUpper (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if hn : n=0 then 1 else
    let z := roundedPowUpper S x (n/2)
    let zz := roundUp S (z*z)
    if n%2=0 then zz else roundUp S (zz*x)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem roundedPowLower_sound {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ roundedPowLower S x n ∧ roundedPowLower S x n ≤ x^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [roundedPowLower]
    · have hn2 := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1<2)
      have hz := ih (n/2) hn2
      have hsq : roundedPowLower S x (n/2)*roundedPowLower S x (n/2) ≤ x^(n/2)*x^(n/2) :=
        mul_le_mul hz.2 hz.2 hz.1 (pow_nonneg hx _)
      have hd := (roundDown_le hS (mul_nonneg hz.1 hz.1)).trans hsq
      rw [roundedPowLower, dif_neg hn]
      dsimp only
      by_cases he : n%2=0
      · rw [if_pos he]
        refine ⟨roundDown_nonneg _ _, ?_⟩
        have hpower : x^(n/2)*x^(n/2)=x^n := by rw [← pow_add]; congr 1; omega
        exact hd.trans_eq hpower
      · rw [if_neg he]
        refine ⟨roundDown_nonneg _ _, ?_⟩
        have h := (roundDown_le hS (mul_nonneg (roundDown_nonneg _ _) hx)).trans
          (mul_le_mul_of_nonneg_right hd hx)
        have hpower : (x^(n/2)*x^(n/2))*x=x^n := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        exact h.trans_eq hpower

theorem roundedPowUpper_sound {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ roundedPowUpper S x n ∧ x^n ≤ roundedPowUpper S x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [roundedPowUpper]
    · have hn2 := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1<2)
      have hz := ih (n/2) hn2
      have hsq : x^(n/2)*x^(n/2) ≤ roundedPowUpper S x (n/2)*roundedPowUpper S x (n/2) :=
        mul_le_mul hz.2 hz.2 (pow_nonneg hx _) hz.1
      have hu := hsq.trans (le_roundUp hS _)
      rw [roundedPowUpper, dif_neg hn]
      dsimp only
      by_cases he : n%2=0
      · rw [if_pos he]
        refine ⟨roundUp_nonneg _ _, ?_⟩
        have hpower : x^(n/2)*x^(n/2)=x^n := by rw [← pow_add]; congr 1; omega
        rwa [hpower] at hu
      · rw [if_neg he]
        refine ⟨roundUp_nonneg _ _, ?_⟩
        have h := (mul_le_mul_of_nonneg_right hu hx).trans (le_roundUp hS _)
        have hpower : (x^(n/2)*x^(n/2))*x=x^n := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rwa [hpower] at h

def roundedSqrtLower (S : ℕ) (x : ℚ) : ℚ := ((Nat.sqrt (⌊x*S⌋₊ * S) : ℕ) : ℚ)/S
def roundedSqrtUpper (S : ℕ) (x : ℚ) : ℚ := ((Nat.sqrt (⌈x*S⌉₊ * S)+1 : ℕ) : ℚ)/S

theorem roundedSqrtLower_nonneg (S : ℕ) (x : ℚ) : 0 ≤ roundedSqrtLower S x := by
  unfold roundedSqrtLower
  positivity

theorem roundedSqrtUpper_nonneg (S : ℕ) (x : ℚ) : 0 ≤ roundedSqrtUpper S x := by
  unfold roundedSqrtUpper
  positivity

theorem roundedSqrtLower_sq {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) :
    (roundedSqrtLower S x)^2 ≤ x := by
  have hroot : ((Nat.sqrt (⌊x*S⌋₊ * S) : ℕ) : ℚ)^2 ≤ (⌊x*S⌋₊ : ℚ)*S := by
    exact_mod_cast Nat.sqrt_le' (⌊x*S⌋₊ * S)
  have hfloor := Nat.floor_le (mul_nonneg hx (Nat.cast_nonneg S))
  have hmul := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg S : (0:ℚ)≤S)
  unfold roundedSqrtLower
  rw [div_pow, div_le_iff₀ (by positivity : (0:ℚ)<(S:ℚ)^2)]
  nlinarith

theorem le_roundedSqrtUpper_sq {S : ℕ} (hS : 0 < S) (x : ℚ) :
    x ≤ (roundedSqrtUpper S x)^2 := by
  have hroot : (⌈x*S⌉₊ : ℚ)*S < ((Nat.sqrt (⌈x*S⌉₊ * S)+1 : ℕ) : ℚ)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (⌈x*S⌉₊ * S)
  have hceil := Nat.le_ceil (x*S)
  have hmul := mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg S : (0:ℚ)≤S)
  unfold roundedSqrtUpper
  rw [div_pow, le_div_iff₀ (by positivity : (0:ℚ)<(S:ℚ)^2)]
  nlinarith

theorem roundedSqrt_sound {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) :
    (roundedSqrtLower S x : ℝ) ≤ Real.sqrt (x:ℝ) ∧
      Real.sqrt (x:ℝ) ≤ (roundedSqrtUpper S x : ℝ) := by
  have hxR : (0:ℝ) ≤ x := by exact_mod_cast hx
  have hL : (roundedSqrtLower S x : ℝ)^2 ≤ (x:ℝ) := by exact_mod_cast roundedSqrtLower_sq hS hx
  have hU : (x:ℝ) ≤ (roundedSqrtUpper S x : ℝ)^2 := by exact_mod_cast le_roundedSqrtUpper_sq hS x
  have hLn : (0:ℝ) ≤ (roundedSqrtLower S x : ℝ) := by exact_mod_cast roundedSqrtLower_nonneg S x
  have hUn : (0:ℝ) ≤ (roundedSqrtUpper S x : ℝ) := by exact_mod_cast roundedSqrtUpper_nonneg S x
  constructor <;> nlinarith [Real.sq_sqrt hxR,Real.sqrt_nonneg (x:ℝ)]

def halfPowerLower (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if n%2=0 then roundedPowLower S x (n/2)
  else roundDown S (roundedPowLower S x (n/2)*roundedSqrtLower S x)

def halfPowerUpper (S : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  if n%2=0 then roundedPowUpper S x (n/2)
  else roundUp S (roundedPowUpper S x (n/2)*roundedSqrtUpper S x)

theorem rpow_half_nat_even (x : ℝ) {n : ℕ} (hn : n%2=0) : x^((n:ℝ)/2) = x^(n/2) := by
  have hcast : (n:ℝ)/2 = ((n/2:ℕ):ℝ) := by
    have h : n=2*(n/2) := by omega
    conv_lhs => rw [h]
    push_cast
    ring
  rw [hcast,Real.rpow_natCast]

theorem rpow_half_nat_odd {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n%2≠0) :
    x^((n:ℝ)/2) = x^(n/2)*Real.sqrt x := by
  have hcast : (n:ℝ)/2 = ((n/2:ℕ):ℝ)+(1/2:ℝ) := by
    have h : n=2*(n/2)+1 := by omega
    conv_lhs => rw [h]
    push_cast
    ring
  rw [hcast,Real.rpow_add_of_nonneg hx (Nat.cast_nonneg _) (by norm_num),
    Real.rpow_natCast,Real.sqrt_eq_rpow]

theorem halfPower_sound {S : ℕ} (hS : 0 < S) {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (halfPowerLower S x n : ℝ) ≤ (x:ℝ)^((n:ℝ)/2) ∧
      (x:ℝ)^((n:ℝ)/2) ≤ (halfPowerUpper S x n : ℝ) := by
  have hxR : (0:ℝ) ≤ x := by exact_mod_cast hx
  have hl := roundedPowLower_sound hS hx (n/2)
  have hu := roundedPowUpper_sound hS hx (n/2)
  have hlR : (roundedPowLower S x (n/2) : ℝ) ≤ (x:ℝ)^(n/2) := by exact_mod_cast hl.2
  have huR : (x:ℝ)^(n/2) ≤ (roundedPowUpper S x (n/2) : ℝ) := by exact_mod_cast hu.2
  have hl0 : (0:ℝ) ≤ (roundedPowLower S x (n/2) : ℝ) := by exact_mod_cast hl.1
  have hu0 : (0:ℝ) ≤ (roundedPowUpper S x (n/2) : ℝ) := by exact_mod_cast hu.1
  by_cases hn : n%2=0
  · simp only [halfPowerLower,halfPowerUpper,if_pos hn,rpow_half_nat_even _ hn]
    exact ⟨hlR,huR⟩
  · simp only [halfPowerLower,halfPowerUpper,if_neg hn,rpow_half_nat_odd hxR hn]
    have hsqrt := roundedSqrt_sound hS hx
    have hsL0 : (0:ℝ) ≤ (roundedSqrtLower S x : ℝ) := by exact_mod_cast roundedSqrtLower_nonneg S x
    constructor
    · have hr := roundDown_cast_le hS (mul_nonneg hl.1 (roundedSqrtLower_nonneg S x))
      rw [Rat.cast_mul] at hr
      exact hr.trans (mul_le_mul hlR hsqrt.1 hsL0 (pow_nonneg hxR _))
    · have hmul := mul_le_mul huR hsqrt.2 (Real.sqrt_nonneg _) hu0
      have hr := cast_le_roundUp hS (roundedPowUpper S x (n/2)*roundedSqrtUpper S x)
      rw [Rat.cast_mul] at hr
      exact hmul.trans hr

end QuadraticTangZhang
