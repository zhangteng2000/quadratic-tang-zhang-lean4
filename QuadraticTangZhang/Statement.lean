import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Statements with the correct convention at a common zero of p and p'

The main statements below are propositions, not proofs. In particular, writing
the target as a definition does not claim that the general theorem is proved.
-/

namespace QuadraticTangZhang
open Polynomial
open scoped BigOperators

noncomputable def reciprocalEnergy (a z : ℂ) : ENNReal :=
  (ENNReal.ofReal (‖a - z‖ ^ 2))⁻¹

/-- A multiset is essential: critical points are counted with multiplicity. -/
noncomputable def criticalEnergy (p : ℂ[X]) (a : ℂ) : ENNReal :=
  (p.derivative.roots.map (reciprocalEnergy a)).sum

def RootsInClosedDisk (p : ℂ[X]) : Prop := ∀ z ∈ p.roots, ‖z‖ ≤ 1

def Extremal (p : ℂ[X]) : Prop :=
  ∃ c ω : ℂ, c ≠ 0 ∧ ‖ω‖ = 1 ∧ p = C c * (X ^ p.natDegree - C ω)

/-- The unrestricted main theorem of the manuscript: an explicit formal target. -/
def MainStatement : Prop :=
  ∀ (p : ℂ[X]), 2 ≤ p.natDegree → RootsInClosedDisk p →
    ∀ a ∈ p.roots, (p.natDegree - 1 : ℕ) ≤ criticalEnergy p a

/-- The full equality classification: an explicit formal target. -/
def EqualityStatement : Prop :=
  ∀ (p : ℂ[X]), 2 ≤ p.natDegree → RootsInClosedDisk p →
    ∀ a ∈ p.roots, criticalEnergy p a = (p.natDegree - 1 : ℕ) ↔ Extremal p

@[simp] theorem reciprocalEnergy_self (a : ℂ) : reciprocalEnergy a a = ⊤ := by
  simp [reciprocalEnergy]

theorem reciprocalEnergy_eq_top_iff (a z : ℂ) : reciprocalEnergy a z = ⊤ ↔ a = z := by
  simp [reciprocalEnergy, ENNReal.inv_eq_top, sub_eq_zero]

theorem criticalEnergy_eq_top_of_mem {p : ℂ[X]} {a : ℂ}
    (ha : a ∈ p.derivative.roots) : criticalEnergy p a = ⊤ := by
  apply top_unique
  have hmem : (⊤ : ENNReal) ∈ p.derivative.roots.map (reciprocalEnergy a) :=
    Multiset.mem_map.mpr ⟨a, ha, reciprocalEnergy_self a⟩
  exact Multiset.le_sum_of_mem hmem

theorem main_at_common_zero {p : ℂ[X]} {a : ℂ}
    (ha : a ∈ p.derivative.roots) : (p.natDegree - 1 : ℕ) < criticalEnergy p a := by
  rw [criticalEnergy_eq_top_of_mem ha]
  exact ENNReal.natCast_lt_top _

end QuadraticTangZhang
