import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GSTStage01

-- PDF, theorem 2: F(x) >= 0 for x > 0.
theorem F_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ x - 1 - Real.log x := by
  have h := Real.log_le_sub_one_of_pos hx
  linarith

-- PDF, theorem 2: G(x) >= 0 for x > 0.
theorem G_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ Real.log x + x⁻¹ - 1 := by
  have h := Real.one_sub_inv_le_log_of_pos hx
  linarith

-- Algebraic identity used in equation (17).
theorem FG_identity (x : ℝ) (hx : 0 < x) :
    (x - 1 - Real.log x) - (x - 1)^2 / x =
      -(Real.log x + x⁻¹ - 1) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

-- Pointwise sign of the integrand in equation (17).
-- This is NOT yet the integral theorem or global optimality.
theorem remainder_nonpos
    (c phi S B d x : ℝ)
    (hc : 0 ≤ c) (hphi : 0 ≤ phi) (hS : S ≤ 0)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hx : 0 < x) :
    c * phi * S * (x - 1 - Real.log x)
      - B * d * (Real.log x + x⁻¹ - 1) ≤ 0 := by
  have hfirst : c * phi * S * (x - 1 - Real.log x) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc hphi) hS)
      (F_nonneg x hx)
  have hsecond : 0 ≤ B * d * (Real.log x + x⁻¹ - 1) :=
    mul_nonneg (mul_nonneg hB hd) (G_nonneg x hx)
  linarith

#print axioms F_nonneg
#print axioms G_nonneg
#print axioms FG_identity
#print axioms remainder_nonpos

end GSTStage01
