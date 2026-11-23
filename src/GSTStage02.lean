import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GSTStage02

-- Derivative of xi = phi / psi from the two resource equations.
-- Hypotheses explicitly require derivatives at the point t.
theorem ratio_derivative
    (phi psi : ℝ → ℝ) (t B eta u v : ℝ)
    (hpsi_pos : 0 < psi t)
    (hphi : HasDerivAt phi (B - eta * phi t * u) t)
    (hpsi : HasDerivAt psi (B - eta * psi t * v) t) :
    HasDerivAt (fun s => phi s / psi s)
      (B / psi t * (1 - phi t / psi t)
        - eta * (phi t / psi t) * (u - v)) t := by
  have hn : psi t ≠ 0 := ne_of_gt hpsi_pos
  convert hphi.div hpsi hn using 1
  all_goals
    field_simp
    ring

-- Chain rule for F(xi) = xi - 1 - log(xi).
theorem entropy_derivative
    (xi : ℝ → ℝ) (t velocity : ℝ)
    (hx : 0 < xi t)
    (hxi : HasDerivAt xi velocity t) :
    HasDerivAt (fun s => xi s - 1 - Real.log (xi s))
      ((1 - 1 / xi t) * velocity) t := by
  have hn : xi t ≠ 0 := ne_of_gt hx
  convert (hxi.sub_const 1).sub (hxi.log hn) using 1
  all_goals
    field_simp

-- Exact algebraic identity before integration in PDF equation (17).
-- x is xi; f is the candidate resource; du is u - u*.
theorem mixed_identity
    (x f eta B d du : ℝ)
    (hx : 0 < x) (hf : 0 < f) (he : 0 < eta) :
    d * f * (x - 1) * du =
      -(f * d) / eta *
        ((1 - 1 / x) * (B / f * (1 - x) - eta * x * du))
      - B * d / eta * ((x - 1)^2 / x) := by
  have hxn : x ≠ 0 := ne_of_gt hx
  have hfn : f ≠ 0 := ne_of_gt hf
  have hen : eta ≠ 0 := ne_of_gt he
  field_simp
  ring

#print axioms ratio_derivative
#print axioms entropy_derivative
#print axioms mixed_identity

end GSTStage02
