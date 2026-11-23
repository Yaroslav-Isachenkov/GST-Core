import GSTStage01
import GSTStage02

namespace GSTStage05

-- Pointwise balance derived from the resource equations and d equation.
-- phi: competitor resource; psi: candidate resource.
-- u and v: control values at t.
-- S: value of the auxiliary expression at t.
theorem weighted_entropy_balance
    (phi psi d : ℝ → ℝ)
    (t B eta rho c S u v : ℝ)
    (hphi_pos : 0 < phi t)
    (hpsi_pos : 0 < psi t)
    (hphi : HasDerivAt phi (B - eta * phi t * u) t)
    (hpsi : HasDerivAt psi (B - eta * psi t * v) t)
    (hd : HasDerivAt d ((rho + eta * v) * d t + c * S) t) :
    HasDerivAt
      (fun s => Real.exp (-rho * s) * (psi s * d s) *
        (phi s / psi s - 1 - Real.log (phi s / psi s)))
      (Real.exp (-rho * t) *
        (c * psi t * S *
            (phi t / psi t - 1 - Real.log (phi t / psi t))
          - B * d t *
            (Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1)
          - eta * d t * (phi t - psi t) * (u - v))) t := by
  have hp : phi t ≠ 0 := ne_of_gt hphi_pos
  have hs : psi t ≠ 0 := ne_of_gt hpsi_pos
  have hx : 0 < phi t / psi t := div_pos hphi_pos hpsi_pos

  have hratio := GSTStage02.ratio_derivative
    phi psi t B eta u v hpsi_pos hphi hpsi

  have hF := GSTStage02.entropy_derivative
    (fun s => phi s / psi s) t
    (B / psi t * (1 - phi t / psi t)
      - eta * (phi t / psi t) * (u - v))
    hx hratio

  have hw : HasDerivAt (fun s => psi s * d s)
      (rho * (psi t * d t) + B * d t + c * psi t * S) t := by
    convert hpsi.mul hd using 1
    all_goals ring

  have he := ((hasDerivAt_id t).const_mul (-rho)).exp

  convert (he.mul hw).mul hF using 1
  all_goals
    field_simp
    simp only [Pi.mul_apply, id_eq]
    ring

-- Nonnegative boundary expression when d >= 0.
-- At t=0 equal initial resources additionally make it zero.
theorem entropy_boundary_nonneg
    (rho t phi psi d : ℝ)
    (hphi : 0 < phi) (hpsi : 0 < psi) (hd : 0 ≤ d) :
    0 ≤ Real.exp (-rho * t) * (psi * d) *
      (phi / psi - 1 - Real.log (phi / psi)) := by
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg hpsi.le hd))
    (GSTStage01.F_nonneg (phi / psi) (div_pos hphi hpsi))

#print axioms weighted_entropy_balance
#print axioms entropy_boundary_nonneg

end GSTStage05
