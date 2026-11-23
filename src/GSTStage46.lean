import GSTStage45

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage46

theorem control_zero_of_p_nonpos
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 ≤ t) (hp : p x t ≤ 0) :
    x.u t = 0 := by
  have hz : 0 ≤ z x t :=
    GSTStage44.candidate_z_nonneg x r hr hi hclip t ht
  have hd : d x t ≤ 0 := by
    change x.c * p x t - x.eta * z x t ≤ 0
    exact sub_nonpos.mpr
      (le_trans (mul_nonpos_of_nonneg_of_nonpos x.hc hp)
        (mul_nonneg x.heta.le hz))
  have hres : 0 ≤ resource x.u x.eta x.B x.phiInitial t :=
    (resource_positive x.u x.eta x.B x.phiInitial t x.hB hi ht).le
  have hquot :
      (resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hres hd)
      (mul_nonneg (by norm_num) hr.le)
  have hmin :
      min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)) ≤ 0 :=
    le_trans (min_le_right _ _) hquot
  rw [hclip t ht, max_eq_left hmin]

noncomputable def discountedP (x : StateData) (t : ℝ) : ℝ :=
  Real.exp (-(x.rho + x.a) * t) * p x t

noncomputable def discountedPInput (x : StateData) (t : ℝ) : ℝ :=
  Real.exp (-(x.rho + x.a) * t) *
    (2 * x.q * (state x t - x.target))

theorem discounted_p_ac
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (discountedP x) 0 T := by
  have hp : AbsolutelyContinuousOnInterval (p x) 0 T :=
    (GSTStage28.p_solution (toCostateData x) T hT).1
  exact (GSTStage30.linear_exponential_ac (-(x.rho + x.a)) T).mul hp

theorem discounted_p_derivative_ae
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (discountedP x) (discountedPInput x t) t := by
  have hp :
      ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (p x)
          ((x.rho + x.a) * p x t +
            2 * x.q * (state x t - x.target)) t :=
    (GSTStage28.p_solution (toCostateData x) T hT).2
  filter_upwards [hp] with t hpt
  intro ht
  have he := ((hasDerivAt_id t).const_mul (-(x.rho + x.a))).exp
  have h := he.mul (hpt ht)
  convert h using 1
  dsimp [discountedP, discountedPInput, Pi.mul_apply, id_eq]
  ring

theorem discounted_p_integral_identity
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, discountedPInput x t) =
      discountedP x T - p x 0 := by
  have h := GSTStage08.ac_integral_identity
    (discountedP x) (discountedPInput x) 0 T
    (discounted_p_ac x T hT)
    (discounted_p_derivative_ae x T hT)
  simpa only [discountedP, mul_zero, Real.exp_zero, one_mul] using h

theorem discounted_p_tendsto_zero
    (x : StateData) :
    Tendsto (discountedP x) atTop (𝓝 0) := by
  obtain ⟨P, _hP, hp⟩ := GSTStage35.p_linear_growth x
  have hk : 0 < x.rho + x.a :=
    lt_of_lt_of_le x.hrho (le_add_of_nonneg_right x.ha)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_
    (GSTStage20.discounted_polynomial_tendsto_zero
      (x.rho + x.a) P 1 hk)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change ‖Real.exp (-(x.rho + x.a) * t) * p x t‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(x.rho + x.a) * t) * |p x t|
        ≤ Real.exp (-(x.rho + x.a) * t) * (P * (1 + t)) :=
      mul_le_mul_of_nonneg_left (hp t ht) (Real.exp_pos _).le
    _ = P * (Real.exp (-(x.rho + x.a) * t) +
        t ^ (1 : ℕ) * Real.exp (-(x.rho + x.a) * t)) := by ring

#print axioms control_zero_of_p_nonpos
#print axioms discounted_p_ac
#print axioms discounted_p_derivative_ae
#print axioms discounted_p_integral_identity
#print axioms discounted_p_tendsto_zero

end GSTStage46
