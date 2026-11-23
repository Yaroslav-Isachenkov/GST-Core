import GSTStage31

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage32

-- The candidate and comparison trajectory share B, eta and phiInitial.
-- The definition reuses the mixed term already used in stages16-18.
noncomputable def comparisonIntegrand
    (x : StateData) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  GSTStage16.mixed
    (GSTStage11.resource u x.eta x.B x.phiInitial)
    (GSTStage11.resource x.u x.eta x.B x.phiInitial)
    (d x) u x.u x.rho t

-- No clip condition is needed for this mixed-term inequality alone.
-- It will be needed separately for the objective comparison.
theorem state_finite_mixed_nonpos
    (x : StateData) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (hu : IntervalIntegrable u volume 0 T) :
    (∫ t in (0 : ℝ)..T, comparisonIntegrand x u t) ≤ 0 := by
  have hv : IntervalIntegrable x.u volume 0 T := by
    apply GSTStage14.admissible_control_integrable
      x.u x.U T hT x.huMeas
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => x.hu t ht.1)

  have hp := GSTStage28.p_solution (toCostateData x) T hT
  have hz := GSTStage28.z_solution (toCostateData x) T hT

  have ho : ContinuousOn (state x) (uIcc (0 : ℝ) T) := by
    apply (state_continuousOn x).mono
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact ht.1

  have hD : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ d x t := by
    intro t ht
    exact state_d_nonneg x hS t ht.1

  have hSlocal : ∀ t ∈ Icc (0 : ℝ) T, S x t ≤ 0 := by
    intro t ht
    exact hS t ht.1

  exact GSTStage18.canonical_finite_mixed_nonpos
    u x.u (p x) (z x) (state x)
    x.a x.c x.eta x.rho x.q x.target x.B x.phiInitial T
    hT x.heta x.hB hphiInitial x.hc hu hv
    hp.1 hz.1 ho hp.2 hz.2 hD hSlocal

-- The comparison control may satisfy its bounds only a.e.
-- on the finite interval.
theorem admissible_finite_mixed_nonpos
    (x : StateData) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ x.U) :
    (∫ t in (0 : ℝ)..T, comparisonIntegrand x u t) ≤ 0 := by
  exact state_finite_mixed_nonpos x u T hT hphiInitial hS
    (GSTStage14.admissible_control_integrable
      u x.U T hT huMeas huBound)

#print axioms state_finite_mixed_nonpos
#print axioms admissible_finite_mixed_nonpos

end GSTStage32
