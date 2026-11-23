import GSTStage28
import GSTStage30

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage31

theorem cumulative_measurable
    (u : ℝ → ℝ) (eta : ℝ) (hu : Measurable u) :
    Measurable (GSTStage11.cumulative u eta) := by
  exact measurable_const.mul
    (GSTStage24.interval_primitive_measurable u 0 hu)

theorem resource_measurable
    (u : ℝ → ℝ) (eta B initial : ℝ)
    (hu : Measurable u) :
    Measurable (GSTStage11.resource u eta B initial) := by
  have hA := cumulative_measurable u eta hu
  have he : Measurable
      (fun t => Real.exp (GSTStage11.cumulative u eta t)) :=
    Real.continuous_exp.measurable.comp hA
  have hI := GSTStage24.interval_primitive_measurable
    (fun t => Real.exp (GSTStage11.cumulative u eta t)) 0 he
  exact (Real.continuous_exp.measurable.comp hA.neg).mul
    (measurable_const.add (measurable_const.mul hI))

theorem omega_measurable
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial : ℝ)
    (hu : Measurable u) :
    Measurable (GSTStage29.omega u eta B phiInitial a c omegaInitial) := by
  have hr := resource_measurable u eta B phiInitial hu
  have hf : Measurable
      (GSTStage29.resourceForcing u eta B phiInitial c) :=
    measurable_const.mul (hr.mul hu)
  have he : Measurable (fun t : ℝ => Real.exp (a * t)) :=
    Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)
  have hw : Measurable
      (GSTStage29.weightedInput
        (GSTStage29.resourceForcing u eta B phiInitial c) a) :=
    he.mul hf
  have hI := GSTStage24.interval_primitive_measurable
    (GSTStage29.weightedInput
      (GSTStage29.resourceForcing u eta B phiInitial c) a) 0 hw
  have heneg : Measurable (fun t : ℝ => Real.exp (-a * t)) :=
    Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id)
  exact heneg.mul (measurable_const.add hI)

-- Finite-interval continuity implies continuity on the whole half-line.
theorem continuousOn_nonnegative_of_finite
    (f : ℝ → ℝ)
    (h : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn f (uIcc (0 : ℝ) T)) :
    ContinuousOn f (Ici (0 : ℝ)) := by
  apply continuousOn_of_locally_continuousOn
  intro t ht
  have ht0 : 0 ≤ t := ht
  have hT : 0 ≤ t + 1 := by linarith
  refine ⟨Iio (t + 1), isOpen_Iio, ?_, ?_⟩
  · change t < t + 1
    linarith
  · apply (h (t + 1) hT).mono
    intro s hs
    rw [uIcc_of_le hT]
    exact ⟨hs.1, le_of_lt hs.2⟩

-- Only control, parameters and initial conditions are inputs.
-- No regularity or growth assumptions on an independent omega are used.
structure StateData where
  u : ℝ → ℝ
  eta : ℝ
  B : ℝ
  phiInitial : ℝ
  a : ℝ
  c : ℝ
  omegaInitial : ℝ
  rho : ℝ
  q : ℝ
  target : ℝ
  U : ℝ
  heta : 0 < eta
  hB : 0 ≤ B
  hphiInitial : 0 ≤ phiInitial
  ha : 0 ≤ a
  hc : 0 ≤ c
  homegaInitial : 0 ≤ omegaInitial
  hrho : 0 < rho
  huMeas : Measurable u
  hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U

noncomputable def state (x : StateData) : ℝ → ℝ :=
  GSTStage29.omega
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial

theorem state_continuousOn
    (x : StateData) :
    ContinuousOn (state x) (Ici (0 : ℝ)) := by
  apply continuousOn_nonnegative_of_finite
  intro T hT
  have hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ x.u t ∧ x.u t ≤ x.U := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => x.hu t ht.1)
  have hu := GSTStage14.admissible_control_integrable
    x.u x.U T hT x.huMeas hb
  exact (GSTStage29.omega_solution
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hu).1.continuousOn

theorem state_linear_growth
    (x : StateData) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t → |state x t| ≤ M * (1 + t) := by
  exact GSTStage30.admissible_omega_linear_growth
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.U
    x.heta x.ha x.hB x.hphiInitial x.hc x.homegaInitial
    x.huMeas x.hu

-- Choice selects a bound whose existence has already been proved.
-- It introduces no new growth hypothesis.
noncomputable def growthConstant (x : StateData) : ℝ :=
  Classical.choose (state_linear_growth x)

noncomputable def toCostateData
    (x : StateData) : GSTStage28.CostateData where
  u := x.u
  omega := state x
  eta := x.eta
  rho := x.rho
  a := x.a
  c := x.c
  q := x.q
  target := x.target
  U := x.U
  M := growthConstant x
  heta := le_of_lt x.heta
  hrho := x.hrho
  hdecay := lt_of_lt_of_le x.hrho (le_add_of_nonneg_right x.ha)
  hc := x.hc
  hU := le_trans (x.hu 0 le_rfl).1 (x.hu 0 le_rfl).2
  hM := (Classical.choose_spec (state_linear_growth x)).1
  huMeas := x.huMeas
  hOmegaMeas := omega_measurable
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.huMeas
  hu := x.hu
  hcont := state_continuousOn x
  hOmega := (Classical.choose_spec (state_linear_growth x)).2

noncomputable def p (x : StateData) : ℝ → ℝ :=
  GSTStage22.pCostate (state x) x.rho x.a x.q x.target

noncomputable def z (x : StateData) : ℝ → ℝ :=
  GSTStage23.zCostate x.u (p x) x.eta x.rho x.c

noncomputable def d (x : StateData) : ℝ → ℝ :=
  GSTStage18.canonicalD (p x) (z x) x.c x.eta

noncomputable def S (x : StateData) : ℝ → ℝ :=
  GSTStage18.canonicalS (p x) (state x) x.a x.q x.target

-- All four conclusions concern the state constructed from the dynamics.
theorem state_costates_verified
    (x : StateData) :
    (∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval (d x) 0 T) ∧
    (∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (d x)
        ((x.rho + x.eta * x.u t) * d x t + x.c * S x t) t) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → |d x t| ≤ C * (1 + t)) ∧
    Tendsto
      (fun t => GSTStage19.weight x.u x.eta x.rho t * d x t)
      atTop (𝓝 0) := by
  exact ⟨
    (fun T hT => GSTStage28.d_ac (toCostateData x) T hT),
    GSTStage28.d_ode_ae (toCostateData x),
    GSTStage28.d_linear_growth (toCostateData x),
    GSTStage28.weighted_limit (toCostateData x)
  ⟩

-- S <= 0 is deliberately retained as an explicit condition.
theorem state_d_nonneg
    (x : StateData)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ d x t := by
  exact GSTStage28.d_nonneg (toCostateData x) hS

#print axioms cumulative_measurable
#print axioms resource_measurable
#print axioms omega_measurable
#print axioms continuousOn_nonnegative_of_finite
#print axioms state_continuousOn
#print axioms state_linear_growth
#print axioms state_costates_verified
#print axioms state_d_nonneg

end GSTStage31
