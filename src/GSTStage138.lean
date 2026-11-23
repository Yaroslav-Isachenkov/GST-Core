import GSTStage137

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage36 GSTStage37

namespace GSTStage138

def CostateProperties (x : StateData) : Prop :=
  (∀ T : ℝ, 0 ≤ T →
    AbsolutelyContinuousOnInterval (p x) 0 T ∧
    AbsolutelyContinuousOnInterval (z x) 0 T) ∧
  (∀ᵐ t : ℝ, 0 ≤ t →
    HasDerivAt (p x)
      ((x.rho + x.a) * p x t +
        2 * x.q * (state x t - x.target)) t ∧
    HasDerivAt (z x)
      ((x.rho + x.eta * x.u t) * z x t -
        x.c * x.u t * p x t) t) ∧
  (∃ P Z : ℝ, 0 ≤ P ∧ 0 ≤ Z ∧
    ∀ t : ℝ, 0 ≤ t →
      |p x t| ≤ P * (1 + t) ∧
      |z x t| ≤ Z * (1 + t))

theorem canonical_costate_properties
    (x : StateData) : CostateProperties x := by
  let y := toCostateData x
  have hAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval (p x) 0 T ∧
      AbsolutelyContinuousOnInterval (z x) 0 T := by
    intro T hT
    exact ⟨(GSTStage28.p_solution y T hT).1,
      (GSTStage28.z_solution y T hT).1⟩
  have hODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (p x)
        ((x.rho + x.a) * p x t +
          2 * x.q * (state x t - x.target)) t ∧
      HasDerivAt (z x)
        ((x.rho + x.eta * x.u t) * z x t -
          x.c * x.u t * p x t) t := by
    apply GSTStage28.ae_nonnegative_of_ae_on_intervals
    intro T hT
    filter_upwards [(GSTStage28.p_solution y T hT).2,
      (GSTStage28.z_solution y T hT).2] with t hp hz ht
    exact ⟨hp ht, hz ht⟩
  obtain ⟨P, hP, hp⟩ := GSTStage22.p_linear_growth
    y.omega y.rho y.a y.q y.target y.M
    y.hdecay y.hM y.hcont y.hOmega
  have hpBound : ∀ t : ℝ, 0 ≤ t →
      |GSTStage28.pOf y t| ≤ P * (1 + t) := hp
  have hpMeas : Measurable (GSTStage28.pOf y) :=
    GSTStage24.p_measurable
      y.omega y.rho y.a y.q y.target y.hOmegaMeas
  have hmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun s => GSTStage23.zKernel y.u y.eta y.rho t (t + s) *
          (y.u (t + s) * GSTStage28.pOf y (t + s)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    intro t _
    exact GSTStage24.z_integrand_aestronglyMeasurable
      y.u (GSTStage28.pOf y) y.eta y.rho t y.huMeas hpMeas
  obtain ⟨Z, hZ, hz⟩ := GSTStage23.z_linear_growth
    y.u (GSTStage28.pOf y) y.eta y.rho y.c y.U P
    y.heta y.hrho y.hU hP y.hu hpBound hmeas
  refine ⟨hAC, hODE, P, Z, hP, hZ, ?_⟩
  intro t ht
  exact ⟨hp t ht, hz t ht⟩

theorem core_exists_optimal_with_necessary_conditions
    (k : GSTStage115.CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    ∃ y : StateData,
      GSTStage136.SameParameters (k.toStateData n hn) y ∧
      Continuous y.u ∧
      IntegrableOn
        (discountedCost (k.toStateData n hn) k.r y.u)
        (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ,
        AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ k.U) →
        IntegrableOn
          (discountedCost (k.toStateData n hn) k.r v)
          (Ioi (0 : ℝ)) ∧
        objective (k.toStateData n hn) k.r v ≤
          objective (k.toStateData n hn) k.r y.u) ∧
      CostateProperties y ∧
      (∀ t : ℝ, 0 ≤ t →
        y.u t = max 0 (min y.U
          ((resource y.u y.eta y.B y.phiInitial t * d y t) /
            (2 * k.r)))) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : ℝ, 0 ≤ v → v ≤ y.U →
        k.r * (v - y.u t) ^ 2 ≤
          GSTStage137.hamiltonian y k.r t (y.u t) -
            GSTStage137.hamiltonian y k.r t v ∧
        GSTStage137.hamiltonian y k.r t v ≤
          GSTStage137.hamiltonian y k.r t (y.u t)) := by
  obtain ⟨y, hparams, hcont, hint, hopt, hclip⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k n hn
  exact ⟨y, hparams, hcont, hint, hopt,
    canonical_costate_properties y, hclip,
    GSTStage137.hamiltonian_maximum_of_clipping y k.r k.hr hclip⟩

end GSTStage138

#print axioms GSTStage138.canonical_costate_properties
#print axioms GSTStage138.core_exists_optimal_with_necessary_conditions
