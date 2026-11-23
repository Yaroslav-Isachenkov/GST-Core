import GSTStage135

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage36 GSTStage37

namespace GSTStage136

def SameParameters (x y : StateData) : Prop :=
  y.eta = x.eta ∧ y.B = x.B ∧
  y.phiInitial = x.phiInitial ∧ y.a = x.a ∧
  y.c = x.c ∧ y.omegaInitial = x.omegaInitial ∧
  y.rho = x.rho ∧ y.q = x.q ∧
  y.target = x.target ∧ y.U = x.U

theorem exists_continuous_optimal_self_clipping
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) :
    ∃ y : StateData,
      SameParameters x y ∧
      Continuous y.u ∧
      IntegrableOn (discountedCost x r y.u) (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ,
        AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ x.U) →
        IntegrableOn (discountedCost x r v) (Ioi (0 : ℝ)) ∧
        objective x r v ≤ objective x r y.u) ∧
      (∀ t : ℝ, 0 ≤ t →
        y.u t = max 0 (min y.U
          ((resource y.u y.eta y.B y.phiInitial t * d y t) /
            (2 * r)))) := by
  obtain ⟨u, huMeas, huBound, _huInt, huOptimal⟩ :=
    GSTStage114.exists_optimal_control x r hq hr.le
  let z : StateData :=
    { x with u := u, huMeas := huMeas, hu := huBound }
  have hzOptimal : ∀ v : ℝ → ℝ, Measurable v →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ z.U) →
      objective z r v ≤ objective z r z.u := by
    intro v hvMeas hvBound
    exact huOptimal v hvMeas hvBound
  let y := GSTStage131.continuousRepresentativeData z r
  obtain ⟨hyCont, _hyEq, _hyPhi, _hyState, _hyJ, hyOptimal, hyClip⟩ :=
    GSTStage131.optimal_representative_self_clipping z r hr hzOptimal
  have hparams : SameParameters x y :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hyBound : ∀ t : ℝ, 0 ≤ t →
      0 ≤ y.u t ∧ y.u t ≤ x.U := y.hu
  have hyInt : IntegrableOn (discountedCost x r y.u) (Ioi (0 : ℝ)) :=
    discounted_cost_integrable x r y.u y.huMeas hyBound
  refine ⟨y, hparams, hyCont, hyInt, ?_, hyClip⟩
  intro v hvMeas hvBound
  exact GSTStage132.optimality_extends_to_aemeasurable
    y r y.u hyOptimal v hvMeas hvBound

theorem core_exists_continuous_optimal_self_clipping
    (p : GSTStage115.CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    ∃ y : StateData,
      SameParameters (p.toStateData n hn) y ∧
      Continuous y.u ∧
      IntegrableOn
        (discountedCost (p.toStateData n hn) p.r y.u)
        (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ,
        AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ p.U) →
        IntegrableOn
          (discountedCost (p.toStateData n hn) p.r v)
          (Ioi (0 : ℝ)) ∧
        objective (p.toStateData n hn) p.r v ≤
          objective (p.toStateData n hn) p.r y.u) ∧
      (∀ t : ℝ, 0 ≤ t →
        y.u t = max 0 (min y.U
          ((resource y.u y.eta y.B y.phiInitial t * d y t) /
            (2 * p.r)))) := by
  exact exists_continuous_optimal_self_clipping
    (p.toStateData n hn) p.r p.hq.le p.hr

end GSTStage136

#print axioms GSTStage136.exists_continuous_optimal_self_clipping
#print axioms GSTStage136.core_exists_continuous_optimal_self_clipping
