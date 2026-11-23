import GSTStage114

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36 GSTStage37

namespace GSTStage115

theorem exists_optimal_control_ae
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    ∃ uStar : ℝ → ℝ, Measurable uStar ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ uStar t ∧ uStar t ≤ x.U) ∧
      IntegrableOn (discountedCost x r uStar) (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ, Measurable v →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ x.U) →
        objective x r v ≤ objective x r uStar) := by
  obtain ⟨uStar, huMeas, huBound, huInt, huOptimal⟩ :=
    GSTStage114.exists_optimal_control x r hq hr
  refine ⟨uStar, huMeas, huBound, huInt, ?_⟩
  intro v hvMeas hvBound
  obtain ⟨w, hwMeas, hwBound, hwAE, hwObjective⟩ :=
    GSTStage113.halfline_admissible_representative x v hvMeas hvBound
  have hle := huOptimal w hwMeas hwBound
  rw [hwObjective r] at hle
  exact hle

-- Parameters of Section 1 of GST: Coherent Core V2.
-- The population n is an external constant, not a control.
structure CoreParameters where
  a : ℝ
  c : ℝ
  b : ℝ
  eta : ℝ
  U : ℝ
  q : ℝ
  r : ℝ
  rho : ℝ
  target : ℝ
  phiInitial : ℝ
  omegaInitial : ℝ
  ha : 0 < a
  hc : 0 < c
  hb : 0 < b
  heta : 0 < eta
  hU : 0 < U
  hq : 0 < q
  hr : 0 < r
  hrho : 0 < rho
  htarget : 0 < target
  hphiInitial : 0 ≤ phiInitial
  homegaInitial : 0 ≤ omegaInitial

-- Zero is only a seed admissible control for the StateData interface.
noncomputable def CoreParameters.toStateData
    (p : CoreParameters) (n : ℝ) (hn : 0 ≤ n) : StateData where
  u := fun _ => 0
  eta := p.eta
  B := p.b * n
  phiInitial := p.phiInitial
  a := p.a
  c := p.c
  omegaInitial := p.omegaInitial
  rho := p.rho
  q := p.q
  target := p.target
  U := p.U
  heta := p.heta
  hB := mul_nonneg p.hb.le hn
  hphiInitial := p.hphiInitial
  ha := p.ha.le
  hc := p.hc.le
  homegaInitial := p.homegaInitial
  hrho := p.hrho
  huMeas := measurable_const
  hu := by
    intro t _
    exact ⟨le_rfl, p.hU.le⟩

theorem theorem1_existence
    (p : CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    ∃ uStar : ℝ → ℝ, Measurable uStar ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ uStar t ∧ uStar t ≤ p.U) ∧
      IntegrableOn
        (discountedCost (p.toStateData n hn) p.r uStar)
        (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ, Measurable v →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ p.U) →
        objective (p.toStateData n hn) p.r v ≤
          objective (p.toStateData n hn) p.r uStar) := by
  exact exists_optimal_control_ae
    (p.toStateData n hn) p.r p.hq.le p.hr.le

end GSTStage115

#print axioms GSTStage115.exists_optimal_control_ae
#print axioms GSTStage115.theorem1_existence
