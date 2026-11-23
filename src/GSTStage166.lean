import GSTStage165

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36 GSTStage37

namespace GSTStage166

noncomputable def fixedSeed (B : ℝ) (hB : 0 ≤ B) : StateData where
  u := fun _ => 0
  eta := 1 / 20
  B := B
  phiInitial := 1 / 2
  a := 1 / 10
  c := 1
  omegaInitial := 1 / 5
  rho := 1 / 20
  q := 1
  target := 1
  U := 1
  heta := by norm_num
  hB := hB
  hphiInitial := by norm_num
  ha := by norm_num
  hc := by norm_num
  homegaInitial := by norm_num
  hrho := by norm_num
  huMeas := measurable_const
  hu := by
    intro _t _ht
    constructor <;> norm_num

theorem fixed_exists_unique_optimal_for_every_source
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ y : StateData,
      (y.eta = 1 / 20 ∧ y.B = B ∧
        y.phiInitial = 1 / 2 ∧ y.a = 1 / 10 ∧
        y.c = 1 ∧ y.omegaInitial = 1 / 5 ∧
        y.rho = 1 / 20 ∧ y.q = 1 ∧
        y.target = 1 ∧ y.U = 1) ∧
      Continuous y.u ∧
      GSTStage138.CostateProperties y ∧
      GSTStage44.Clipping y (1 / 10) ∧
      (∀ t : ℝ, 0 ≤ t → S y t ≤ 0) ∧
      (∀ u : ℝ → ℝ,
        AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ u t ∧ u t ≤ y.U) →
        IntegrableOn (discountedCost y (1 / 10) u) (Ioi (0 : ℝ)) ∧
        IntegrableOn (gap y (1 / 10) u) (Ioi (0 : ℝ)) ∧
        ((∫ t in Ioi (0 : ℝ), gap y (1 / 10) u t) ≤
          objective y (1 / 10) y.u - objective y (1 / 10) u) ∧
        (objective y (1 / 10) u ≤ objective y (1 / 10) y.u) ∧
        (objective y (1 / 10) u = objective y (1 / 10) y.u →
          u =ᵐ[volume.restrict (Ioi (0 : ℝ))] y.u) ∧
        (¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] y.u) →
          objective y (1 / 10) u < objective y (1 / 10) y.u)) := by
  obtain ⟨y, hparams, hcont, hcostates, hclip, hS, hoptimal⟩ :=
    GSTStage165.fixed_exists_unique_optimal
      (fixedSeed B hB) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨y, hparams, hcont, hcostates, hclip, hS, hoptimal⟩

end GSTStage166

#print axioms GSTStage166.fixed_exists_unique_optimal_for_every_source
