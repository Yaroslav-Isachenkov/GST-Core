import GSTStage164

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36 GSTStage37

namespace GSTStage165

theorem fixed_exists_unique_optimal
    (x : StateData)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hphi : x.phiInitial = 1 / 2)
    (homega : x.omegaInitial = 1 / 5) :
    ∃ y : StateData,
      GSTStage136.SameParameters x y ∧
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
  have hqNonneg : 0 ≤ x.q := by
    rw [hq]
    norm_num
  obtain ⟨y, hparams, hcont, _hint, _hopt, hclip⟩ :=
    GSTStage136.exists_continuous_optimal_self_clipping
      x (1 / 10) hqNonneg (by norm_num)
  have hparamsCopy := hparams
  rcases hparamsCopy with
    ⟨hyeta, _hyB, hyphi, hya, hyc, hyomega,
      hyrho, hyq, hytarget, hyU⟩
  have hresult := GSTStage164.fixed_candidate_sufficiency_and_uniqueness
    y (hya.trans ha) (hyc.trans hc)
    (hyeta.trans heta) (hyrho.trans hrho)
    (hyq.trans hq) (hyU.trans hU) (hytarget.trans htarget)
    (hyphi.trans hphi) (hyomega.trans homega) hclip
  exact ⟨y, hparams, hcont,
    GSTStage138.canonical_costate_properties y,
    hclip, hresult.1, hresult.2⟩

end GSTStage165

#print axioms GSTStage165.fixed_exists_unique_optimal
