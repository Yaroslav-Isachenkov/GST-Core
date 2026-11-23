import GSTStage138

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36 GSTStage37

namespace GSTStage139

theorem core_exists_unique_optimal_under_thresholds
    (k : GSTStage115.CoreParameters) (n : ℝ) (hn : 0 ≤ n)
    (hi : 0 < k.phiInitial)
    (ho : 0 < k.omegaInitial)
    (hthreshold :
      k.omegaInitial < k.rho * k.target / (k.rho + k.a))
    (hdiscount : k.eta * k.U ≤ k.rho)
    (hrThreshold :
      k.a * k.q * k.target ^ 2 /
        (4 * k.U ^ 2 * (k.rho + k.a)) < k.r) :
    ∃ y : StateData,
      GSTStage136.SameParameters (k.toStateData n hn) y ∧
      Continuous y.u ∧
      GSTStage138.CostateProperties y ∧
      GSTStage44.Clipping y k.r ∧
      (∀ t : ℝ, 0 ≤ t → S y t ≤ 0) ∧
      (∀ u : ℝ → ℝ,
        AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ u t ∧ u t ≤ y.U) →
        IntegrableOn (discountedCost y k.r u) (Ioi (0 : ℝ)) ∧
        IntegrableOn (gap y k.r u) (Ioi (0 : ℝ)) ∧
        ((∫ t in Ioi (0 : ℝ), gap y k.r u t) ≤
          objective y k.r y.u - objective y k.r u) ∧
        (objective y k.r u ≤ objective y k.r y.u) ∧
        (objective y k.r u = objective y k.r y.u →
          u =ᵐ[volume.restrict (Ioi (0 : ℝ))] y.u) ∧
        (¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] y.u) →
          objective y k.r u < objective y k.r y.u)) := by
  obtain ⟨y, hparams, hcont, _hint, _hopt, hcostates, hclip, _hmax⟩ :=
    GSTStage138.core_exists_optimal_with_necessary_conditions k n hn
  have hparams' := hparams
  rcases hparams' with
    ⟨heta, _hB, hphi, ha, _hc, homega, hrho, hq, htarget, hU⟩
  change y.eta = k.eta at heta
  change y.phiInitial = k.phiInitial at hphi
  change y.a = k.a at ha
  change y.omegaInitial = k.omegaInitial at homega
  change y.rho = k.rho at hrho
  change y.q = k.q at hq
  change y.target = k.target at htarget
  change y.U = k.U at hU
  have hyU : 0 < y.U := by
    rw [hU]
    exact k.hU
  have hyi : 0 < y.phiInitial := by
    rw [hphi]
    exact hi
  have hya : 0 < y.a := by
    rw [ha]
    exact k.ha
  have hyq : 0 < y.q := by
    rw [hq]
    exact k.hq
  have hyo : 0 < y.omegaInitial := by
    rw [homega]
    exact ho
  have hyt :
      y.omegaInitial < y.rho * y.target / (y.rho + y.a) := by
    rw [homega, hrho, htarget, ha]
    exact hthreshold
  have hyd : y.eta * y.U ≤ y.rho := by
    rw [heta, hU, hrho]
    exact hdiscount
  have hyr :
      y.a * y.q * y.target ^ 2 /
        (4 * y.U ^ 2 * (y.rho + y.a)) < k.r := by
    rw [ha, hq, htarget, hU, hrho]
    exact hrThreshold
  have hresult := GSTStage66.candidate_sufficiency_and_uniqueness
    y k.r k.hr hyU hyi hya hyq hyo hyt hyd hyr hclip
  exact ⟨y, hparams, hcont, hcostates, hclip, hresult.1, hresult.2⟩

end GSTStage139

#print axioms GSTStage139.core_exists_unique_optimal_under_thresholds
