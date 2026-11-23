import GSTStage188
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage37 GSTStage115 GSTStage185

namespace GSTStage189

def CoreAdmissible (k : CoreParameters) (u : ℝ → ℝ) : Prop :=
  AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) ∧
  (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u t ∧ u t ≤ k.U)

def attainableValues (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) : Set ℝ :=
  {v | ∃ u : ℝ → ℝ, CoreAdmissible k u ∧
    objective (k.toStateData n hn) k.r u = v}

noncomputable def coreValue (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) : ℝ :=
  sSup (attainableValues k n hn)

def measurableAttainableValues
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) : Set ℝ :=
  {v | ∃ u : ℝ → ℝ, Measurable u ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ k.U) ∧
    objective (k.toStateData n hn) k.r u = v}

theorem exists_continuous_core_optimizer
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    ∃ u : ℝ → ℝ, Continuous u ∧ IsCoreOptimizer k n hn u := by
  obtain ⟨y, hparams, hcont, hint, hopt, _hclip⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k n hn
  have hU : y.U = k.U := hparams.2.2.2.2.2.2.2.2.2
  have hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ y.u t ∧ y.u t ≤ k.U := by
    simpa only [hU] using y.hu
  exact ⟨y.u, hcont, y.huMeas, hbound, hint,
    fun v hv hb => (hopt v hv hb).2⟩

theorem optimizer_isGreatest
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n)
    (u : ℝ → ℝ) (hu : IsCoreOptimizer k n hn u) :
    IsGreatest (attainableValues k n hn)
      (objective (k.toStateData n hn) k.r u) := by
  have hbound :
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ u t ∧ u t ≤ k.U :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => hu.2.1 t (le_of_lt ht))
  refine ⟨⟨u, ⟨hu.1.aemeasurable, hbound⟩, rfl⟩, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact hu.2.2.2 w hw.1 hw.2

theorem coreValue_eq_of_optimizer
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n)
    (u : ℝ → ℝ) (hu : IsCoreOptimizer k n hn u) :
    coreValue k n hn = objective (k.toStateData n hn) k.r u := by
  exact (optimizer_isGreatest k n hn u hu).csSup_eq

theorem attainableValues_nonempty_bddAbove
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    (attainableValues k n hn).Nonempty ∧
      BddAbove (attainableValues k n hn) := by
  obtain ⟨u, _hcont, hu⟩ := exists_continuous_core_optimizer k n hn
  have hg := optimizer_isGreatest k n hn u hu
  exact ⟨⟨_, hg.1⟩, ⟨_, hg.2⟩⟩

theorem coreValue_eq_measurable_sup
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    coreValue k n hn = sSup (measurableAttainableValues k n hn) := by
  obtain ⟨u, _hcont, hu⟩ := exists_continuous_core_optimizer k n hn
  have hg : IsGreatest (measurableAttainableValues k n hn)
      (objective (k.toStateData n hn) k.r u) := by
    refine ⟨⟨u, hu.1, hu.2.1, rfl⟩, ?_⟩
    rintro v ⟨w, hwMeas, hwBound, rfl⟩
    apply hu.2.2.2 w hwMeas.aemeasurable
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => hwBound t (le_of_lt ht))
  exact (coreValue_eq_of_optimizer k n hn u hu).trans hg.csSup_eq.symm

theorem theorem7_strict_value_improvement
    (k : CoreParameters) (n : ℝ) (hn : 0 < n) :
    coreValue k 0 le_rfl < coreValue k n hn.le := by
  obtain ⟨u0, un, hu0, hun, _hcont0, _hcontN, hstrict⟩ :=
    GSTStage188.exists_strictly_ordered_optimizers k n hn
  rw [coreValue_eq_of_optimizer k 0 le_rfl u0 hu0,
    coreValue_eq_of_optimizer k n hn.le un hun]
  exact hstrict

end GSTStage189

#print axioms GSTStage189.exists_continuous_core_optimizer
#print axioms GSTStage189.optimizer_isGreatest
#print axioms GSTStage189.coreValue_eq_of_optimizer
#print axioms GSTStage189.attainableValues_nonempty_bddAbove
#print axioms GSTStage189.coreValue_eq_measurable_sup
#print axioms GSTStage189.theorem7_strict_value_improvement
