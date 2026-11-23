import GSTStage187

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36 GSTStage37 GSTStage115 GSTStage185

namespace GSTStage188

theorem exists_strictly_ordered_optimizers_zero_resource
    (k : CoreParameters) (n : ℝ) (hn : 0 < n)
    (hi : k.phiInitial = 0) :
    ∃ u0 un : ℝ → ℝ,
      IsCoreOptimizer k 0 le_rfl u0 ∧
      IsCoreOptimizer k n hn.le un ∧
      Continuous u0 ∧ Continuous un ∧
      objective (k.toStateData 0 le_rfl) k.r u0 <
        objective (k.toStateData n hn.le) k.r un := by
  obtain ⟨y0, hparams0, hcont0, hint0, hopt0, _hclip0⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k 0 le_rfl
  obtain ⟨yn, hparamsN, hcontN, hintN, hoptN, _hclipN⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k n hn.le
  have hy0U : y0.U = k.U := hparams0.2.2.2.2.2.2.2.2.2
  have hynU : yn.U = k.U := hparamsN.2.2.2.2.2.2.2.2.2
  have hbound0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y0.u t ∧ y0.u t ≤ k.U := by
    simpa only [hy0U] using y0.hu
  have hboundN : ∀ t : ℝ, 0 ≤ t → 0 ≤ yn.u t ∧ yn.u t ≤ k.U := by
    simpa only [hynU] using yn.hu
  have hzeroStrict :
      objective (k.toStateData n hn.le) k.r (fun _ => 0) <
        objective (k.toStateData n hn.le) k.r yn.u := by
    by_contra hnot
    have hle :
        objective (k.toStateData n hn.le) k.r yn.u ≤
          objective (k.toStateData n hn.le) k.r (fun _ => 0) :=
      le_of_not_gt hnot
    have hnonoptimal :=
      GSTStage187.zero_control_not_optimal_of_positive_source
        (k.toStateData n hn.le) k.r rfl
        (mul_pos k.hb hn) k.hr k.ha k.hc k.hq k.htarget k.hU
    apply hnonoptimal
    intro v hvMeas hvBound
    have hvAE :
        ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ k.U :=
      ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => hvBound t (le_of_lt ht))
    exact le_trans (hoptN v hvMeas.aemeasurable hvAE).2 hle
  have hbase :
      objective (k.toStateData 0 le_rfl) k.r y0.u ≤
        objective (k.toStateData 0 le_rfl) k.r (fun _ => 0) :=
    GSTStage186.zero_control_optimal_of_zero_source_zero_resource
      (k.toStateData 0 le_rfl) k.r
      (by simp [CoreParameters.toStateData])
      hi k.hr.le y0.u y0.huMeas hbound0
  have hstrict :
      objective (k.toStateData 0 le_rfl) k.r y0.u <
        objective (k.toStateData n hn.le) k.r yn.u := by
    calc
      objective (k.toStateData 0 le_rfl) k.r y0.u
          ≤ objective (k.toStateData 0 le_rfl) k.r (fun _ => 0) := hbase
      _ = objective (k.toStateData n hn.le) k.r (fun _ => 0) :=
        (GSTStage186.zero_control_objective_independent_source k n hn.le).symm
      _ < objective (k.toStateData n hn.le) k.r yn.u := hzeroStrict
  refine ⟨y0.u, yn.u, ?_, ?_, hcont0, hcontN, hstrict⟩
  · exact ⟨y0.huMeas, hbound0, hint0,
      fun v hv hb => (hopt0 v hv hb).2⟩
  · exact ⟨yn.huMeas, hboundN, hintN,
      fun v hv hb => (hoptN v hv hb).2⟩

theorem exists_strictly_ordered_optimizers
    (k : CoreParameters) (n : ℝ) (hn : 0 < n) :
    ∃ u0 un : ℝ → ℝ,
      IsCoreOptimizer k 0 le_rfl u0 ∧
      IsCoreOptimizer k n hn.le un ∧
      Continuous u0 ∧ Continuous un ∧
      objective (k.toStateData 0 le_rfl) k.r u0 <
        objective (k.toStateData n hn.le) k.r un := by
  rcases k.hphiInitial.eq_or_lt with hzero | hpos
  · exact exists_strictly_ordered_optimizers_zero_resource k n hn hzero.symm
  · exact GSTStage185.exists_strictly_ordered_optimizers_positive_resource
      k n hn hpos

end GSTStage188

#print axioms GSTStage188.exists_strictly_ordered_optimizers_zero_resource
#print axioms GSTStage188.exists_strictly_ordered_optimizers
