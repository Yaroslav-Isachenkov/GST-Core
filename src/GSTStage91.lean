import GSTStage90

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage91

theorem L2_tendsto_of_ae_uniform_error
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n)
    (herr : ∀ n, ∀ᵐ t ∂μ, ‖v n t - w t‖ ≤ e n)
    (hzero : Tendsto e atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 w) := by
  let K : ℝ := ((μ Set.univ) ^ (2 : ENNReal).toReal⁻¹).toReal
  have hb (n : ℕ) : ‖v n - w‖ ≤ K * e n := by
    have hae : ∀ᵐ t ∂μ, ‖(v n - w) t‖ ≤ e n := by
      filter_upwards [Lp.coeFn_sub (v n) w, herr n] with t ht hb
      simpa only [ht, Pi.sub_apply] using hb
    have hfinite :
        (μ Set.univ) ^ (2 : ENNReal).toReal⁻¹ *
          ENNReal.ofReal (e n) ≠ ⊤ := by
      finiteness
    rw [Lp.norm_def]
    calc
      (eLpNorm (fun t => (v n - w) t) 2 μ).toReal ≤
          ((μ Set.univ) ^ (2 : ENNReal).toReal⁻¹ *
            ENNReal.ofReal (e n)).toReal :=
        ENNReal.toReal_mono hfinite
          (eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hae)
      _ = K * e n := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (he n)]
  have hk : Tendsto (fun n => K * e n) atTop (𝓝 0) := by
    simpa using
      (show Tendsto (fun _ : ℕ => K) atTop (𝓝 K) from
        tendsto_const_nhds).mul hzero
  have hn : Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hb hk
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn

theorem interval_BC_to_L2_tendsto
    (T : ℝ)
    (F : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (Flim : BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ)
    (f : ℕ → ℝ → ℝ) (flim : ℝ → ℝ)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hflim : MemLp flim 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hF : ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      F n ⟨t, ht⟩ = f n t)
    (hFlim : ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      Flim ⟨t, ht⟩ = flim t)
    (hconv : Tendsto F atTop (𝓝 Flim)) :
    Tendsto (fun n => (hf n).toLp (f n))
      atTop (𝓝 (hflim.toLp flim)) := by
  have hzero : Tendsto (fun n => ‖F n - Flim‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => Flim) atTop (𝓝 Flim) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hconv.sub hc).norm
  apply L2_tendsto_of_ae_uniform_error
    (fun n => (hf n).toLp (f n)) (hflim.toLp flim)
    (fun n => ‖F n - Flim‖) (fun n => norm_nonneg _) ?_ hzero
  intro n
  filter_upwards [
    (hf n).coeFn_toLp,
    hflim.coeFn_toLp,
    ae_restrict_mem measurableSet_Icc
  ] with t ht hfLim htI
  rw [ht, hfLim]
  have hb := (F n - Flim).norm_coe_le_norm ⟨t, htI⟩
  change ‖F n ⟨t, htI⟩ - Flim ⟨t, htI⟩‖ ≤ ‖F n - Flim‖ at hb
  rw [hF n t htI, hFlim t htI] at hb
  exact hb

end GSTStage91

#print axioms GSTStage91.L2_tendsto_of_ae_uniform_error
#print axioms GSTStage91.interval_BC_to_L2_tendsto
