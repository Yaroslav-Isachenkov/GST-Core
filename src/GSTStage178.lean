import GSTStage177

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage178

theorem resource_linear_upper
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hi : 0 ≤ initial)
    (hu : IntervalIntegrable u volume 0 T)
    (hu0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    resource u eta B initial T ≤ initial + B * T := by
  have hAC := GSTStage12.resource_ac u eta B initial T hu
  have hODE := GSTStage12.resource_ode_ae u eta B initial T hu
  have hderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      deriv (resource u eta B initial) t ≤ B := by
    filter_upwards [hODE] with t hd
    intro ht
    have ht' : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT] using ht
    rw [(hd ht).deriv]
    exact sub_le_self B
      (mul_nonneg (mul_nonneg heta (hu0 t ht'.1))
        (GSTStage30.resource_nonneg u eta B initial t hB hi ht'.1))
  have h := GSTStage30.ac_endpoint_upper
    (resource u eta B initial) B T hT hAC hderiv
  simpa only [resource_initial] using h

theorem effort_threshold_necessary_at_corner
    (u : ℝ → ℝ) (eta B a c h s U : ℝ)
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U)
    (hkeep : ∀ t : ℝ, 0 ≤ t →
      h ≤ omega u eta B s a c h t) :
    a * h / (c * s) ≤ U := by
  have hu : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable u U T hT hmeas hbound
  have hu0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t :=
    fun t ht => (hbound t ht).1
  have hU : 0 ≤ U :=
    (hbound 0 le_rfl).1.trans (hbound 0 le_rfl).2
  by_contra hbad
  have hcross : U * (c * s) < a * h :=
    (lt_div_iff₀ (mul_pos hc hs)).mp (lt_of_not_ge hbad)
  let D : ℝ := a * h - c * s * U
  let K : ℝ := c * B * U
  have hD : 0 < D := by
    dsimp [D]
    nlinarith only [hcross]
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hc.le hB) hU
  have hden : 0 < 2 * (K + 1) := by positivity
  let T : ℝ := D / (2 * (K + 1))
  have hT : 0 < T := div_pos hD hden
  have hTD : T * (2 * (K + 1)) = D := by
    dsimp only [T]
    exact div_mul_cancel₀ D (ne_of_gt hden)
  have hgap : 0 < D - K * T := by
    nlinarith only [hTD, hT, mul_nonneg hK hT.le]
  let L : ℝ := -a * h + c * (s + B * T) * U
  have hL : L < 0 := by
    have heq : L = -(D - K * T) := by
      dsimp [L, D, K]
      ring
    rw [heq]
    exact neg_neg_of_pos hgap
  have hsol := GSTStage29.omega_solution u eta B s a c h T (hu T hT.le)
  have hderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      deriv (omega u eta B s a c h) t ≤ L := by
    filter_upwards [hsol.2] with t hd
    intro ht
    have ht' : t ∈ Icc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT.le] using ht
    have hF : resource u eta B s t ≤ s + B * T := by
      calc
        resource u eta B s t ≤ s + B * t :=
          resource_linear_upper u eta B s t ht'.1
            heta hB hs.le (hu t ht'.1) hu0
        _ ≤ s + B * T :=
          by
            linarith only [mul_le_mul_of_nonneg_left ht'.2 hB]
    have hFT : 0 ≤ s + B * T :=
      add_nonneg hs.le (mul_nonneg hB hT.le)
    have hprod :
        resource u eta B s t * u t ≤ (s + B * T) * U := by
      calc
        resource u eta B s t * u t ≤ (s + B * T) * u t :=
          mul_le_mul_of_nonneg_right hF (hu0 t ht'.1)
        _ ≤ (s + B * T) * U :=
          mul_le_mul_of_nonneg_left (hbound t ht'.1).2 hFT
    have hdecay :
        -a * omega u eta B s a c h t ≤ -a * h :=
      mul_le_mul_of_nonpos_left (hkeep t ht'.1) (neg_nonpos.mpr ha.le)
    have hforce := mul_le_mul_of_nonneg_left hprod hc.le
    rw [(hd ht).deriv]
    simpa only [L, mul_assoc] using add_le_add hdecay hforce
  have hend := GSTStage30.ac_endpoint_upper
    (omega u eta B s a c h) L T hT.le hsol.1 hderiv
  rw [omega_initial] at hend
  have hfinal := hkeep T hT.le
  have hnegative : L * T < 0 := mul_neg_of_neg_of_pos hL hT
  linarith only [hend, hfinal, hnegative]

end GSTStage178

#print axioms GSTStage178.resource_linear_upper
#print axioms GSTStage178.effort_threshold_necessary_at_corner
