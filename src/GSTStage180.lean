import GSTStage179

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage180

noncomputable def liftedResource
    (u : ℝ → ℝ) (eta B initial t : ℝ) : ℝ :=
  resource u eta 0 initial t + B * t

noncomputable def liftedControl
    (u : ℝ → ℝ) (eta B initial t : ℝ) : ℝ :=
  (resource u eta 0 initial t / liftedResource u eta B initial t) * u t

theorem source_lift_initial
    (u : ℝ → ℝ) (eta B initial : ℝ) (hi : 0 < initial) :
    liftedResource u eta B initial 0 = initial ∧
    liftedControl u eta B initial 0 = u 0 := by
  simp [liftedResource, liftedControl, resource_initial, ne_of_gt hi]

theorem source_lift_control_measurable
    (u : ℝ → ℝ) (eta B initial : ℝ) (hu : Measurable u) :
    Measurable (liftedControl u eta B initial) := by
  have hF := GSTStage31.resource_measurable u eta 0 initial hu
  have hG : Measurable (liftedResource u eta B initial) :=
    hF.add (measurable_const.mul measurable_id)
  exact (hF.div hG).mul hu

theorem source_lift_bounds_and_flow
    (u : ℝ → ℝ) (eta B initial t : ℝ)
    (hi : 0 < initial) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hu : 0 ≤ u t) :
    0 < liftedResource u eta B initial t ∧
    (0 ≤ liftedControl u eta B initial t ∧
      liftedControl u eta B initial t ≤ u t) ∧
    liftedResource u eta B initial t * liftedControl u eta B initial t =
      resource u eta 0 initial t * u t := by
  have hF : 0 < resource u eta 0 initial t :=
    resource_positive u eta 0 initial t le_rfl hi ht
  have hBt : 0 ≤ B * t := mul_nonneg hB ht
  have hG : 0 < liftedResource u eta B initial t :=
    add_pos_of_pos_of_nonneg hF hBt
  have hFG : resource u eta 0 initial t ≤ liftedResource u eta B initial t :=
    le_add_of_nonneg_right hBt
  have hratio0 :
      0 ≤ resource u eta 0 initial t / liftedResource u eta B initial t :=
    div_nonneg hF.le hG.le
  have hratio1 :
      resource u eta 0 initial t / liftedResource u eta B initial t ≤ 1 := by
    apply (div_le_iff₀ hG).2
    simpa only [one_mul] using hFG
  have hv0 : 0 ≤ liftedControl u eta B initial t :=
    mul_nonneg hratio0 hu
  have hvle : liftedControl u eta B initial t ≤ u t := by
    have hm := mul_le_mul_of_nonneg_right hratio1 hu
    simpa only [liftedControl, one_mul] using hm
  have hcancel :
      (resource u eta 0 initial t / liftedResource u eta B initial t) *
        liftedResource u eta B initial t = resource u eta 0 initial t :=
    div_mul_cancel₀ _ (ne_of_gt hG)
  refine ⟨hG, ⟨hv0, hvle⟩, ?_⟩
  calc
    liftedResource u eta B initial t * liftedControl u eta B initial t =
        ((resource u eta 0 initial t / liftedResource u eta B initial t) *
          liftedResource u eta B initial t) * u t := by
      dsimp only [liftedControl]
      ring
    _ = resource u eta 0 initial t * u t := by rw [hcancel]

theorem source_lift_control_strict
    (u : ℝ → ℝ) (eta B initial t : ℝ)
    (hi : 0 < initial) (hB : 0 < B) (ht : 0 < t)
    (hu : 0 < u t) :
    liftedControl u eta B initial t < u t := by
  have hG :=
    (source_lift_bounds_and_flow u eta B initial t hi hB.le ht.le hu.le).1
  have hFG : resource u eta 0 initial t < liftedResource u eta B initial t :=
    lt_add_of_pos_right _ (mul_pos hB ht)
  have hratio :
      resource u eta 0 initial t / liftedResource u eta B initial t < 1 := by
    apply (div_lt_iff₀ hG).2
    simpa only [one_mul] using hFG
  have hm := mul_lt_mul_of_pos_right hratio hu
  simpa only [liftedControl, one_mul] using hm

end GSTStage180

#print axioms GSTStage180.source_lift_initial
#print axioms GSTStage180.source_lift_control_measurable
#print axioms GSTStage180.source_lift_bounds_and_flow
#print axioms GSTStage180.source_lift_control_strict
