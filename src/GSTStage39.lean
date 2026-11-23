import GSTStage38

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage39

-- A representative of an a.e.-bounded control.
-- This is not the canonical feedback/clipping condition.
def boundedRepresentative
    (U : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  max 0 (min U (u t))

theorem representative_measurable
    (U : ℝ) (u : ℝ → ℝ) (hu : Measurable u) :
    Measurable (boundedRepresentative U u) := by
  exact measurable_const.max (measurable_const.min hu)

theorem representative_bounds
    (U : ℝ) (u : ℝ → ℝ) (hU : 0 ≤ U) :
    ∀ t : ℝ,
      0 ≤ boundedRepresentative U u t ∧
        boundedRepresentative U u t ≤ U := by
  intro t
  change 0 ≤ max 0 (min U (u t)) ∧ max 0 (min U (u t)) ≤ U
  exact ⟨le_max_left _ _, max_le hU (min_le_left _ _)⟩

theorem representative_eq_of_bounds
    (U : ℝ) (u : ℝ → ℝ) (t : ℝ)
    (hlo : 0 ≤ u t) (hhi : u t ≤ U) :
    boundedRepresentative U u t = u t := by
  unfold boundedRepresentative
  rw [min_eq_right hhi, max_eq_right hlo]

theorem representative_ae_on_Ioi
    (U : ℝ) (u : ℝ → ℝ)
    (hbound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    boundedRepresentative U u =ᵐ[volume.restrict (Ioi (0 : ℝ))] u := by
  change ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
    boundedRepresentative U u t = u t
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hbound] with t ht
  intro hmem
  change (0 : ℝ) < t at hmem
  exact representative_eq_of_bounds U u t
    (ht hmem.le).1 (ht hmem.le).2

theorem representative_ae_on_Icc
    (U : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hbound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    boundedRepresentative U u =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u := by
  change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
    boundedRepresentative U u t = u t
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hbound] with t ht
  intro hmem
  exact representative_eq_of_bounds U u t
    (ht hmem.1).1 (ht hmem.1).2

#print axioms representative_measurable
#print axioms representative_bounds
#print axioms representative_eq_of_bounds
#print axioms representative_ae_on_Ioi
#print axioms representative_ae_on_Icc

end GSTStage39
