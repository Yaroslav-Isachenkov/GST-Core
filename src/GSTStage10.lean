import GSTStage09
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage10

-- Strict positivity plus continuity on a compact interval
-- yields a strictly positive uniform lower bound.
theorem positive_lower_bound
    (f : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (uIcc a b))
    (hp : ∀ t ∈ uIcc a b, 0 < f t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ uIcc a b, m ≤ f t := by
  exact isCompact_uIcc.exists_forall_le' hc hp

theorem inverse_distance_bound
    (m x y : ℝ) (hm : 0 < m)
    (hmx : m ≤ x) (hmy : m ≤ y) :
    dist x⁻¹ y⁻¹ ≤ (m * m)⁻¹ * dist x y := by
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hy : 0 < y := lt_of_lt_of_le hm hmy
  have hxy : m * m ≤ x * y :=
    mul_le_mul hmx hmy (le_of_lt hm) (le_of_lt hx)
  rw [Real.dist_eq, inv_sub_inv (ne_of_gt hx) (ne_of_gt hy),
      abs_div, abs_of_pos (mul_pos hx hy), abs_sub_comm]
  calc
    |x - y| / (x * y) ≤ |x - y| / (m * m) :=
      div_le_div_of_nonneg_left
        (abs_nonneg _) (mul_pos hm hm) hxy
    _ = (m * m)⁻¹ * dist x y := by
      rw [Real.dist_eq, div_eq_mul_inv, mul_comm]

theorem log_difference_upper_bound
    (m x y : ℝ) (hm : 0 < m)
    (hmx : m ≤ x) (hmy : m ≤ y) :
    Real.log x - Real.log y ≤ |x - y| / m := by
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hy : 0 < y := lt_of_lt_of_le hm hmy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at hlog
  have hid : x / y - 1 = (x - y) / y := by
    field_simp
  rw [hid] at hlog
  calc
    Real.log x - Real.log y ≤ (x - y) / y := hlog
    _ ≤ |x - y| / y :=
      div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hy)
    _ ≤ |x - y| / m :=
      div_le_div_of_nonneg_left (abs_nonneg _) hm hmy

theorem log_distance_bound
    (m x y : ℝ) (hm : 0 < m)
    (hmx : m ≤ x) (hmy : m ≤ y) :
    dist (Real.log x) (Real.log y) ≤ m⁻¹ * dist x y := by
  have hupper := log_difference_upper_bound m x y hm hmx hmy
  have hlower := log_difference_upper_bound m y x hm hmy hmx
  rw [abs_sub_comm y x] at hlower
  have habs : |Real.log x - Real.log y| ≤ |x - y| / m := by
    apply abs_le.mpr
    constructor
    · linarith
    · exact hupper
  simpa only [Real.dist_eq, div_eq_mul_inv, mul_comm] using habs

-- No inverse-distance bound is assumed here:
-- it is derived from positivity of the denominator.
theorem positive_ratio_ac
    (phi psi : ℝ → ℝ) (a b : ℝ)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hpsi : AbsolutelyContinuousOnInterval psi a b)
    (hpositive : ∀ t ∈ uIcc a b, 0 < psi t) :
    AbsolutelyContinuousOnInterval
      (fun t => phi t / psi t) a b := by
  obtain ⟨m, hm, hbound⟩ :=
    positive_lower_bound psi a b hpsi.continuousOn hpositive
  apply GSTStage09.ratio_ac phi psi a b ((m * m)⁻¹) hphi hpsi
  intro s hs t ht
  exact inverse_distance_bound
    m (psi s) (psi t) hm (hbound s hs) (hbound t ht)

-- No logarithm-distance bound is assumed here:
-- it is derived from positivity and continuity of the ratio.
theorem positive_entropy_ac
    (phi psi : ℝ → ℝ) (a b : ℝ)
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hpsi : AbsolutelyContinuousOnInterval psi a b)
    (hphi_pos : ∀ t ∈ uIcc a b, 0 < phi t)
    (hpsi_pos : ∀ t ∈ uIcc a b, 0 < psi t) :
    AbsolutelyContinuousOnInterval
      (fun t => phi t / psi t - 1 -
        Real.log (phi t / psi t)) a b := by
  have hratio := positive_ratio_ac phi psi a b hphi hpsi hpsi_pos
  have hratio_pos : ∀ t ∈ uIcc a b, 0 < phi t / psi t := by
    intro t ht
    exact div_pos (hphi_pos t ht) (hpsi_pos t ht)
  obtain ⟨m, hm, hbound⟩ :=
    positive_lower_bound
      (fun t => phi t / psi t) a b hratio.continuousOn hratio_pos
  apply GSTStage09.entropy_ac
    (fun t => phi t / psi t) a b m⁻¹ hratio
  intro s hs t ht
  exact log_distance_bound
    m (phi s / psi s) (phi t / psi t)
    hm (hbound s hs) (hbound t ht)

#print axioms positive_lower_bound
#print axioms inverse_distance_bound
#print axioms log_difference_upper_bound
#print axioms log_distance_bound
#print axioms positive_ratio_ac
#print axioms positive_entropy_ac

end GSTStage10
