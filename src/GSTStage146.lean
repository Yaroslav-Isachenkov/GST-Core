import GSTStage145

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57

namespace GSTStage146

theorem fixed_positive_saturated_maximum_with_bounds
    (x : StateData)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hphi : x.phiInitial = 1 / 2)
    (homega : x.omegaInitial = 1 / 5)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (s : ℝ) (hs : 0 ≤ s) (hpositive : 0 < S x s) :
    ∃ t : ℝ, 0 < t ∧ 0 < S x t ∧
      sRate x t = 0 ∧
      (∀ᶠ v in 𝓝 t, S x v ≤ S x t) ∧
      (let F := resource x.u x.eta x.B x.phiInitial t
       x.u t = 1 ∧
       F = 1 / 10 - 3 * p x t / 400 ∧
       (3 / 200 * S x t + 3 / 2000 * p x t -
         1 / 100 + 2 * x.B ≤ 0) ∧
       ((12 / 5 < p x t ∧ p x t < 20 / 3) ∧
        (1 / 20 < F ∧ F < 41 / 500) ∧
        (1 / 5 ≤ F * p x t ∧ F * p x t ≤ 1 / 3) ∧
        (0 ≤ z x t ∧ z x t ≤ 8 * p x t))) := by
  have hr : (0 : ℝ) < 1 / 10 := by norm_num
  have hi : 0 < x.phiInitial := by rw [hphi]; norm_num
  have haPos : 0 < x.a := by rw [ha]; norm_num
  have hqPos : 0 < x.q := by rw [hq]; norm_num
  have ho : 0 < x.omegaInitial := by rw [homega]; norm_num
  have hoTarget : x.omegaInitial < x.target := by
    rw [homega, htarget]
    norm_num
  have hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a) := by
    rw [homega, hrho, htarget, ha]
    norm_num
  obtain ⟨t, ht, hSt, hstationary, _huPositive, hlocal⟩ :=
    GSTStage58.candidate_positive_stationary_maximum
      x (1 / 10) hr hi haPos hqPos ho hthreshold hclip
      s hs hpositive
  have hFpos : 0 < resource x.u x.eta x.B x.phiInitial t :=
    GSTStage11.resource_positive
      x.u x.eta x.B x.phiInitial t x.hB hi ht.le
  have hbounds := GSTStage145.fixed_positive_local_maximum_bounds
    x t ha hc heta hrho hq hU htarget hi ho hoTarget hclip
    ht hFpos hSt hlocal
  exact ⟨t, ht, hSt, hstationary, hlocal, hbounds⟩

end GSTStage146

#print axioms GSTStage146.fixed_positive_saturated_maximum_with_bounds
