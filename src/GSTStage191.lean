import GSTStage190

open GSTStage31

namespace GSTStage191

theorem fixed_candidate_state_bounds
    (x : StateData)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hphi : x.phiInitial = 1 / 2)
    (homega : x.omegaInitial = 1 / 5)
    (hclip : GSTStage44.Clipping x (1 / 10)) :
    ∀ t : ℝ, 0 ≤ t →
      0 < state x t ∧
      state x t ≤ 1 - p x t / 20 ∧
      1 - p x t / 20 < 1 := by
  have hS := GSTStage163.fixed_candidate_S_nonpos
    x ha hc heta hrho hq hU htarget hphi homega hclip
  intro t ht
  have hb := GSTStage190.candidate_state_bounds_of_S_nonpos
    x (1 / 10)
    (by norm_num)
    (by rw [hphi]; norm_num)
    (by rw [ha]; norm_num)
    (by rw [hq]; norm_num)
    (by rw [homega]; norm_num)
    (by rw [homega, htarget]; norm_num)
    hclip hS t ht
  have hcoef : x.a * p x t / (2 * x.q) = p x t / 20 := by
    rw [ha, hq]
    ring
  simpa only [htarget, hcoef] using hb

end GSTStage191

#print axioms GSTStage191.fixed_candidate_state_bounds
