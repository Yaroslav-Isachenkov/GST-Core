import GSTStage147

open GSTStage147

namespace GSTStage148

theorem saturated_profiles_solve_odes
    (P M F Z B : ℝ) (X : ℝ → ℝ) (t : ℝ)
    (hX : HasDerivAt X (X t / 20) t)
    (hpos : 0 < X t) :
    HasDerivAt (fun s => satResource F B (X s))
      (B - satResource F B (X t) / 20) t ∧
    HasDerivAt (fun s => satState P M F B (X s))
      (-satState P M F B (X t) / 10 +
        satResource F B (X t)) t ∧
    HasDerivAt (fun s => satP P M F B (X s))
      (3 / 20 * satP P M F B (X t) +
        2 * (satState P M F B (X t) - 1)) t ∧
    HasDerivAt (fun s => satZ P M F Z B (X s))
      (satZ P M F Z B (X t) / 10 -
        satP P M F B (X t)) t := by
  have hNZ : X t ≠ 0 := ne_of_gt hpos
  have hInv : HasDerivAt (fun s => 1 / X s)
      (-1 / (20 * X t)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div hX hNZ using 1
    all_goals field_simp [hNZ]
    all_goals ring
  have hInv2 := hInv.pow 2
  have hPow2 := hX.pow 2
  have hPow3 := hX.pow 3

  have hR :=
    (hasDerivAt_const t (20 * B)).add
      (hInv.const_mul (F - 20 * B))
  have hO :=
    ((hasDerivAt_const t (200 * B)).add
      (hInv.const_mul (20 * (F - 20 * B)))).add
      (hInv2.const_mul (satA P M B))
  have hP :=
    (((hasDerivAt_const t (40 / 3 * (1 - 200 * B))).sub
      (hInv.const_mul (200 * (F - 20 * B)))).sub
      (hInv2.const_mul (8 * satA P M B))).add
      (hPow3.const_mul (satC P M B))
  have hZ :=
    ((((hasDerivAt_const t (400 / 3 * (1 - 200 * B))).sub
      (hInv.const_mul (4000 / 3 * (F - 20 * B)))).sub
      (hInv2.const_mul (40 * satA P M B))).sub
      (hPow3.const_mul (20 * satC P M B))).add
      (hPow2.const_mul (satD M Z B))

  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hR using 1
    all_goals
      first
      | (apply funext
         intro s
         dsimp [satResource]
         ring)
      | (dsimp [satResource]
         field_simp [hNZ]
         ring)
  · convert hO using 1
    all_goals
      first
      | (apply funext
         intro s
         dsimp [satState, satResource, satA]
         ring)
      | (dsimp [satState, satResource, satA]
         field_simp [hNZ]
         ring)
  · convert hP using 1
    all_goals
      first
      | (apply funext
         intro s
         dsimp [satP, satState, satA, satC]
         ring)
      | (dsimp [satP, satState, satA, satC]
         field_simp [hNZ]
         ring)
  · convert hZ using 1
    all_goals
      first
      | (apply funext
         intro s
         dsimp [satZ, satP, satA, satC, satD]
         ring)
      | (dsimp [satZ, satP, satA, satC, satD]
         field_simp [hNZ]
         ring)

end GSTStage148

#print axioms GSTStage148.saturated_profiles_solve_odes
