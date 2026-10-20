module

public import SKBarriers2.Corner.FrozenRowsMixedRecursion

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem epsilonMovingBellKJet_differentiates_of_normalized {ρ : ℝ} (hρ : ρ ≠ 0)
    (m : ℝ) (v x : ℝ → Vec3) (F : ℝ → ℝ → Vec3 → ℝ)
    (ε : ℝ) (i : Fin 3) {k : ℝ}
    (hA : MomentKJet.Differentiates (normalizedMovingBellKJet ρ m v x F ε i) k) :
    MomentKJet.Differentiates (epsilonMovingBellKJet m v x F ε i) k := by
  have he : epsilonMovingBellKJet m v x F ε i =
      fun t => (normalizedMovingBellKJet ρ m v x F ε i t).scale ((ρ^3)^(i.val+1)) :=
    funext (fun t => epsilonMovingBellKJet_eq_scale_normalized hρ m v x F ε i t)
  rw [he]
  exact hA.scale _

theorem normalizedMovingBellKJet_differentiates_of_contDiffAt
    (ρ m : ℝ) (v x : ℝ → Vec3) (F : ℝ → ℝ → Vec3 → ℝ)
    (ε : ℝ) (i : Fin 3) {k : ℝ}
    (hA : ContDiffAt ℝ 2 (normalizedMovingBellAverage ρ m v x F ε i) k) :
    MomentKJet.Differentiates (normalizedMovingBellKJet ρ m v x F ε i) k := by
  have hd : ContDiffAt ℝ 1 (deriv (normalizedMovingBellAverage ρ m v x F ε i)) k :=
    hA.derivWithin (by norm_num)
  exact ⟨(hA.differentiableAt (by norm_num)).hasDerivAt,
    (hd.differentiableAt (by norm_num)).hasDerivAt⟩

theorem scalarData_frozenRowsNormalizedJet_eq_cumulants {β l u : ℝ}
    (D : ScalarData β) (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, j < 11 → ∀ y : Vec3, ∀ g : ℝ,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      (∀ k ∈ frozenRowsKDomain, ∀ i : Fin 3,
        MomentKJet.Differentiates
          (fun t => frozenRowsMovingBellKJet β α a (r - h) h z ε j i y t g) k) →
      ∀ k ∈ frozenRowsKDomain, ∀ i : Fin 3,
        frozenRowsNormalizedJet β α a (r - h) h z ε j i y k g =
          epsilonLogCumulantsKJet (frozenPartitionMass a (j + 1))
            (fun t => frozenRowsMovingBellKJet β α a (r - h) h z ε j t y k g) i := by
  classical
  obtain ⟨h₀,hh₀,hhl,HJ⟩ := scalarData_frozen_suffix_joint_epsilon_jets D hl hu
  refine ⟨h₀,hh₀,?_⟩
  intro r hr h hh hhsmall z ε hε j hj y g
  dsimp only
  intro hA k hk i
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let K := terminalResidual β α (r - h) h z
  have hs : 0 < r - h := by linarith [hr.1,hhsmall.trans hhl]
  have ha : 0 < a := scalarData_cdf_pos_of_pos D hs
  have hm : 0 < frozenPartitionMass a (j + 1) := by
    unfold frozenPartitionMass
    split_ifs <;> positivity
  have hhalf (t : ℝ) (ht : t ∈ frozenRowsKDomain) : |t| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have HM (t : ℝ) (ht : t ∈ frozenRowsKDomain) :
      ∃ P : QuadraticTerminal,
        1 / 2 ≤ P.precision (frozenPartitionMass a (j + 1))
          (frozenRowsHead β a h (j + 1) t).2 ∧
        ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x,
          epsilonChain ((frozenSchedule β a (1 / 2) h t).drop (j + 2)) Q K e x ≤ P.value x := by
    have H := (HJ r hr h hh hhsmall t (hhalf t ht) z).2
      (frozenPartitionMass a (j + 1),(frozenRowsHead β a h (j + 1) t).2)
      ((frozenSchedule β a (1 / 2) h t).drop (j + 2))
    apply H
    rw [← frozenRows_next_suffix β a h t j hj]
    exact List.drop_suffix _ _
  let P : ℝ → QuadraticTerminal := fun t =>
    if ht : t ∈ frozenRowsKDomain then Classical.choose (HM t ht) else Q
  have hP (t : ℝ) (ht : t ∈ frozenRowsKDomain) :
      1 / 2 ≤ (P t).precision (frozenPartitionMass a (j + 1))
        (frozenRowsHead β a h (j + 1) t).2 := by
    simpa only [P,dite_eq_left ht] using (Classical.choose_spec (HM t ht)).1
  have hmajor (t : ℝ) (ht : t ∈ frozenRowsKDomain) :
      ∀ e ∈ Ioo (-1 : ℝ) 2, ∀ x,
        epsilonChain ((frozenSchedule β a (1 / 2) h t).drop (j + 2)) Q K e x ≤ (P t).value x := by
    simpa only [P,dite_eq_left ht] using (Classical.choose_spec (HM t ht)).2
  have hA' (t : ℝ) (ht : t ∈ frozenRowsKDomain) (n : Fin 3) :
      MomentKJet.Differentiates
        (epsilonMovingBellKJet (frozenPartitionMass a (j + 1))
          (fun t => (frozenRowsHead β a h (j + 1) t).2)
          (fun t => Real.sqrt h • (y + (Real.sqrt h)⁻¹ •
            (g • (frozenRowsHead β a h j t).2)) + (fun _ => z))
          (fun t e => epsilonChain ((frozenSchedule β a (1 / 2) h t).drop (j + 2)) Q K e) ε n) t := by
    apply epsilonMovingBellKJet_differentiates_of_normalized (Real.sqrt_pos.mpr hh).ne'
    simpa only [frozenRowsMovingBellKJet, α, a, Q, K] using hA t ht n
  exact frozenRowsNormalizedJet_eq_cumulants isOpen_Ioo isOpen_Ioo hh
    ⟨by linarith [hε.1],by linarith [hε.2]⟩ j hj y g
    (fun t ht => (HJ r hr h hh hhsmall t (hhalf t ht) z).1 _ (List.drop_suffix _ _))
    P hm hP hmajor hA' hk i

end SKBarriers2.Corner
