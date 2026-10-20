module

public import OmittedStrengthDerivative

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem workingInterval_weightedQuadratic_integrable (n : ℕ) (hn : 0<n)
    (bf hf : ℝ → ℝ≥0) (hb : MonotoneOn bf (Icc (0:ℝ) 1))
    (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    {u0 : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (w R : ℝ → ℝ)
    (hw : ContinuousOn w (Icc u0 1)) (hR : ContinuousOn R (Icc u0 1))
    (hbefore : ∀ u ∈ Ico (0:ℝ) u0, w u=0) :
    IntervalIntegrable (fun u => w u*(orderedPathB n bf hf u-
      2*R u*orderedPathS n bf hf u+(R u)^2)) volume 0 1 := by
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Icc u0 1)) :
      IntervalIntegrable (fun u => w u*f u) volume 0 1 := by
    apply cutoff_eq_intervalIntegrable hu0 (hw.mul hf)
    intro u hu
    by_cases he : u0 ≤ u
    · rw [ite_eq_left he]; rfl
    · rw [ite_eq_right he,hbefore u ⟨hu.1,lt_of_not_ge he⟩,zero_mul]
  have hB := orderedPathPair_mul_integrable n hn bf hf hb hh
    (fun σ τ => (orderedOverlap n σ τ)^2) w (by simpa only [mul_one] using hi (fun _=>1) continuousOn_const)
  have hS := orderedPathPair_mul_integrable n hn bf hf hb hh
    (orderedOverlap n) (fun u => w u*R u) (hi R hR)
  have hP := hi (fun u => (R u)^2) (hR.pow 2)
  convert (hB.sub (hS.const_mul 2)).add hP using 1
  ext u
  simp only [orderedPathB,orderedPathS,Pi.mul_apply,Pi.pow_apply]
  ring

theorem omittedStrengthSweep_log_derivative_le (n : ℕ) (hn : 0<n)
    (b h R : ℝ → ℝ) {d u0 L lam : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d≠0)
    (hLcut : L ≤ b u0) (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+L ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : ContinuousOn R (Icc u0 1)) (hlam : lam ∈ Ioo (0:ℝ) L) :
    let bf := fun u => (b u-omittedStrengthCoefficient d u0 R lam u).toNNReal
    let hf := fun u => (h u+omittedStrengthCoefficient d u0 R lam u*R u).toNNReal
    lam*deriv (omittedStrengthSweepObjective n b h d u0 R) lam ≤
      (1/4:ℝ)*(∫ u in (0:ℝ)..1,omittedStrengthCoefficient d u0 R lam u*
        ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
          (orderedPathS n bf hf u-R u)^2)) := by
  dsimp only
  rw [(omittedStrengthSweepObjective_hasDerivAt n hn b h R hu0 hd hLcut hcross hb hb0 hh hh0 hR hRb hRc hlam).deriv]
  let bf := fun u => (b u-omittedStrengthCoefficient d u0 R lam u).toNNReal
  let hf := fun u => (h u+omittedStrengthCoefficient d u0 R lam u*R u).toNNReal
  have ha := omittedStrengthSweep_clocks_admissible b h R hu0 hd hlam.1.le
    (hlam.2.le.trans hLcut) (fun u hu => by linarith [hcross u hu,hlam.2]) hb hb0 hh hh0 hR hRb
  have hbm := toNNReal_monotoneOn ha.1
  have hfm := toNNReal_monotoneOn ha.2.1
  have hD : ContinuousOn (omittedStrengthParameterDeriv d u0 R lam) (Icc u0 1) := by
    apply ((laplaceStrengthParameterDeriv_continuous_radius d lam).comp_continuousOn hRc).congr
    intro u hu
    simp [omittedStrengthParameterDeriv,hu.1]
  have hE : ContinuousOn (omittedStrengthCoefficient d u0 R lam) (Icc u0 1) := by
    apply ((laplaceComparisonStrength_contDiff d lam).continuous.comp_continuousOn hRc).congr
    intro u hu
    simp [omittedStrengthCoefficient,hu.1]
  have hI := workingInterval_weightedQuadratic_integrable n hn bf hf hbm hfm hu0
    (omittedStrengthParameterDeriv d u0 R lam) R hD hRc
    (fun u hu => by simp [omittedStrengthParameterDeriv,not_le_of_gt hu.2])
  have hI' := workingInterval_weightedQuadratic_integrable n hn bf hf hbm hfm hu0
    (omittedStrengthCoefficient d u0 R lam) R hE hRc
    (fun u hu => by simp [omittedStrengthCoefficient,not_le_of_gt hu.2])
  have he (u : ℝ) : (orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
      (orderedPathS n bf hf u-R u)^2 =
      orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2 := by ring
  change lam*((1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedStrengthParameterDeriv d u0 R lam u*
      (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2))) ≤
    (1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedStrengthCoefficient d u0 R lam u*
      ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+(orderedPathS n bf hf u-R u)^2))
  simp_rw [he]
  have hcomp : lam*(∫ u in (0:ℝ)..1, omittedStrengthParameterDeriv d u0 R lam u*
      (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2)) ≤
      ∫ u in (0:ℝ)..1, omittedStrengthCoefficient d u0 R lam u*
      (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one (hI.const_mul lam) hI'
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne (0:ℝ)] with u hu0' hu
    by_cases heu : u0 ≤ u
    · have hs := orderedPath_SK_bounds n hn bf hf hbm hfm
        (⟨lt_of_le_of_ne hu.1 hu0'.symm,hu.2⟩ : u∈Ioc (0:ℝ) 1)
      have hquad : 0 ≤ orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2 := by
        nlinarith [sq_nonneg (orderedPathS n bf hf u-R u)]
      simp only [omittedStrengthParameterDeriv,omittedStrengthCoefficient,ite_eq_left heu]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (laplaceStrength_logParameterDeriv_le d (R u) hlam.1.le) hquad
    · simp [omittedStrengthParameterDeriv,omittedStrengthCoefficient,heu]
  nlinarith [hcomp]

end OAI.SKFluctuations.LaplaceWindowFormalization
