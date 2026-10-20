module

public import OmittedStrengthEnvelope

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem omittedStrengthSweepObjective_hasDerivAt (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d u0 L lam : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d ≠ 0)
    (hLcut : L ≤ b u0) (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+L ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : ContinuousOn R (Icc u0 1)) (hlam : lam ∈ Ioo (0:ℝ) L) :
    let bf := fun u => (b u-omittedStrengthCoefficient d u0 R lam u).toNNReal
    let hf := fun u => (h u+omittedStrengthCoefficient d u0 R lam u*R u).toNNReal
    HasDerivAt (omittedStrengthSweepObjective n b h d u0 R)
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedStrengthParameterDeriv d u0 R lam u*
        (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2))) lam := by
  dsimp only
  have hi : lam ∈ Icc (0:ℝ) L := ⟨hlam.1.le,hlam.2.le⟩
  have ha (l : ℝ) (hl : l ∈ Icc (0:ℝ) L) := omittedStrengthSweep_clocks_admissible b h R hu0 hd hl.1
    (hl.2.trans hLcut) (fun u hu => by linarith [hcross u hu,hl.2]) hb hb0 hh hh0 hR hRb
  have hev : ∀ᶠ τ in 𝓝[(univ:Set ℝ) \ {0}] (0:ℝ), lam+τ ∈ Icc (0:ℝ) L := by
    have ht : Tendsto (fun τ : ℝ => lam+τ) (𝓝 0) (𝓝 lam) := by
      simpa only [add_zero,id_eq] using tendsto_const_nhds.add
        (tendsto_id : Tendsto (fun τ:ℝ=>τ) (𝓝 0) (𝓝 0))
    exact (ht.eventually (Icc_mem_nhds hlam.1 hlam.2)).filter_mono nhdsWithin_le_nhds
  have hi0 (l : ℝ) := omittedStrengthCoefficient_mul_integrable (d:=d) (lam:=l) hu0 R hRc
    (fun u => (R u)^2) (hRc.pow 2)
  have hdisp (τ u : ℝ) :
      |omittedStrengthCoefficient d u0 R (lam+τ) u-omittedStrengthCoefficient d u0 R (lam+0) u| ≤ |τ| := by
    simpa using omittedStrengthCoefficient_displacement d u0 R (lam+τ) (lam+0) u
  have hd0 (u : ℝ) : HasDerivAt
      (fun τ => omittedStrengthCoefficient d u0 R (lam+τ) u)
      (omittedStrengthParameterDeriv d u0 R lam u) (0:ℝ) := by
    by_cases hu : u0 ≤ u
    · simp only [omittedStrengthCoefficient,omittedStrengthParameterDeriv,ite_eq_left hu]
      convert (laplaceStrength_parameter_hasDerivAt d lam (R u)).comp_of_eq (0:ℝ)
        ((hasDerivAt_id (0:ℝ)).const_add lam) (by simp) using 1
      · rfl
      · simp
    · simpa only [omittedStrengthCoefficient,omittedStrengthParameterDeriv,ite_eq_right hu] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hD := omittedStrengthParameterDeriv_mul_integrable (d:=d) (lam:=lam) hu0 R hRc
    (fun _ => 1) continuousOn_const
  have hDR := omittedStrengthParameterDeriv_mul_integrable (d:=d) (lam:=lam) hu0 R hRc R hRc
  have hDR2 := omittedStrengthParameterDeriv_mul_integrable (d:=d) (lam:=lam) hu0 R hRc
    (fun u => (R u)^2) (hRc.pow 2)
  have hder := compensated_curve_derivative n hn b h
    (fun τ u => omittedStrengthCoefficient d u0 R (lam+τ) u)
    (fun τ u => omittedStrengthCoefficient d u0 R (lam+τ) u*R u)
    (fun τ u => omittedStrengthCoefficient d u0 R (lam+τ) u*(R u)^2)
    (fun u => omittedStrengthParameterDeriv d u0 R lam u)
    (fun u => omittedStrengthParameterDeriv d u0 R lam u*R u)
    (fun u => omittedStrengthParameterDeriv d u0 R lam u*(R u)^2) 1 1 1 univ
    (by simpa using (ha lam hi).1) (by simpa using (ha lam hi).2.1)
    (by simpa using (ha lam hi).2.2.1) (by simpa using (ha lam hi).2.2.2)
    (hev.mono (fun τ hτ => (ha (lam+τ) hτ).1))
    (hev.mono (fun τ hτ => by simpa using (ha (lam+τ) hτ).2.1))
    (hev.mono (fun τ hτ => (ha (lam+τ) hτ).2.2.1))
    (hev.mono (fun τ hτ => by simpa using (ha (lam+τ) hτ).2.2.2))
    (Eventually.of_forall (fun τ u _ => by simpa using hdisp τ u))
    (Eventually.of_forall (by
      intro τ u hu
      by_cases hu0' : u0 ≤ u
      · rw [← sub_mul,abs_mul,abs_of_nonneg (hRb u ⟨hu0',hu.2⟩).1]
        exact (mul_le_mul_of_nonneg_right (hdisp τ u) (hRb u ⟨hu0',hu.2⟩).1).trans
          (by simpa using mul_le_of_le_one_right (abs_nonneg τ) (hRb u ⟨hu0',hu.2⟩).2)
      · simp [omittedStrengthCoefficient,hu0']))
    (Eventually.of_forall (by
      intro τ u hu
      by_cases hu0' : u0 ≤ u
      · rw [← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg (R u))]
        have hsq : (R u)^2 ≤ 1 := by nlinarith [(hRb u ⟨hu0',hu.2⟩).1,(hRb u ⟨hu0',hu.2⟩).2]
        exact (mul_le_mul_of_nonneg_right (hdisp τ u) (sq_nonneg _)).trans
          (by simpa using mul_le_of_le_one_right (abs_nonneg τ) hsq)
      · simp [omittedStrengthCoefficient,hu0']))
    (by simpa only [mul_one] using hD) hDR hDR2 (by simpa using hi0 lam)
    (Eventually.of_forall (fun τ => hi0 (lam+τ)))
    (Eventually.of_forall (fun u _ => (hd0 u).hasDerivWithinAt))
    (Eventually.of_forall (fun u _ => ((hd0 u).mul_const (R u)).hasDerivWithinAt))
    (Eventually.of_forall (fun u _ => ((hd0 u).mul_const ((R u)^2)).hasDerivWithinAt))
  have hd' := (hasDerivWithinAt_univ.mp hder).comp_of_eq lam
    ((hasDerivAt_id lam).sub_const lam) (by simp)
  convert hd' using 1
  · ext l
    simp only [Function.comp_apply,id_eq]
    have he : lam+(l-lam)=l := by ring
    simp only [he,omittedStrengthSweepObjective,zero_add]
  · rw [mul_one]
    apply congrArg (fun x : ℝ => (1/4:ℝ)*x)
    apply intervalIntegral.integral_congr
    intro u _
    simp only [add_zero,zero_add]
    ring

theorem omittedStrengthSweep_derivative_nonneg (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d u0 lam : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d ≠ 0)
    (hlam : 0 ≤ lam) (hlcut : lam ≤ b u0)
    (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+lam ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1) :
    let bf := fun u => (b u-omittedStrengthCoefficient d u0 R lam u).toNNReal
    let hf := fun u => (h u+omittedStrengthCoefficient d u0 R lam u*R u).toNNReal
    0 ≤ (1/4:ℝ)*(∫ u in (0:ℝ)..1, omittedStrengthParameterDeriv d u0 R lam u*
      (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2)) := by
  dsimp only
  have ha := omittedStrengthSweep_clocks_admissible b h R hu0 hd hlam hlcut hcross hb hb0 hh hh0 hR hRb
  have hbm := toNNReal_monotoneOn ha.1
  have hfm := toNNReal_monotoneOn ha.2.1
  apply mul_nonneg (by norm_num : 0≤(1/4:ℝ))
  apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [volume.ae_ne (0:ℝ)] with u hu0' hu
  by_cases he : u0 ≤ u
  · have hs := orderedPath_SK_bounds n hn _ _ hbm hfm
      (⟨lt_of_le_of_ne hu.1 hu0'.symm,hu.2⟩ : u∈Ioc (0:ℝ) 1)
    simp only [omittedStrengthParameterDeriv,ite_eq_left he]
    apply mul_nonneg (laplaceStrengthParameterDeriv_mem d lam (R u)).1.le
    nlinarith [sq_nonneg (orderedPathS n
      (fun u => (b u-omittedStrengthCoefficient d u0 R lam u).toNNReal)
      (fun u => (h u+omittedStrengthCoefficient d u0 R lam u*R u).toNNReal) u-R u)]
  · simp [omittedStrengthParameterDeriv,he]

theorem omittedStrengthSweepObjective_monotone (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d u0 L : ℝ} (hu0 : u0 ∈ Icc (0:ℝ) 1) (hd : d ≠ 0)
    (hLcut : L ≤ b u0) (hcross : ∀ u ∈ Ico (0:ℝ) u0, b u+L ≤ b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0 ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc u0 1))
    (hRb : ∀ u ∈ Icc u0 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : ContinuousOn R (Icc u0 1)) :
    MonotoneOn (omittedStrengthSweepObjective n b h d u0 R) (Icc (0:ℝ) L) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) L)
    (omittedStrengthSweepObjective_lipschitz n hn b h R hu0 hd hLcut hcross hb hb0 hh hh0 hR hRb hRc).continuousOn
  · intro lam hlam
    rw [interior_Icc] at hlam
    exact (omittedStrengthSweepObjective_hasDerivAt n hn b h R hu0 hd hLcut hcross hb hb0 hh hh0 hR hRb hRc hlam).differentiableAt.differentiableWithinAt
  · intro lam hlam
    rw [interior_Icc] at hlam
    rw [(omittedStrengthSweepObjective_hasDerivAt n hn b h R hu0 hd hLcut hcross hb hb0 hh hh0 hR hRb hRc hlam).deriv]
    exact omittedStrengthSweep_derivative_nonneg n hn b h R hu0 hd hlam.1.le
      (hlam.2.le.trans hLcut) (fun u hu => by linarith [hcross u hu,hlam.2]) hb hb0 hh hh0 hR hRb

end OAI.SKFluctuations.LaplaceWindowFormalization
