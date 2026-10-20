module

public import ActualStrengthEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def variableEndpointStrengthSweepObjective (n : ℕ) (b h : ℝ → ℝ) (d : ℝ)
    (R : ℝ → ℝ) (lam : ℝ) : ℝ :=
  realOrderedSKPathPressure n
    (fun u => b u-laplaceComparisonStrength d lam (R u))
    (fun u => h u+laplaceComparisonStrength d lam (R u)*R u) 0 +
    (1/4:ℝ)*(∫ u in (0:ℝ)..1, laplaceComparisonStrength d lam (R u)*(R u)^2)

theorem variableEndpointStrengthSweep_clocks_admissible (b h R : ℝ → ℝ) {d lam : ℝ}
    (hd : d ≠ 0) (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1) :
    MonotoneOn (fun u => b u-laplaceComparisonStrength d lam (R u)) (Icc (0:ℝ) 1) ∧
    MonotoneOn (fun u => h u+laplaceComparisonStrength d lam (R u)*R u) (Icc (0:ℝ) 1) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u-laplaceComparisonStrength d lam (R u)) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u+laplaceComparisonStrength d lam (R u)*R u) := by
  have hm := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu v hv huv
    exact sub_le_sub (hb hu hv huv) (hm.1 (hRb u hu) (hRb v hv) (hR hu hv huv))
  · intro u hu v hv huv
    exact add_le_add (hh hu hv huv) (hm.2 (hRb u hu) (hRb v hv) (hR hu hv huv))
  · intro u hu
    exact sub_nonneg.mpr ((laplaceComparisonStrength_le d hlam _).trans
      (hlb.trans (hb (by norm_num) hu hu.1)))
  · intro u hu
    exact add_nonneg (hh0.trans (hh (by norm_num) hu hu.1))
      (mul_nonneg (laplaceComparisonStrength_nonneg d _ hlam) (hRb u hu).1)

theorem variableEndpointStrengthSweepObjective_lipschitz (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d L : ℝ} (hd : d ≠ 0) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : Continuous R) :
    LipschitzOnWith 1 (variableEndpointStrengthSweepObjective n b h d R) (Icc (0:ℝ) L) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro lam hl lam' hl'
  have ha := variableEndpointStrengthSweep_clocks_admissible b h R hd hl.1 (hl.2.trans hLb) hb hh hh0 hR hRb
  have ha' := variableEndpointStrengthSweep_clocks_admissible b h R hd hl'.1 (hl'.2.trans hLb) hb hh hh0 hR hRb
  have hdisp (u : ℝ) :
      |laplaceComparisonStrength d lam (R u)-laplaceComparisonStrength d lam' (R u)| ≤
        |lam-lam'| := laplaceStrength_parameter_displacement d _ _ _
  have hfdisp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      |(h u+laplaceComparisonStrength d lam (R u)*R u)-
        (h u+laplaceComparisonStrength d lam' (R u)*R u)| ≤ |lam-lam'| := by
    have he : (h u+laplaceComparisonStrength d lam (R u)*R u)-
        (h u+laplaceComparisonStrength d lam' (R u)*R u)=
        laplaceComparisonStrength d lam (R u)*R u-laplaceComparisonStrength d lam' (R u)*R u := by ring
    rw [he]
    rw [← sub_mul,abs_mul,abs_of_nonneg (hRb u hu).1]
    exact (mul_le_mul_of_nonneg_right (hdisp u) (hRb u hu).1).trans
      (mul_le_of_le_one_right (abs_nonneg _) (hRb u hu).2)
  have hpdisp (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      |laplaceComparisonStrength d lam (R u)*(R u)^2-
        laplaceComparisonStrength d lam' (R u)*(R u)^2| ≤ |lam-lam'| := by
    rw [← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg (R u))]
    exact (mul_le_mul_of_nonneg_right (hdisp u) (sq_nonneg _)).trans
      (mul_le_of_le_one_right (abs_nonneg _) (by nlinarith [(hRb u hu).1,(hRb u hu).2]))
  have hp := realOrderedSKPathPressure_uniform_comparison n hn _ _ _ _
    ha.1 ha.2.1 ha'.1 ha'.2.1 (ha.2.2.1 0 (by norm_num))
    (ha.2.2.2 0 (by norm_num)) (ha'.2.2.1 0 (by norm_num))
    (ha'.2.2.2 0 (by norm_num)) (fun u _ => by
      have he : b u-laplaceComparisonStrength d lam (R u)-
        (b u-laplaceComparisonStrength d lam' (R u)) =
        -(laplaceComparisonStrength d lam (R u)-laplaceComparisonStrength d lam' (R u)) := by ring
      rw [he,abs_neg]; exact hdisp u) hfdisp 0
  have hi (l : ℝ) : IntervalIntegrable
      (fun u => laplaceComparisonStrength d l (R u)*(R u)^2) volume 0 1 :=
    (((laplaceComparisonStrength_contDiff d l).continuous.comp hRc).mul (hRc.pow 2)).intervalIntegrable _ _
  have hip := intervalIntegral_abs_le_unit_bound hpdisp
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul]
  unfold variableEndpointStrengthSweepObjective
  have he (p q a c : ℝ) : (p+1/4*a)-(q+1/4*c)=(p-q)+1/4*(a-c) := by ring
  rw [he,← intervalIntegral.integral_sub (hi lam) (hi lam')]
  calc
    |_ + _| ≤ |_ - _| + |(1/4:ℝ)*(∫ u in (0:ℝ)..1,
      laplaceComparisonStrength d lam (R u)*(R u)^2-
      laplaceComparisonStrength d lam' (R u)*(R u)^2)| := abs_add_le _ _
    _ ≤ |lam-lam'|/4+|lam-lam'|/2+(1/4:ℝ)*|lam-lam'| := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hip (by norm_num))
    _ = |lam-lam'| := by ring

theorem variableEndpointStrengthSweepObjective_hasDerivAt (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d L lam : ℝ} (hd : d ≠ 0) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : Continuous R) (hlam : lam ∈ Ioo (0:ℝ) L) :
    let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    HasDerivAt (variableEndpointStrengthSweepObjective n b h d R)
      ((1/4:ℝ)*(∫ u in (0:ℝ)..1, laplaceStrengthParameterDeriv d lam (R u)*
        (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2))) lam := by
  dsimp only
  have hi : lam ∈ Icc (0:ℝ) L := ⟨hlam.1.le,hlam.2.le⟩
  have ha (l : ℝ) (hl : l ∈ Icc (0:ℝ) L) :=
    variableEndpointStrengthSweep_clocks_admissible b h R hd hl.1 (hl.2.trans hLb) hb hh hh0 hR hRb
  have hev : ∀ᶠ τ in 𝓝[(univ:Set ℝ) \ {0}] (0:ℝ), lam+τ ∈ Icc (0:ℝ) L := by
    have ht : Tendsto (fun τ : ℝ => lam+τ) (𝓝 0) (𝓝 lam) := by
      simpa only [add_zero, id_eq] using tendsto_const_nhds.add (tendsto_id : Tendsto (fun τ:ℝ=>τ) (𝓝 0) (𝓝 0))
    exact (ht.eventually (Icc_mem_nhds hlam.1 hlam.2)).filter_mono nhdsWithin_le_nhds
  have hD : Continuous (fun u => laplaceStrengthParameterDeriv d lam (R u)) :=
    (laplaceStrengthParameterDeriv_continuous_radius d lam).comp hRc
  have hi0 (l : ℝ) : IntervalIntegrable
      (fun u => laplaceComparisonStrength d l (R u)*(R u)^2) volume 0 1 :=
    (((laplaceComparisonStrength_contDiff d l).continuous.comp hRc).mul (hRc.pow 2)).intervalIntegrable _ _
  have hdisp (τ u : ℝ) :
      |laplaceComparisonStrength d (lam+τ) (R u)-laplaceComparisonStrength d (lam+0) (R u)| ≤ |τ| := by
    simpa using laplaceStrength_parameter_displacement d (R u) (lam+τ) (lam+0)
  have hd0 (u : ℝ) : HasDerivAt
      (fun τ => laplaceComparisonStrength d (lam+τ) (R u))
      (laplaceStrengthParameterDeriv d lam (R u)) (0:ℝ) := by
    convert (laplaceStrength_parameter_hasDerivAt d lam (R u)).comp_of_eq (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).const_add lam) (by simp) using 1
    · rfl
    · simp
  have hder := compensated_curve_derivative n hn b h
    (fun τ u => laplaceComparisonStrength d (lam+τ) (R u))
    (fun τ u => laplaceComparisonStrength d (lam+τ) (R u)*R u)
    (fun τ u => laplaceComparisonStrength d (lam+τ) (R u)*(R u)^2)
    (fun u => laplaceStrengthParameterDeriv d lam (R u))
    (fun u => laplaceStrengthParameterDeriv d lam (R u)*R u)
    (fun u => laplaceStrengthParameterDeriv d lam (R u)*(R u)^2) 1 1 1 univ
    (by simpa using (ha lam hi).1) (by simpa using (ha lam hi).2.1)
    (by simpa using (ha lam hi).2.2.1) (by simpa using (ha lam hi).2.2.2)
    (hev.mono (fun τ hτ => (ha (lam+τ) hτ).1))
    (hev.mono (fun τ hτ => by simpa using (ha (lam+τ) hτ).2.1))
    (hev.mono (fun τ hτ => (ha (lam+τ) hτ).2.2.1))
    (hev.mono (fun τ hτ => by simpa using (ha (lam+τ) hτ).2.2.2))
    (Eventually.of_forall (fun τ u _ => by simpa using hdisp τ u))
    (Eventually.of_forall (by
      intro τ u hu
      rw [← sub_mul,abs_mul,abs_of_nonneg (hRb u hu).1]
      exact (mul_le_mul_of_nonneg_right (hdisp τ u) (hRb u hu).1).trans
        (by simpa using mul_le_of_le_one_right (abs_nonneg τ) (hRb u hu).2)))
    (Eventually.of_forall (by
      intro τ u hu
      rw [← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg (R u))]
      have hsq : (R u)^2≤1 := by nlinarith [(hRb u hu).1,(hRb u hu).2]
      exact (mul_le_mul_of_nonneg_right (hdisp τ u) (sq_nonneg _)).trans
        (by simpa using (mul_le_of_le_one_right (abs_nonneg τ) hsq))))
    (hD.intervalIntegrable _ _) ((hD.mul hRc).intervalIntegrable _ _)
    ((hD.mul (hRc.pow 2)).intervalIntegrable _ _) (by simpa using hi0 lam)
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
    simp only [he,variableEndpointStrengthSweepObjective,zero_add]
  · rw [mul_one]
    apply congrArg (fun x : ℝ => (1/4:ℝ)*x)
    apply intervalIntegral.integral_congr
    intro u _
    simp only [add_zero,zero_add]
    ring

theorem variableEndpointStrengthSweep_derivative_nonneg (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d lam : ℝ} (hd : d ≠ 0)
    (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1) :
    let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    0 ≤ (1/4:ℝ)*(∫ u in (0:ℝ)..1, laplaceStrengthParameterDeriv d lam (R u)*
      (orderedPathB n bf hf u-2*R u*orderedPathS n bf hf u+(R u)^2)) := by
  dsimp only
  have ha := variableEndpointStrengthSweep_clocks_admissible b h R hd hlam hlb hb hh hh0 hR hRb
  have hbm := toNNReal_monotoneOn ha.1
  have hfm := toNNReal_monotoneOn ha.2.1
  apply mul_nonneg (by norm_num : 0≤(1/4:ℝ))
  apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [volume.ae_ne (0:ℝ)] with u hu0 hu
  have hs := orderedPath_SK_bounds n hn _ _ hbm hfm
    (⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2⟩ : u∈Ioc (0:ℝ) 1)
  apply mul_nonneg (laplaceStrengthParameterDeriv_mem d lam (R u)).1.le
  nlinarith [sq_nonneg (orderedPathS n
    (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
    (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-R u)]

theorem variableEndpointStrengthSweep_log_derivative_le (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d L lam : ℝ} (hd : d ≠ 0) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : Continuous R) (hlam : lam ∈ Ioo (0:ℝ) L) :
    let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    lam*deriv (variableEndpointStrengthSweepObjective n b h d R) lam ≤
      (1/4:ℝ)*(∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
        ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
          (orderedPathS n bf hf u-R u)^2)) := by
  dsimp only
  rw [(variableEndpointStrengthSweepObjective_hasDerivAt n hn b h R hd hLb hb hh hh0 hR hRb hRc hlam).deriv]
  have ha := variableEndpointStrengthSweep_clocks_admissible b h R hd hlam.1.le (hlam.2.le.trans hLb) hb hh hh0 hR hRb
  have hbm := toNNReal_monotoneOn ha.1
  have hfm := toNNReal_monotoneOn ha.2.1
  have hI := strengthSweep_weightedQuadratic_integrable n hn _ _ hbm hfm
    (fun u => laplaceStrengthParameterDeriv d lam (R u)) R
    ((laplaceStrengthParameterDeriv_continuous_radius d lam).comp hRc) hRc
  have hI' := strengthSweep_weightedQuadratic_integrable n hn _ _ hbm hfm
    (fun u => laplaceComparisonStrength d lam (R u)) R
    ((laplaceComparisonStrength_contDiff d lam).continuous.comp hRc) hRc
  have he (u : ℝ) :
      (orderedPathB n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-
        (orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u)^2)+
        (orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-R u)^2 =
      orderedPathB n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-
        2*R u*orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u+(R u)^2 := by ring
  simp_rw [he]
  have hcomp : lam*(∫ u in (0:ℝ)..1,laplaceStrengthParameterDeriv d lam (R u)*
      (orderedPathB n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-
        2*R u*orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u+(R u)^2)) ≤
      ∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
      (orderedPathB n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-
        2*R u*orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u+(R u)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one (hI.const_mul lam) hI'
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne (0:ℝ)] with u hu0 hu
    have hs := orderedPath_SK_bounds n hn _ _ hbm hfm
      (⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2⟩ : u∈Ioc (0:ℝ) 1)
    have hquad : 0 ≤ orderedPathB n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-
        2*R u*orderedPathS n (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u+(R u)^2 := by
      nlinarith [sq_nonneg (orderedPathS n
        (fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal)
        (fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal) u-R u)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (laplaceStrength_logParameterDeriv_le d (R u) hlam.1.le) hquad
  nlinarith [hcomp]

theorem variableEndpointStrengthSweepObjective_monotone (n : ℕ) (hn : 0 < n)
    (b h R : ℝ → ℝ) {d L : ℝ} (hd : d ≠ 0) (hLb : L ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hR : MonotoneOn R (Icc (0:ℝ) 1))
    (hRb : ∀ u ∈ Icc (0:ℝ) 1, R u ∈ Icc (0:ℝ) 1)
    (hRc : Continuous R) :
    MonotoneOn (variableEndpointStrengthSweepObjective n b h d R) (Icc (0:ℝ) L) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) L)
    (variableEndpointStrengthSweepObjective_lipschitz n hn b h R hd hLb hb hh hh0 hR hRb hRc).continuousOn
  · intro lam hlam
    rw [interior_Icc] at hlam
    exact (variableEndpointStrengthSweepObjective_hasDerivAt n hn b h R hd hLb hb hh hh0 hR hRb hRc hlam).differentiableAt.differentiableWithinAt
  · intro lam hlam
    rw [interior_Icc] at hlam
    rw [(variableEndpointStrengthSweepObjective_hasDerivAt n hn b h R hd hLb hb hh hh0 hR hRb hRc hlam).deriv]
    exact variableEndpointStrengthSweep_derivative_nonneg n hn b h R hd hlam.1.le
      (hlam.2.le.trans hLb) hb hh hh0 hR hRb

theorem variableEndpointStrengthSweepObjective_zero (n : ℕ) (b h R : ℝ → ℝ) (d : ℝ) :
    variableEndpointStrengthSweepObjective n b h d R 0=realOrderedSKPathPressure n b h 0 := by
  simp [variableEndpointStrengthSweepObjective,laplaceComparisonStrength_zero]

end OAI.SKFluctuations.LaplaceWindowFormalization
