module

public import ComparisonScalarGlobalCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 3500000

theorem comparison_joint_scalar_radius_compactness {T R0 c B : ℝ}
    (hT : 0 < T) (hR0 : 0 < R0) (hc0 : 0 < c) (hB : 0 ≤ B)
    (alpha radiusCDF : ℕ → boundedMassProfiles) (x : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀n, 0 < x n)
    (hc : ∀n q, ContinuousWithinAt (alpha n).val (Ici q) q)
    (hcap : ∀R : ℝ, 0 < R → ∃A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, (alpha n).val (x n*R) ≤ A*x n)
    (hradiusCap : ∀R : ℝ, 0 < R → ∃A : ℝ,
      ∀ᶠ n in atTop, (radiusCDF n).val (x n*R)/x n ≤ A)
    (hcal : ∀ᶠ n in atTop, ∃q, c*x n ≤ q ∧ q ≤ R0*x n ∧
      |scalarPlantedEnergy hT (alpha n) q-q| ≤ B*(x n)^3) :
    ∃(beta radiusLimit : boundedMassProfiles) (U V : NonnegativeMassProfile)
      (sigma : ℝ) (phi : ℕ → ℕ),
      StrictMono phi ∧ Tendsto (alpha ∘ phi) atTop (𝓝 beta) ∧
      Tendsto (radiusCDF ∘ phi) atTop (𝓝 radiusLimit) ∧
      (∀t : ℝ, Tendsto (fun n => (alpha (phi n)).val (x (phi n)*t)/x (phi n))
        atTop (𝓝 (U.mass t))) ∧
      (∀t : ℝ, Tendsto (fun n => (radiusCDF (phi n)).val (x (phi n)*t)/x (phi n))
        atTop (𝓝 (V.mass t))) ∧
      let F := fun t => T^3*(scalarTailSpatialJet hT beta 4 0 0)^2*t-
        2*T^2*(scalarTailSpatialJet hT beta 2 0 0)^3*U.mass t
      let p := fun t => sigma+∫s in 0..t,F s
      ∀R : ℝ, 0 < R → ContinuousOn p (Icc (0 : ℝ) R) ∧
        TendstoUniformlyOn (fun n => comparisonActualScalarSlope hT (alpha (phi n)) (x (phi n)))
          p atTop (Icc (0 : ℝ) R) ∧
        TendstoUniformlyOn (fun n => comparisonActualScalarResponse hT (alpha (phi n)) (x (phi n)))
          (fun t => ∫s in 0..t,p s) atTop (Icc (0 : ℝ) R) := by
  have hnormcap : ∀R : ℝ, 0 < R → ∃A : ℝ,
      ∀ᶠ n in atTop, (alpha n).val (x n*R)/x n ≤ A := by
    intro R hR
    obtain ⟨A,_,hAn⟩ := hcap R hR
    exact ⟨A,hAn.mono fun n hn => (div_le_iff₀ (hxp n)).mpr hn⟩
  obtain ⟨beta,radiusLimit,U,V,phi,hphi,halpha,hradius,hU,hV⟩ :=
    profile_pair_and_rescalings_tendsto_subseq alpha radiusCDF x hxp hnormcap hradiusCap
  have hUi (R : ℝ) : IntegrableOn U.mass (Icc (0 : ℝ) R) := by
    apply (integrable_const (U.mass R)).mono' U.monotone.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg t)] using U.monotone ht.2
  obtain ⟨A,hA,hAn⟩ := hcap R0 hR0
  obtain ⟨sigma,psi,hpsi,_,_,hp,_⟩ := comparison_actual_scalar_compactness hT hR0.le hA hc0 hB
    halpha (hx.comp hphi.tendsto_atTop) (Eventually.of_forall fun n => hxp (phi n))
    (fun n q => hc (phi n) q) (hphi.tendsto_atTop.eventually hAn) U.mass (hUi R0)
    (Eventually.of_forall fun t _ => hU t) (hphi.tendsto_atTop.eventually hcal)
  have hsigma : Tendsto
      (fun n => comparisonActualScalarSlope hT (alpha (phi (psi n))) (x (phi (psi n))) 0)
      atTop (𝓝 sigma) := by
    simpa only [Function.comp_apply,intervalIntegral.integral_same,add_zero]
      using hp.tendsto_at ⟨le_rfl,hR0.le⟩
  refine ⟨beta,radiusLimit,U,V,sigma,phi ∘ psi,hphi.comp hpsi,
    halpha.comp hpsi.tendsto_atTop,hradius.comp hpsi.tendsto_atTop,
    fun t => (hU t).comp hpsi.tendsto_atTop,fun t => (hV t).comp hpsi.tendsto_atTop,?_⟩
  dsimp only
  intro R hR
  obtain ⟨AR,hAR,hARn⟩ := hcap R hR
  exact comparison_scalar_limits_of_initial_slope hT hR.le hAR
    (halpha.comp hpsi.tendsto_atTop) (hx.comp (hphi.comp hpsi).tendsto_atTop)
    (Eventually.of_forall fun n => hxp (phi (psi n))) (fun n q => hc (phi (psi n)) q)
    ((hphi.comp hpsi).tendsto_atTop.eventually hARn) U.mass (hUi R)
    (Eventually.of_forall fun t _ => (hU t).comp hpsi.tendsto_atTop) hsigma

theorem comparison_initial_interval_limits_locally_uniform
    (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hF : ∀R : ℝ, 0 < R → TendstoUniformlyOn F g atTop (Icc (0 : ℝ) R)) :
    TendstoLocallyUniformlyOn F g atTop (Ioi (0 : ℝ)) := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro eps heps v hv
  change 0 < v at hv
  refine ⟨Ioo (v/2) (v+1),mem_nhdsWithin_of_mem_nhds
    (Ioo_mem_nhds (by linarith) (by linarith)),?_⟩
  have hh := Metric.tendstoUniformlyOn_iff.mp (hF (v+1) (by linarith)) eps heps
  filter_upwards [hh] with n hn w hw
  exact hn w ⟨by linarith [hw.1],hw.2.le⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
