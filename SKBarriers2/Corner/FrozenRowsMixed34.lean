module

public import SKBarriers2.Corner.FrozenRowsMixed31
public import SKBarriers2.Corner.FrozenRowsMixed33
public import SKBarriers2.Corner.FrozenRowsNaturalTestProfiles
public import SKBarriers2.Corner.FrozenRowsMixedFiniteBudgets
public import SKBarriers2.Corner.FrozenRowsMixedAverageRealization
public import SKBarriers2.Corner.FrozenRowsMixedValue6
public import SKBarriers2.Corner.FrozenRowsPotential24

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner
open StepCalculus

theorem scalarData_frozenRowsMovingAffineAverage_spatial {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ E : ℝ, 0 < h₀ ∧ 1 ≤ E ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j : ℕ, ∀ hj : j < 11, ∀ M : ℝ, 1 ≤ M →
      (∀ k ∈ frozenRowsKDomain, FrozenRowsMixedEnvelope β (cdf (D.μ : Measure ℝ))
        (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h z ε (j+1) M k) →
      ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ, ∀ i : Fin 3,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r-h)
      let parent : Fin 12 := ⟨j,by omega⟩
      let q : Fin 12 := ⟨j+1,by omega⟩
      let c := frozenRowsNaturalHead h z q
      let F := frozenRowsNaturalPotential β α (r-h) h z ε (q.val+1)
      let G := frozenRowsNaturalBellTest β α (r-h) h z ε q i
      let p := frozenRowsMovingParameterCurve β α a (r-h) h z ε parent q g
      MomentKJet.SpatialBound (2*j) (E*M^(i.val+1)*(1+|g|)^(3*(i.val+1))) (3*(i.val+1))
        (fun y => MomentKJet.rescale (Real.sqrt h/(1+|g|))
          (parameterCurveKJet (affineCoordinateAverage c F G) p k y)) := by
  obtain ⟨hA,hhA,HA⟩ := scalarData_frozenRows_average_inputs D hl hu
  obtain ⟨hG,K,hhG,hK,HG⟩ := scalarData_frozenRowsMovingTestEndpoint_geometry D hl hu
  obtain ⟨hQ,B,hhQ,_hB,HQ⟩ := scalarData_frozenRows_translated_potential_qPotential D hl hu 22 (by norm_num)
  obtain ⟨hC,Mc,hhC,hMc,HC⟩ := scalarData_frozen_coarse_normalized_first_epsilon_jets D hl hu 22
  obtain ⟨hS,L,hhS,hL,HS⟩ := scalarData_frozenCompletedFineLogInput_score_profiles D hl hu 20
  obtain ⟨T,hT,HT⟩ := spatialNoiseTransportBudget_uniform_boundedGeometry 20 11 B L K hK
  let Aprofile := fun r N => movingTestProfileUniformCoefficient r (3*N) K
  let Dt := finiteMovingTestProfileBudget bellFineCoefficient bellCoarseCoefficient Aprofile Mc
  have hDt : 1 ≤ Dt := one_le_finiteMovingTestProfileBudget _ _ _ _
  let h₀ := min hA (min hG (min hQ (min hC (min hS 1))))
  let E := T*Dt
  have hE : 1 ≤ E := by
    dsimp only [E]
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sub_nonneg.mpr hDt)]
  refine ⟨h₀,E,lt_min hhA (lt_min hhG (lt_min hhQ (lt_min hhC (lt_min hhS (by norm_num))))),hE,?_⟩
  intro r hr h hh hhsmall z ε hε j hj M hM Hfine k hk g i
  have hcaps : h ≤ hA ∧ h ≤ hG ∧ h ≤ hQ ∧ h ≤ hC ∧ h ≤ hS ∧ h ≤ 1 := by
    simpa only [h₀,le_min_iff] using hhsmall
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r-h)
  let parent : Fin 12 := ⟨j,by omega⟩
  let q : Fin 12 := ⟨j+1,by omega⟩
  let ρ := Real.sqrt h
  let W := 1+|g|
  let σ := ρ/W
  let δ := ρ^3/W
  let rsp := 2*j
  let N := i.val+1
  let c := frozenRowsNaturalHead h z q
  let F := frozenRowsNaturalPotential β α (r-h) h z ε (q.val+1)
  let G := frozenRowsNaturalBellTest β α (r-h) h z ε q i
  let p := frozenRowsMovingParameterCurve β α a (r-h) h z ε parent q g
  let u := fun κ => ρ • (g • frozenUnitDirection β κ parent)
  obtain ⟨Hmodel,_⟩ := HA r hr h hh hcaps.1 z ε hε
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₁ : ρ ≤ 1 := Real.sqrt_le_one.mpr hcaps.2.2.2.2.2
  have hW : 1 ≤ W := by dsimp only [W]; linarith [abs_nonneg g]
  have hδ : |δ| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hρ.le 3) (by positivity))]
    exact (div_le_one₀ (by dsimp only [W]; positivity)).mpr ((pow_le_one₀ hρ.le hρ₁).trans hW)
  have hrsp : rsp ≤ 20 := by dsimp only [rsp]; omega
  have hrsp₂ : rsp+2 ≤ 22 := by omega
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hN₃ : N ≤ 3 := by dsimp only [N]; omega
  have hm : a*frozenUnitMass q ∈ Icc (0 : ℝ) 1 := by
    have hunit : ∀ v : Fin 12, 0 < frozenUnitMass v ∧ frozenUnitMass v ≤ 1 := by
      intro v
      fin_cases v <;> norm_num [frozenUnitMass]
    have hu := hunit q
    refine ⟨mul_nonneg Hmodel.mass_pos.le hu.1.le,?_⟩
    exact (mul_le_mul (cdf_le_one (D.μ : Measure ℝ) (r-h)) hu.2 hu.1.le
      (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hFine (v : Fin 3) : MomentKJet.SpatialBound (rsp+2) (M^(v.val+1)) (3*(v.val+1))
      (fun y => MomentKJet.rescale ρ (normalizedEpsilonKJet
        (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α (r-h) h z) (terminalResidual β α (r-h) h z)
        ρ (fun _ => z) (fun _ => y) (v.val+1) ε k)) := by
    simpa [MomentKJet.SpatialBound,FrozenRowsMixedEnvelope,frozenRowsNormalizedJet,rsp,q,ρ,α,a,Nat.mul_add] using Hfine k hk 0 v
  have hCoarse (v : Fin 3) : MomentKJet.FirstDegreeBound (rsp+2) ((Mc/ρ)^(v.val+1)) (2*(v.val+1)-1)
      (fun y => MomentKJet.rescale ρ (normalizedEpsilonKJet
        (fun κ => (frozenSchedule β a (1/2) h κ).drop (q.val+1))
        (terminalTaylorQuadratic β α (r-h) h z) (terminalResidual β α (r-h) h z)
        ρ (fun _ => z) (fun _ => y) (v.val+1) ε k)) := by
    have Hc := (HC r hr h hh hcaps.2.2.2.1 z ε hε k hk ⟨j+2,by omega⟩ v).of_le hrsp₂
    simpa only [frozenRowsCoarseNormalizedJet,q,ρ,div_eq_mul_inv] using Hc
  have HI := Hmodel.bell_intrinsicTestProfiles hk q u hm hM hMc hρ₁ hW hFine hCoarse i
  obtain ⟨hcurve,V₀,W₀,U,V,hV₀,hW₀,hA,hd,hv,hU,hV,hVW,hX,hfirst,hsecond⟩ :=
    HG r hr h hh hcaps.2.1 z ε hε parent q k hk g
  have Htest := Hmodel.movingBellTestPacket (r := rsp) (n := 3*N) parent q i (by dsimp only [N]; omega) hK
    V₀ W₀ U V (hcurve.of_le (by simp)) hδ hA hd hv hU hV
    (hV₀.of_le (by simp)) (hW₀.of_le (by simp)) hVW hX hfirst hsecond HI
  have htestCoef : (bellFineCoefficient rsp+bellCoarseCoefficient rsp*(max 1 Mc)^3)*
      movingTestProfileUniformCoefficient rsp (3*N) K ≤ Dt :=
    movingTestProfileCoefficient_le_finiteBudget bellFineCoefficient bellCoarseCoefficient Aprofile Mc hrsp hN hN₃
  have htestMono :
      ((bellFineCoefficient rsp+bellCoarseCoefficient rsp*(max 1 Mc)^3)*M^N)*
        movingTestProfileUniformCoefficient rsp (3*N) K*W^(3*N) ≤ Dt*M^N*W^(3*N) := by
    have Hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htestCoef (pow_nonneg (zero_le_one.trans hM) N))
      (pow_nonneg (zero_le_one.trans hW) (3*N))
    convert Hmul using 1
    ring
  have Htest' := Htest.mono_noise htestMono (by dsimp only [N]; omega : 3*N+2 ≤ 11)
  obtain ⟨s₀,s₁,t₀,t₁,t₂,hSmooth,hJets,hScore,hSecond⟩ :=
    HS r hr h hh hcaps.2.2.2.2.1 z ε hε q parent k hk g
  have hNoisePow (t : ℝ) : L*(1+|t|)^3 ≤ L*(1+|t|)^11 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)) (zero_le_one.trans hL)
  have hDensity (t : ℝ) (y : Vec3) :
      (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t))) =ᶠ[𝓝 k]
      fun κ => frozenCompletedFineLogInput β α a (r-h) h z ε q parent κ g t y := by
    filter_upwards [(show IsOpen frozenRowsKDomain from isOpen_Ioo).mem_nhds hk] with κ hκ
    dsimp only [p]
    rw [frozenRowsMovingParameterCurve_eq_physical β α a (r-h) h z ε hh.le parent q g]
    exact Hmodel.translated_density_eq_fine hκ parent q g t y
  have hScore' (t : ℝ) (y : Vec3) : σ*deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t))) k =
      s₀ t y+δ*s₁ t y := by rw [(hDensity t y).deriv_eq]; exact hScore t y
  have hSecond' (t : ℝ) (y : Vec3) : σ^2*deriv (deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t)))) k =
      t₀ t y+δ*t₁ t y+δ^2*t₂ t y := by rw [(hDensity t y).deriv.deriv_eq]; exact hSecond t y
  have hQf := (HQ r hr h hh hcaps.2.2.1 z ε hε q u k hk).of_le hrsp₂
  have hValues := frozenRowsTranslated_head_values β α a (r-h) h z ε k Hmodel.mass_pos hh.le q u
  have hmass : Real.exp (c.logMass (p k)) = a*frozenUnitMass q :=
    hValues.1.trans (frozenRowsHead_mass_eq β a h k hh.le q)
  have hmean : c.mean (p k) = frozenRowsCompletedMeanLinear β α a (r-h) h z ε q.val k := hValues.2.1
  have hnoise : c.noise (p k) = frozenRowsCompletedHeadDirection β α a (r-h) h z ε q.val k := hValues.2.2.1
  have hbudget := HT rsp hrsp (c.mean (p k)) (by rw [hmean]; exact hA)
  have Hresult := spatialBound_parameterCurveKJet_affineAverage c (Hmodel.potential_regular (q.val+1))
    (Hmodel.bell_smooth q i) (hcurve.of_le (by simp)) (by omega : 2 ≤ 3*N) hQf
    (by positivity : 0 ≤ Dt*M^N*W^(3*N)) (zero_le_one.trans hL) hδ hK (by rw [hnoise]; exact hv)
    (by rw [hmass]; exact hm) Htest'
    s₀ s₁ t₀ t₁ t₂ (hSmooth.1.of_le (by exact_mod_cast hrsp))
    (hSmooth.2.1.of_le (by exact_mod_cast hrsp)) (hSmooth.2.2.1.of_le (by exact_mod_cast hrsp))
    (hSmooth.2.2.2.1.of_le (by exact_mod_cast hrsp)) (hSmooth.2.2.2.2.of_le (by exact_mod_cast hrsp))
    (fun t => ((hJets t).1.of_le hrsp).mono (hNoisePow t) le_rfl)
    (fun t => ((hJets t).2.1.of_le hrsp).mono (hNoisePow t) le_rfl)
    (fun t => ((hJets t).2.2.1.of_le hrsp).mono (hNoisePow t) le_rfl)
    (fun t => ((hJets t).2.2.2.1.of_le hrsp).mono (hNoisePow t) le_rfl)
    (fun t => ((hJets t).2.2.2.2.of_le hrsp).mono (hNoisePow t) le_rfl)
    hScore' hSecond' hbudget
  convert Hresult using 1
  dsimp only [E,rsp,N,W]
  ring

end SKBarriers2.Corner
