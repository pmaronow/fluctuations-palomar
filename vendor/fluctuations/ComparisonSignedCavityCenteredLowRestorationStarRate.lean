module

public import ComparisonSignedCavityCenteredLowRestorationLinearity
public import ComparisonSignedCavityCanonicalLowRestorationStarRate
public import ComparisonSignedCavityConstantLowRestorationStarRate
public import ComparisonSignedCavityCanonicalContinuumMoments
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_rest_mean_abs_le_square (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
      (fun σ=>|P (T.cavityAssignment σ).1|^2) 0 ≤ A^2) :
    |nativeOriginalRestTestExpectation n q U b h K T P| ≤ A := by
  have HC:=T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho 0
    (cutFullVariance n q U 1 1 b h K) (fun σ=>P (T.cavityAssignment σ).1) (fun _=>1) 0
  simp only [mul_one,one_pow,T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho] at HC
  simp only [sq_abs] at hP
  have H : (nativeOriginalRestTestExpectation n q U b h K T P)^2 ≤ A^2:=HC.trans hP
  rw [←sq_abs] at H
  exact (sq_le_sq₀ (abs_nonneg _) hA).mp H

theorem actual_centered_canonical_low_restoration_star_rate
    (aDegree rBound : ℕ) (ha : 0 < aDegree)
    (Bclock Temp Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Lwin Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n)) :
    ∃Ccenter : ℝ,0 < Ccenter ∧ ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)),partitionPoint 0 as U ≤ Ccut*W n→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale (M n).xs (W n) initial e)→
        ∀a z : T.Slot,T.splitIndex a z=star→star < U→
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (nativeOriginalCenteredRestTest n q U b h K T
              (G.canonicalMinimumSource (M n) forms).restProduct) a z|≤
            Ccenter*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(W n*(M n).xs^2)*
              sourceMonomialScale (M n).xs (W n) initial := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_square_even_moment
    (D:=D) aDegree 1 rBound ha (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HR:=actual_canonical_low_restoration_star_rate aDegree rBound ha Bclock Temp Cmass Ccut
    hTemp hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt M W hcanonical hWlim hb hh w hw
  have H1:=actual_constant_low_restoration_star_rate rBound Bclock Temp Ccut hTemp hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hcanonical hWlim hb hh w hw
  let Mc:=4*bareSourceClockConstant cl Az D+2*Temp
  let Cmean:=Real.exp (wholeLawRowComparisonConstant rBound*Mc)*Cp^aDegree
  refine ⟨1+Cmean,by dsimp [Cmean];positivity,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [HP,HR,H1,HW] with n hnP hnR hn1 hnW
  have hxsW : (M n).xs ≤ W n:=by rw [hcanonical];exact le_max_left _ _
  intro L us hus hret hmesh hstar
  filter_upwards [hnP (M n) (hb n) (hh n) (hxsW.trans hnW) L us hus hret hmesh,
    hnR L us hus hret hmesh hstar,hn1 L us hus hret hmesh hstar] with jGrid hgridP hgridR hgrid1
  dsimp only at hgridP hgridR hgrid1 ⊢
  intro U T hU hT G forms initial hcut hmass a z hsplit hlow
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource (M n) forms).restProduct
  let p0:=sourceMonomialScale (M n).xs (W n) initial
  let saving:=((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(W n*(M n).xs^2)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hp0 : 0 ≤ p0:=by
    dsimp only [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M n).hxs
      ((M n).hxs.trans_le hxsW) initial e).le
  have hsaving : 0 ≤ saving:=by
    dsimp only [saving]
    have hW : 0 ≤ W n:=((M n).hxs.trans_le hxsW).le
    positivity
  have hmean : |nativeOriginalRestTestExpectation n q U b h K T P| ≤ Cmean*p0 := by
    apply native_original_rest_mean_abs_le_square n q U b h K T ho P (by dsimp [Cmean];positivity)
    have H:=hgridP U T 1 1 (by norm_num) (by norm_num) hT G forms initial (W n) hxsW hmass
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,P,Cmean,Mc,p0,
      mul_assoc] using H
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr ((M n).inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr ((M n).inherited_hf_monotone hu hv huv)) as ho
  have hK0 : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho
  have HE:=native_centered_low_gamma_low_restoration_original_center n q U b h K S T ho P a z
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hU
  have HR':=hgridR U T hU hT G forms initial hcut hmass a z hsplit hlow
  have H1':=hgrid1 U T hU hT hcut a z hsplit hlow
  change |nativeCenteredLowGammaLowRestoration n q U b h K S T
    (nativeOriginalCenteredRestTest n q U b h K T P) a z| ≤ _
  rw [HE]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have HB:=mul_le_mul hmean H1' (abs_nonneg _) (mul_nonneg (by dsimp [Cmean];positivity) hp0)
  have HH:=add_le_add HR' HB
  apply HH.trans_eq
  dsimp only [p0,saving]
  ring

end OAI.SKFluctuations.Cavity
