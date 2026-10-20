module

public import ComparisonSignedCavityInheritedGammaWorkingScaleMoments
public import ComparisonSignedCavityInheritedGammaLowRestoration
public import ComparisonSignedCavityInheritedGammaLowRestorationPrice
public import ComparisonSignedCavityInheritedBoundedDegreeGammaLowPrice
public import ComparisonSignedCavityActualResourceGammaLowRestorationFromMinimum
public import ComparisonSignedCavityInheritedAllDegreeLowRestorationLedger
public import ComparisonSignedCavityInheritedCanonicalJointLowRestorationPrice
public import ComparisonSignedCavityActualResourceJointLowRestorationFromMinimum
public import ComparisonSignedCavityActualCenteredResourceJointLowRestorationFromMinimum
public import ComparisonSignedCavityActualResourceLowTaylorFromMinimum
public import ComparisonSignedCavityActualCenteredResourceLowTaylorFromMinimum
public import SKProof.Port.ComparisonActualOriginalQGammaHighSecondCore
public import SKProof.Port.ComparisonActualOriginalQLowResourceReadoutSourceAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQRawResourcePairBudget

@[expose] public section
noncomputable section
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_gamma_working_scale_even_moment_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalOriginalQSource M forms).product σ|^(2*dOrder)) 0≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale x W initial)^(2*dOrder) := by
  by_cases ha : 0<aDegree
  · obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
      (D:=D) aDegree dOrder rBound ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨Cp,hCp,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T l t hl ht hT G forms initial x W hxsx hxW hmass
    exact hj U T l t hl ht hT G forms initial x W hxsx hxW hmass
  · have hz : aDegree=0:=by omega
    subst aDegree
    refine ⟨1,by norm_num,Filter.Eventually.of_forall (fun n=>?_)⟩
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    refine Filter.Eventually.of_forall (fun jGrid=>?_)
    dsimp only
    intro U T l t hl ht hT G forms initial x W hxsx hxW hmass
    have ho : MassOrdered 0 (finiteCutMasses us jGrid):=finiteCutMasses_ordered us hus jGrid
    have Hp0 : sourceMonomialScale x W initial=1 := by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    simp_rw [native_canonical_source_zero_degree_product_original_q]
    simp only [abs_one,one_pow,pow_zero,mul_one,Hp0]
    rw [T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
    apply one_le_pow₀
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _)
      (by positivity)

theorem eventually_actual_minimum_inherited_canonical_gamma_low_restoration_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(a : T.Slot) (star : ℕ),star<U →
          |nativeGammaProjectedLowSecondRestoration T a star U q b h K
            (restCenteredFixedForkKernel n b S star 0) (G.canonicalOriginalQSource M forms).restProduct| ≤
            4*((rBound:ℝ)+1)*ClockTree.absJetVariation (rBound+2) 2*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ)))*
              (Cq*(1+Ccut)*W)^2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_gamma_working_scale_even_moment_original_q
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) 4 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a star hs
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale x W initial
  let rho:=Cq*(1+Ccut)*W
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have hxscale : M.xs ≤ W:=hxsx.trans hxW
  have HW : 0<W:=M.hxs.trans_le hxscale
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hd : 0 ≤ d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock j (_hj : j ≤ as.length) : |b j| ≤ Mclock∧|h j| ≤ Mclock∧|K j| ≤ Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have H:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [H])
    have HK : K j ≤ 2*Cf+Temp := by
      have H:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.sweepBf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hfield.1]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hfield.1],by linarith,by linarith⟩
  have HQmoment l (hl : l∈Icc (0:ℝ) 1) j (hj : j ≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0 ≤ rho^8 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l 1 1 hl (by norm_num) (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W := by nlinarith only [hxscale,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (8:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  apply native_gamma_projected_low_second_restoration_wholeLaw_bound n U star q b h S T ho hT
    (G.canonicalOriginalQSource M forms).restProduct a hs hU HC Hrho HM Hd
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    _ Hclock _ HQmoment
  · intro l hl
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct] using
      hgrid U T l 1 hl (by norm_num) hT G forms initial x W hxsx hxW hmass
  · intro l hl
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf hsource hxs
      ho U hl (show (1:ℝ)∈Icc 0 1 by norm_num) _ (hs.le.trans hU)
    dsimp only at H
    simpa only [hs,ite_true] using H

theorem eventually_actual_minimum_inherited_canonical_gamma_LOW_restoration_price_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(a : T.Slot) (star : ℕ),star<U →
          |nativeGammaProjectedLowSecondRestoration T a star U q b h K
            (restCenteredFixedForkKernel n b S star 0) (G.canonicalOriginalQSource M forms).restProduct|  ≤
            C*sourceMonomialScale x W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ)))*W^2 := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_gamma_low_restoration_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let base:=4*((rBound:ℝ)+1)*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^aDegree)*(Cq*(1+Ccut))^2
  have hbase : 0 ≤ base:=by
    have HV:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [base]
    positivity
  refine ⟨base+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a star hs
  have Hraw:=hj U T hU hT G forms initial x W hxsx hxW hcut hmass a star hs
  let Z:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf (finiteCutMasses us jGrid) star+1/(n+1:ℕ))
  have hZ : 0 ≤ Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hd : 0 ≤ d:=by
    dsimp only [d,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
    (show 0 ≤ Z*d*W^2 by positivity)
  apply Hraw.trans
  convert Hmajor using 1 <;> dsimp only [base,Z,d] <;> ring

theorem eventually_actual_minimum_inherited_bounded_degree_gamma_LOW_restoration_price_original_q
    (degree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀aDegree : ℕ,aDegree ≤ degree →
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀(a : T.Slot) (star : ℕ),star<U →
          |nativeGammaProjectedLowSecondRestoration T a star U q b h K
            (restCenteredFixedForkKernel n b S star 0) (G.canonicalOriginalQSource M forms).restProduct| ≤
            C*sourceMonomialScale x W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ)))*W^2 := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_gamma_LOW_restoration_price_original_q
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro aDegree hdegree U T hU hT G forms initial x W hxsx hxW hcut hmass slot star hs
  let a : Fin (degree+1):=⟨aDegree,by omega⟩
  have Hraw:=hj a U T hU hT G forms initial x W hxsx hxW hcut hmass slot star hs
  let as:=finiteCutMasses us jGrid
  have hZ : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx)
      ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hd : 0 ≤ actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ)):=
    mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  exact Hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdom a) hZ) hd) (sq_nonneg W))

theorem eventually_actual_minimum_inherited_resource_gamma_LOW_restoration_from_minimum_original_q
    (degree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        |(W⁻¹)^k*nativeActualResourceGammaSecondRestoration_original_q M U P false| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ)))*W^2) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_degree_gamma_LOW_restoration_price_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnC M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW _hW1 hmi hms hcut
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  let as:=finiteCutMasses us jGrid
  let profile:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ))*W^2
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hprofile : 0 ≤ profile:=by
    have HD : 0 ≤ nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as star+1/(n+1:ℕ):=
      add_nonneg (Real.sqrt_nonneg _) (by positivity)
    exact mul_nonneg (mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) HD) (sq_nonneg W)
  have HliveDegree : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  have HL:=hjC P.live.factors.length HliveDegree U T hU hT G (fun _=>.centered) I x W hx hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass x W hmi hms) P.live.test.target star hs
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have H:=actual_resource_gamma_second_restoration_normalized_profile_le_original_q M hP hdepth ho hi
    hs false hA hx hxW (mul_nonneg hC.le hprofile) HP (by
      dsimp only
      convert HL using 1 <;> first
      | rfl
      | (dsimp only [G,profile,as,nativeGammaProjectedSecondRestoration,Bool.false_eq_true,ite_false];ring))
  apply H.trans_eq
  dsimp only [profile,as]
  ring

theorem eventually_actual_minimum_inherited_all_degree_canonical_low_restoration_ledger_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ)))*
              (Cq*(1+Ccut)*W)^2 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_LOW_taylor_continuum_even_all_degree_original_q
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) 4 (by norm_num) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale M.xs W initial
  let rho:=Cq*(1+Ccut)*W
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HM : 0 ≤ Mclock:=by dsimp [Mclock];positivity
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial i).le)
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have Hd : 0 ≤ d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hclock j (_hj : j ≤ as.length) : |b j| ≤ Mclock∧|h j| ≤ Mclock∧|K j| ≤ Mclock := by
    have Hfield:=hsource _ (partitionPoint_mem as ho j)
    have Hh : h j ≤ 2*Cf := by
      have H:=mul_le_mul_of_nonneg_left
        (show M.xs+partitionPoint 0 as j ≤ 2 by linarith [(partitionPoint_mem as ho j).2]) hCf
      exact Hfield.2.trans (by linarith only [H])
    have HK : K j ≤ 2*Cf+Temp := by
      have H:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.sweepBf (partitionPoint 0 as j)))
      dsimp only [K]
      linarith [Hfield.1]
    rw [abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (hK0 j)]
    dsimp only [Mclock]
    exact ⟨by linarith [Hfield.1],by linarith,by linarith⟩
  have HQmoment l (hl : l∈Icc (0:ℝ) 1) j (hj : j ≤ as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l 1 b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8) 0 ≤ rho^8 := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l 1 1 hl (by norm_num) (by norm_num) j hj
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^8)=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by norm_num : (8:ℕ)≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  apply native_centered_low_gamma_low_restoration_wholeLaw_bound n U q b h S T ho hT
    (G.canonicalOriginalQSource M forms).restProduct a z hU haz HC Hrho HM Hd
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    _ Hclock _ HQmoment
  · intro l hl
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct] using
      hgrid U T l 1 hl (by norm_num) hT G forms initial W hxW hmass
  · intro l hl
    have H:=actual_minimum_inherited_current_low_error_radius_le_original_original_q M Temp Cf hTemp hCf hsource hxs
      ho U hl (show (1:ℝ)∈Icc 0 1 by norm_num) _ (T.splitIndex_le_clockLength a z)
    dsimp only at H
    simpa only [haz,ite_true] using H

theorem eventually_actual_minimum_inherited_canonical_joint_LOW_restoration_price_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          |nativeCenteredLowGammaLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z|  ≤
            C*sourceMonomialScale M.xs W initial*
              (actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ)))*W^2 := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_inherited_all_degree_canonical_low_restoration_ledger_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let base:=4*(rBound:ℝ)*(rBound+1)*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*Cp^aDegree)*(Cq*(1+Ccut))^2
  have hbase : 0 ≤ base:=by
    have HV:=absJetVariation_nonneg (rBound+2) 2
    dsimp only [base]
    positivity
  refine ⟨base+1,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a z haz
  have Hraw:=hj U T hU hT G forms initial W hxW hcut hmass a z haz
  let Z:=sourceMonomialScale M.xs W initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf (finiteCutMasses us jGrid) (T.splitIndex a z)+1/(n+1:ℕ))
  have hZ : 0 ≤ Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hd : 0 ≤ d:=by
    dsimp only [d,nativeOriginalCutLowErrorRadius]
    exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
    (show 0 ≤ Z*d*W^2 by positivity)
  apply Hraw.trans
  convert Hmajor using 1 <;> dsimp only [base,Z,d] <;> ring

theorem eventually_actual_minimum_inherited_resource_joint_LOW_restoration_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualResourceJointLowRestoration_original_q M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*R*W^2) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_joint_LOW_restoration_price_original_q
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut aSlot z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex aSlot z)+1/(n+1:ℕ))
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR : 0 ≤ R:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
    dsimp only [nativeOriginalCutLowErrorRadius]
    positivity)
  have hprice : 0 ≤ Cmax*R*W^2:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    M.xs W le_rfl hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T hU hT G (fun _=>.centered) I W hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass M.xs W hmi hms) aSlot z haz
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeCenteredLowGammaLowRestoration n q U b h K (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) T
      (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale M.xs W 1 P.live.tags*(Cmax*R*W^2):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ nativeResourceScale M.xs W 1 P.live.tags*R*W^2 by
        exact mul_nonneg (mul_nonneg (actual_resource_raw_scale_pos _ M.hxs (M.hxs.trans_le hxW)).le hR) (sq_nonneg W))
    convert Hdom using 1 <;> ring
  have H:=actual_resource_joint_LOW_normalized_price_le_original_q M hP hdepth ho hi (hs.trans_le hU) hU
    aSlot z hA le_rfl hxW hprice Hpair HL'
  apply H.trans_eq
  ring

theorem eventually_actual_minimum_inherited_centered_resource_joint_LOW_restoration_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointLowRestoration_original_q M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*R*W^2) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_joint_LOW_restoration_from_minimum_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_joint_LOW_restoration_eq_two_resources_original_q M U P ho hU a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

theorem eventually_actual_minimum_inherited_resource_third_LOW_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
        |(W⁻¹)^k*nativeActualResourceThirdLowPart_original_q M U P a z l t| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*W^2*(T.forkCost R+edgeBudget 0 as R)) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_third_LOW_profile_original_q
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut aSlot z l t hl ht
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let cost:=T.forkCost R+edgeBudget 0 as R
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hCost : 0 ≤ cost:=add_nonneg (T.forkCost_nonneg (fun j=>nativeWholeLawErrorRadius_nonneg _ _ _ _ j))
    (edgeBudget_nonneg ho (fun j=>nativeWholeLawErrorRadius_nonneg _ _ _ _ j))
  have hprice : 0 ≤ Cmax*W^2*cost:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    M.xs W le_rfl hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T W l t hU hT hxW hW1 hcut hl ht G (fun _=>.centered) I
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass M.xs W hmi hms) aSlot z
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have HL' : |nativeActualCenteredThirdLowPart n q U b h K T
      (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z l t| ≤
      nativeResourceScale M.xs W 1 P.live.tags*(Cmax*W^2*cost):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ W^2*nativeResourceScale M.xs W 1 P.live.tags*cost by
        exact mul_nonneg (mul_nonneg (sq_nonneg W) (actual_resource_raw_scale_pos _ M.hxs (M.hxs.trans_le hxW)).le) hCost)
    convert Hdom using 1 <;> ring
  have H:=actual_resource_third_LOW_normalized_profile_le_original_q M hP hdepth ho hi (hs.trans_le hU)
    aSlot z l t hA le_rfl hxW hprice Hpair HL'
  apply H.trans_eq
  ring

theorem eventually_actual_minimum_inherited_centered_resource_third_LOW_from_minimum_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceThirdLowPart_original_q M U P a z l t| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*W^2*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_third_LOW_from_minimum_original_q
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z l t hl ht
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_third_LOW_eq_two_resources_original_q M U P ho a z l t,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z l t hl ht
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z l t hl ht
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
