module

public import ComparisonSignedCavityActualSmallCutCanonicalOldMoment
public import ComparisonSignedCavityInheritedAllDegreeContinuumMoments
public import ComparisonSignedCavityInheritedOriginalScalarLowJets
public import ComparisonSignedCavityInheritedFixedLowOneHigh
public import ComparisonSignedCavityInheritedFixedLowTwoHigh
public import ComparisonSignedCavityInheritedConstantHighSource
public import ComparisonSignedCavityInheritedConstantTwoHighSource
public import ComparisonSignedCavityInheritedTransientHighBudget
public import ComparisonSignedCavityInheritedTransientHighZero
public import ComparisonSignedCavityInheritedTransientLowPartBudget
public import ComparisonSignedCavityInheritedTransientLowZeroBudget
public import ComparisonSignedCavityInheritedCenteredTransientLowPart
public import ComparisonSignedCavityInheritedCanonicalThirdLowProfile
public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonSignedCavityInheritedCenteredFixedLowOneHigh
public import ComparisonSignedCavityInheritedCenteredFixedLowTwoHigh
public import ComparisonSignedCavityInheritedCenteredTransientHigh
public import ComparisonSignedCavityInheritedConstantCenteredFixedLowOneHigh
public import ComparisonSignedCavityInheritedConstantCenteredFixedLowTwoHigh
public import ComparisonSignedCavityInheritedConstantCenteredTransientHigh
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 38000000
set_option linter.unusedVariables false

theorem native_canonical_source_zero_degree_product_original_q {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n 0 T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin 0→NativeSourceFactorForm) (σ : T.Assignment) :
    (G.canonicalOriginalQSource M forms).product σ=1 := by
  simp only [ActualNaturalBoundaryShape.product,fullBoundaryAffineProduct,Fin.prod_univ_zero]

theorem eventually_actual_minimum_inherited_LOW_taylor_continuum_even_all_degree_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
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
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalOriginalQSource M forms).product σ|^(2*dOrder)) 0≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              sourceMonomialScale M.xs W initial)^(2*dOrder) := by
  by_cases ha : 0<aDegree
  · obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
      (D:=D) aDegree dOrder rBound ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨Cp,hCp,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T l t hl ht hT G forms initial W hxW hmass
    exact hj U T l t hl ht hT G forms initial M.xs W le_rfl hxW hmass
  · have hz : aDegree=0:=by omega
    subst aDegree
    refine ⟨1,by norm_num,Filter.Eventually.of_forall (fun n=>?_)⟩
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    refine Filter.Eventually.of_forall (fun jGrid=>?_)
    dsimp only
    intro U T l t hl ht hT G forms initial W hxW hmass
    have ho : MassOrdered 0 (finiteCutMasses us jGrid):=finiteCutMasses_ordered us hus jGrid
    have Hp0 : sourceMonomialScale M.xs W initial=1 := by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    simp_rw [native_canonical_source_zero_degree_product_original_q]
    simp only [abs_one,one_pow,pow_zero,mul_one,Hp0]
    rw [T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
    apply one_le_pow₀
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _)
      (by positivity)

theorem eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ck : ℝ,0<Ck ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
      ∀(us : List PositiveMass) (jGrid : ℕ), (∀u∈us,u.val≤1) →
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W → l∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(a z : T.Slot) (k : ℕ),
          |cutLowJet n q U b h K T (fun σ=>sitePair T a z (T.cavityAssignment σ).2)
            (cavityEmbed 0) k l 0|≤jetVariation rBound k*(Ck*W)^k := by
  obtain ⟨Cs,hCs,HS⟩:=ActualThetaZeroOverlapMinimum.eventually_actual_mass_mean_upper_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cscalar:=Cf+Temp*Cs
  have hCscalar : 0≤Cscalar:=by dsimp [Cscalar];positivity
  let Ck:=Cscalar*(1+Ccut)+1
  have hCk : 0<Ck:=by dsimp [Ck];positivity
  refine ⟨Ck,hCk,?_⟩
  filter_upwards [HS] with n hnS
  intro M hs0 hsxs hsource us jGrid hus
  dsimp only
  intro U T W l hxW hcut hl hT a z k
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hxs0 :=M.hxs.le
  have HSunit j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HSunit j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HSunit i).1 (NNReal.coe_nonneg _))
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hfield j : h j≤Cf*(M.xs+partitionPoint 0 as j):=
    (hsource _ (partitionPoint_mem as ho j)).2
  have Hmean j : S j≤Cs*(M.xs+partitionPoint 0 as j):=by
    by_cases hj : 0<partitionPoint 0 as j
    · exact hnS M hs0 hsxs _ ⟨hj,(partitionPoint_mem as ho j).2⟩
    · have hz : partitionPoint 0 as j=0:=le_antisymm (le_of_not_gt hj) (partitionPoint_mem as ho j).1
      dsimp only [S]
      rw [hz,orderedPathS,orderedPathPair_zero]
      positivity
  have Hcap j (hj : j<U) : |K j|≤Ck*W:=by
    rw [abs_of_nonneg (hK0 j)]
    have Hprod:=mul_le_mul (Hb j) (Hmean j) (HSunit j).1 hTemp
    have Hlocal : K j≤Cscalar*(M.xs+partitionPoint 0 as j):=by
      dsimp only [K,Cscalar]
      nlinarith only [Hprod,Hfield j]
    have Hmass:=partitionPoint_mono as ho hj.le
    have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W:=by nlinarith only [Hmass,hcut,hxW]
    have HH:=(Hlocal.trans (mul_le_mul_of_nonneg_left Hscale hCscalar))
    have HW:=hW
    dsimp only [Ck]
    nlinarith only [HH,HW]
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ (cavityEmbed 0)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm k hl (by norm_num)]
  have H:=T.disorderProfileJets_abs_le (fullWeight_pos n) (fullFeature n) ho
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K))) hT
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (C:=1) (by norm_num)
    (mul_nonneg hCk.le hW) (fun σ=>by simp only [sitePair_apply,abs_mul,abs_spinValue,one_mul,le_refl])
    (fun A hA j σ τ=>by
      rw [(List.mem_replicate.mp hA).2]
      exact native_scalar_low_profile_abs_le n U b h K (mul_nonneg hCk.le hW) Hcap j σ τ)
    0 (cutFullVariance n q U l 0 b h K) (cavityEmbed 0)
  simpa only [List.length_replicate,mul_one] using H

theorem eventually_actual_minimum_inherited_canonical_fixed_low_one_high_budget_original_q
    (aDegree k rBound : ℕ) (ha : 0<aDegree) (hk : 0<k)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) k 1 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*(Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) (2*k) (by omega) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t s hU hl ht hs hT G forms initial x W hxsx hxW hcut hmass es
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
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have HW : 0<W:=(M.hxs.trans_le hxsx).trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es|^4) 0≤C^4 := by
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
    exact hgrid U T l t hl ht hT G forms initial x W hxsx hxW hmass
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k) := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t s hl ht hs j hj
      rw [show 2*(2*k)=4*k by omega] at Hraw
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxsx,hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k))=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*k≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_fixed_low_one_high_wholeLaw_first_bound n U k hk q b h K T ho hT _ hl ht HC Hrho
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment HQmoment

theorem eventually_actual_minimum_inherited_canonical_fixed_low_two_high_budget_original_q
    (aDegree k rBound dOld ellLow : ℕ) (ha : 0<aDegree) (hdOld : 0<dOld) (hellLow : 0<ellLow)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOld:ℝ))
    (hLowOrder : (2*(p/(p-2)))*(k:ℝ)≤((2*ellLow:ℕ):ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) k 2 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*ClockTree.absJetVariation (rBound+4) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*(Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
    (D:=D) aDegree dOld rBound ha hdOld Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) ellLow hellLow Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t s hU hl ht hs hT G forms initial x W hxsx hxW hcut hmass es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale x W initial
  let rho:=Cq*(1+Ccut)*W
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have HW : 0<W:=(M.hxs.trans_le hxsx).trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  let P:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es
  have HrawOld:=hgrid U T l t hl ht hT G forms initial x W hxsx hxW hmass
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 P
      (by have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2))≤((2*dOld:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [P,abs_mul,native_site_monomial_abs_one,mul_one,Real.rpow_natCast,C,law,q,b,h,S,K,Mclock,as] using HrawOld
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hhigh:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0≤rho^((2*(p/(p-2)))*(k:ℝ)) := by
    by_cases hk0 : k=0
    · simp only [hk0,Nat.cast_zero,mul_zero,Real.rpow_zero]
      exact le_of_eq ((ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0)
    · have hek : 0<(2*(p/(p-2)))*(k:ℝ):=by
        have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith)
        have Hk : 0<(k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hk0
        positivity
      apply (ClockTree.pairClock as j).disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0
        (fun σ=>ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) hek hLowOrder Hrho.le
      simp only [Real.rpow_natCast]
      by_cases hju : j<U
      · have Hraw:=hgridQ U l t s hl ht hs j hj
        apply Hraw.trans
        apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
        dsimp only [rho]
        have Hmass:=partitionPoint_mono as ho hju.le
        have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W:=by nlinarith only [hxsx,hxW,hcut,Hmass]
        exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
      · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
            (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*ellLow))=fun _=>0:=by
          funext σ
          simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
            zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 2*ellLow≠0)]
        rw [HE]
        simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
        exact pow_nonneg Hrho.le _
  exact native_fixed_low_two_high_wholeLaw_bound n U k q b h K T ho hT P hl ht HC Hrho
    (show 0≤2*Temp by positivity) hp
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment
    (fun j _=>Hhigh j) HQmoment

theorem eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (k rBound : ℕ) (hk : 0<k)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>siteMonomial T σ es) k 1 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) (2*k) (by omega) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T l t s hU hl ht hs hT W hxW hcut es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let C : ℝ:=1
  let rho:=Cq*(1+Ccut)*W
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0≤C:=by norm_num [C]
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|siteMonomial T σ es|^4) 0≤C^4:=by
    simp only [native_site_monomial_abs_one,C,one_pow]
    exact le_of_eq (T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 (cutFullVariance n q U l t b h K) 0)
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k) := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t s hl ht hs j hj
      rw [show 2*(2*k)=4*k by omega] at Hraw
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k))=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*k≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  simpa only [C,mul_one] using native_fixed_low_one_high_wholeLaw_first_bound n U k hk q b h K T ho hT (fun σ=>siteMonomial T σ es) hl ht HC Hrho
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment HQmoment

theorem eventually_actual_minimum_inherited_constant_fixed_low_two_high_budget_original_q
    (k rBound ellLow : ℕ) (hellLow : 0<ellLow)
    (p : ℝ) (hp : 2<p)
    (hLowOrder : (2*(p/(p-2)))*(k:ℝ)≤((2*ellLow:ℕ):ℝ))
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cq : ℝ,0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀es : List T.Slot,
          |nativeFixedLowHighProfile n q U b h K T
            (fun σ=>siteMonomial T σ es) k 2 s l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*ClockTree.absJetVariation (rBound+4) k*
              (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*(Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) ellLow hellLow Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U T l t s hU hl ht hs hT W hxW hcut es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let C : ℝ:=1
  let rho:=Cq*(1+Ccut)*W
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0≤C:=by norm_num [C]
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  let P:=fun σ=>siteMonomial T σ es
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0≤C^(2*(p/(p-2))):=by
    simpa only [C,Real.one_rpow,P] using (native_site_monomial_rpow_moment_one n T ho law es (2*(p/(p-2)))).le
  have Hb j : b j≤Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hhigh:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0≤rho^((2*(p/(p-2)))*(k:ℝ)) := by
    by_cases hk0 : k=0
    · simp only [hk0,Nat.cast_zero,mul_zero,Real.rpow_zero]
      exact le_of_eq ((ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0 law 0)
    · have hek : 0<(2*(p/(p-2)))*(k:ℝ):=by
        have Hq : 0<p/(p-2):=div_pos (by linarith) (by linarith)
        have Hk : 0<(k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hk0
        positivity
      apply (ClockTree.pairClock as j).disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0
        (fun σ=>ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) hek hLowOrder Hrho.le
      simp only [Real.rpow_natCast]
      by_cases hju : j<U
      · have Hraw:=hgridQ U l t s hl ht hs j hj
        apply Hraw.trans
        apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
        dsimp only [rho]
        have Hmass:=partitionPoint_mono as ho hju.le
        have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W:=by nlinarith only [hxW,hcut,Hmass]
        exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
      · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U s b h K) j
            (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*ellLow))=fun _=>0:=by
          funext σ
          simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
            zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 2*ellLow≠0)]
        rw [HE]
        simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
        exact pow_nonneg Hrho.le _
  simpa only [C,mul_one] using native_fixed_low_two_high_wholeLaw_bound n U k q b h K T ho hT P hl ht HC Hrho
    (show 0≤2*Temp by positivity) hp
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment
    (fun j _=>Hhigh j) HQmoment

theorem eventually_actual_minimum_inherited_canonical_transient_high_budget_original_q
    (aDegree k rBound : ℕ) (ha : 0<aDegree) (hk : 0<k)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀es : List T.Slot,
          |nativeTransientHighJet n q U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) 0 k l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale x W initial)*(Cq*(1+Ccut)*W)^k*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K)
                (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp,Cq,hCp,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_one_high_budget_original_q
    (D:=D) aDegree k rBound ha hk Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass es
  exact hj U T l t t hU hl ht ht hT G forms initial x W hxsx hxW hcut hmass es

theorem eventually_actual_minimum_inherited_canonical_transient_high_zero_budget_original_q
    (aDegree rBound : ℕ) (ha : 0<aDegree)
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀es : List T.Slot,
          |nativeTransientHighJet n q U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) 0 0 l t|≤
            pairForkVariation rBound*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*sourceMonomialScale x W initial)*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
    (D:=D) aDegree 1 rBound ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht hT G forms initial x W hxsx hxW hmass es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let A:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (4*Cf+2*Temp))*Cp^aDegree*sourceMonomialScale x W initial
  let P:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hC : 0≤C:=by dsimp [C];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law (fun σ=>P σ^2) 0≤C^2:=by
    have HH:=hgrid U T l t hl ht hT G forms initial x W hxsx hxW hmass
    have HE : (fun σ=>P σ^2)=(fun σ=>|(G.canonicalOriginalQSource M forms).product σ|^2):=by
      funext σ
      rw [←sq_abs]
      simp only [P,abs_mul,native_site_monomial_abs_one,mul_one]
    rw [HE]
    simpa only [Nat.mul_one,law,q,b,h,S,K,C,as] using HH
  have HB:=T.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2 (fullWeight_pos n) (fullFeature n)
    ho 0 law 0 hT P hC HPmoment (ReplicaTree.coordinateProfile (fullFeature n) A)
    (fun σ=>fullFeature_coordinateProfile_self n A as.length σ)
    (nativeWholeLawErrorRadius_nonneg n as law A)
    (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
  simpa only [nativeTransientHighJet,List.replicate_zero,List.nil_append,List.map_cons,List.map_nil,
    nativeWholeLawProfileCost,Real.rpow_one,P,C,law,A,q,b,h,K,S,as] using HB

theorem eventually_actual_minimum_inherited_canonical_transient_low_part_budget_original_q
    (aDegree k rBound : ℕ) (hk : 0<k)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀(i star : ℕ) (part : NativeTransientLowErrorPart) (es : List T.Slot),
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) 0 part k l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*(Cq*(1+Ccut)*W)^k*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_LOW_taylor_continuum_even_all_degree_original_q
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_continuum_low_profile_moment_original_q
    (D:=D) (2*k) (by omega) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part es
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
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial i).le)
  have HW : 0<W:=M.hxs.trans_le hxW
  have Hrho : 0<rho:=by dsimp [rho];positivity
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es|^4) 0≤C^4 := by
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
    exact hgrid U T l t hl ht hT G forms initial W hxW hmass
  have HQmoment j (hj : j≤as.length) : (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0≤rho^(4*k) := by
    by_cases hju : j<U
    · have Hraw:=hgridQ U l t t hl ht ht j hj
      rw [show 2*(2*k)=4*k by omega] at Hraw
      apply Hraw.trans
      apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      dsimp only [rho]
      have Hmass:=partitionPoint_mono as ho hju.le
      have Hscale : M.xs+partitionPoint 0 as j≤(1+Ccut)*W := by nlinarith only [hxW,hcut,Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
    · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k))=fun _=>0 := by
        funext σ
        simp only [ReplicaTree.coordinateProfile,cutLSlope,hju,ite_false,Pi.zero_apply,
          zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*k≠0)]
      rw [HE]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hrho.le _
  exact native_transient_low_part_wholeLaw_first_bound n U i star k hk q b h K T ho hT _ part hl ht HC Hrho
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm HPmoment HQmoment

theorem eventually_actual_minimum_inherited_canonical_transient_low_part_zero_budget_original_q
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp : ℝ,0<Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀(i star : ℕ) (part : NativeTransientLowErrorPart) (es : List T.Slot),
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es) 0 part 0 l t|≤
            ClockTree.pairForkVariation rBound*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_LOW_taylor_continuum_even_all_degree_original_q
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht hT G forms initial W hxW hmass i star part es
  let as:=finiteCutMasses us jGrid
  let Mclock:=4*Cf+2*Temp
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
    sourceMonomialScale M.xs W initial
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
  apply native_transient_low_part_zero_wholeLaw_bound n U i star _ _ _ _ T
    (finiteCutMasses_ordered us hus jGrid) hT _ part HC
  have HE : (fun σ=>((G.canonicalOriginalQSource M forms).product σ*siteMonomial T σ es)^2)=
      (fun σ=>|(G.canonicalOriginalQSource M forms).product σ|^2) := by
    funext σ
    rw [←sq_abs]
    simp only [abs_mul,native_site_monomial_abs_one,mul_one]
  rw [HE]
  simpa only [Nat.mul_one,C,Mclock,as] using hgrid U T l t hl ht hT G forms initial W hxW hmass

theorem eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget_original_q
    (aDegree rBound : ℕ)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i star U : ℕ) (part : NativeTransientLowErrorPart) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W → W≤1 →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,
          |nativeTransientCenteredLowErrorPart n q i star U b h K T
              (G.canonicalOriginalQSource M forms).restProduct (sitePair T a z) 0 part l t|≤
            C*W^2*sourceMonomialScale M.xs W initial*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp0,hCp0,H0⟩:=eventually_actual_minimum_inherited_canonical_transient_low_part_zero_budget_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass hTemp hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_minimum_inherited_canonical_transient_low_part_budget_original_q
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,Cq2,hCp2,hCq2,H2⟩:=eventually_actual_minimum_inherited_canonical_transient_low_part_budget_original_q
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp3,Cq3,hCp3,hCq3,H3⟩:=eventually_actual_minimum_inherited_canonical_transient_low_part_budget_original_q
    (D:=D) aDegree 3 rBound (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let a0:=pairForkVariation rBound*(Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp2^aDegree)*(Cq2*(1+Ccut))^2
  let a3:=pairForkVariation rBound*absJetVariation (rBound+2) 3*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp3^aDegree)*(Cq3*(1+Ccut))^3
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else if i.val=2 then a2 else a3
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=mul_nonneg (pairForkVariation_nonneg _) (by positivity)
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha2 : 0≤a2:=by
    dsimp only [a2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha3 : 0≤a3:=by
    dsimp only [a3]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let c3:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0
  let c2:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0
  let C:=c3+3*c2+1
  have hc3 : 0≤c3:=by dsimp only [c3];exact native_centered_LOW_third_coefficient_nonneg hA hB
  have hc2 : 0≤c2:=by dsimp only [c2];exact native_centered_LOW_second_coefficient_nonneg hA hB
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,H2,H3,HG] with n hn0 hn1 hn2 hn3 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh,hn3 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1 hgrid2 hgrid3
  dsimp only at hgrid0 hgrid1 hgrid2 hgrid3 ⊢
  intro i star U part T l t hU hl ht hT G forms initial W hxW hW1 hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource M forms).product
  let Z:=sourceMonomialScale M.xs W initial
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
    (nativeTransientLowErrorPartDirection n U i star b h K part)
  let Cost:=T.forkCost R+edgeBudget 0 as R
  let f : Fin 4→ℝ:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T P 0 part j l t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0
  let J:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 part j l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0≤Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  have hR j : 0≤R j:=nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have hCost : 0≤Cost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have Hf0:=hgrid0 U T l t hl ht hT G forms initial W hxW hmass i star part []
  have Hf1:=hgrid1 U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part []
  have Hf2:=hgrid2 U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part []
  have Hf3:=hgrid3 U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part []
  simp only [siteMonomial,mul_one] at Hf0 Hf1 Hf2 Hf3
  have hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf3 using 1
      dsimp only [f,A,a3,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
  have hg i : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W l hxW hcut hl hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ (j : Fin 4) (hj : j=2 ∨ j=3) : |J j|≤A j*W^(j:ℕ)*Z*Cost:=by
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    rcases hj with rfl | rfl
    · have HH:=hgrid2 U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part [a,z]
      dsimp only [J]
      rw [HE]
      convert HH using 1 <;> dsimp only [A,a2,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      all_goals norm_num [mul_pow]
      all_goals ring_nf
      all_goals simp
    · have HH:=hgrid3 U T l t hU hl ht hT G forms initial W hxW hcut hmass i star part [a,z]
      dsimp only [J]
      rw [HE]
      convert HH using 1 <;> dsimp only [A,a3,Z,Cost,R,Mclock,P,q,b,h,K,S,as]
      all_goals norm_num [mul_pow]
      all_goals ring_nf
      all_goals simp
  have HH:=native_centered_LOW_parts_product_bound hW hW1 hZ hCost hl A B f g (J 2) (J 3)
    hA hB (hJ 2 (Or.inl rfl)) (hJ 3 (Or.inr rfl)) hf hg
  have Hleft : nativeTransientCenteredLowErrorPart n q i star U b h K T
      (G.canonicalOriginalQSource M forms).restProduct (sitePair T a z) 0 part l t=
      l*(J 3-productJet3 g f 3)+3*(J 2-productJet3 g f 2) := by
    dsimp only [nativeTransientCenteredLowErrorPart,J,f,g]
    simp_rw [←(G.canonicalOriginalQSource M forms).product_eq_restProduct]
    simp only [map_zero,P]
  rw [Hleft]
  apply HH.trans
  have HC : c3+3*c2≤C:=by dsimp only [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 2)) hZ) hCost
  simpa only [Z,Cost,R,q,b,h,K,S,as,c3,c2] using HB

theorem eventually_actual_minimum_inherited_canonical_third_LOW_profile_original_q
  (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
  (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
  {m delta cl cu Az C0 Ct D : ℝ}
  (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
  (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
  ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
   ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
    ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
   ∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
   ∀ᶠjGrid : ℕ in atTop,
    let as:=finiteCutMasses us jGrid
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l t : ℝ),U ≤ as.length →
     T.leaves ≤ rBound → M.xs ≤ W → W ≤ 1 → partitionPoint 0 as U ≤ Ccut*W →
     l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
      (initial : Finset (Fin aDegree)),
     (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) → ∀a z : T.Slot,
     let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
     |nativeActualCenteredThirdLowPart n q U b h K T (G.canonicalOriginalQSource M forms).restProduct a z l t| ≤
      C*W^2*sourceMonomialScale M.xs W initial*(T.forkCost R+edgeBudget 0 as R) := by
 obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget_original_q
  (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
  hm hdelta hroom hcl hcu hAz hC0 hCt
 refine ⟨3*C,by positivity,?_⟩
 filter_upwards [H] with n hn
 intro M hs0 hsxs hsource hxs L us hus hret hmesh
 filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
 dsimp only at hj ⊢
 intro U T W l t hU hT hxW hW1 hcut hl ht G forms initial hmass a z
 let as:=finiteCutMasses us jGrid
 let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
 have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
 have HE (part : NativeTransientLowErrorPart) :
   |nativeTransientCenteredLowErrorPart n q 0 0 U b h K T (G.canonicalOriginalQSource M forms).restProduct (sitePair T a z) 0 part l t| ≤
    C*W^2*sourceMonomialScale M.xs W initial*(T.forkCost R+edgeBudget 0 as R):=by
  have HH:=hj 0 0 U part T l t hU hl ht hT G forms initial W hxW hW1 hcut hmass a z
  have HR j (_hj : j ≤ as.length):=native_transient_low_part_radius_le n U 0 0 b h K as
   (cutFullVariance n q U l t b h K) part j
  have HC:=add_le_add (native_forkCost_mono_on_clock T HR) (actual_low_edgeBudget_mono ho HR)
  have hZ : 0 ≤ sourceMonomialScale M.xs W initial:=by
   rw [←source_factor_scale_product]
   exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  exact HH.trans (mul_le_mul_of_nonneg_left HC (by positivity))
 rw [native_actual_centered_third_LOW_part_eq_sum n q 0 0]
 have Habs:=((abs_add_le _ _).trans (add_le_add
  ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving)))
 convert Habs using 1; ring

theorem eventually_actual_minimum_inherited_constant_centered_third_LOW_profile_original_q
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l t : ℝ),U≤as.length →
          T.leaves≤rBound → M.xs≤W → W≤1 → partitionPoint 0 as U≤Ccut*W →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀a z : T.Slot,
          let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
          |nativeActualCenteredThirdLowPart n q U b h K T (fun _=>1) a z l t|≤
            C*W^2*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget_original_q
    (D:=D) 0 rBound Bclock Temp Cf 0 Ccut hTemp hCf (by norm_num) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T W l t hU hT hxW hW1 hcut hl ht a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let G : ActualNaturalBoundaryShape n 0 T:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalOriginalQSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HE (part : NativeTransientLowErrorPart) :
      |nativeTransientCenteredLowErrorPart n q 0 0 U b h K T (fun _=>1) (sitePair T a z) 0 part l t|≤
        C*W^2*(T.forkCost R+edgeBudget 0 as R):=by
    have HH:=hj 0 0 U part T l t hU hl ht hT G forms ∅ W hxW hW1 hcut (fun e=>Fin.elim0 e) a z
    rw [HP] at HH
    simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at HH
    have HR j (_hj : j≤as.length):=native_transient_low_part_radius_le n U 0 0 b h K as
      (cutFullVariance n q U l t b h K) part j
    have HC:=add_le_add (native_forkCost_mono_on_clock T HR) (actual_low_edgeBudget_mono ho HR)
    exact HH.trans (mul_le_mul_of_nonneg_left HC (mul_nonneg hC.le (sq_nonneg W)))
  rw [native_actual_centered_third_LOW_part_eq_sum n q 0 0]
  have Habs:=((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving)))
  convert Habs using 1; ring

theorem eventually_actual_minimum_inherited_canonical_centered_fixed_low_two_one_high_budget_original_q
    (aDegree rBound : ℕ) (ha : 0<aDegree)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),U≤as.length →
          t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,
          |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalOriginalQSource M forms).product a z 2 1 t|≤
            C*W^2*sourceMonomialScale x W initial*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp0,hCp0,H0⟩:=eventually_actual_minimum_inherited_canonical_transient_high_zero_budget_original_q
    (D:=D) aDegree rBound ha Bclock Temp Cf Cmass hTemp hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_one_high_budget_original_q
    (D:=D) aDegree 1 rBound ha (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,Cq2,hCp2,hCq2,H2⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_one_high_budget_original_q
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let a0:=pairForkVariation rBound*(Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp2^aDegree)*(Cq2*(1+Ccut))^2
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else a2
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=mul_nonneg (pairForkVariation_nonneg _) (by positivity)
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha2 : 0≤a2:=by
    dsimp only [a2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0+1
  have hC : 0<C:=by
    have H1:=hA 2
    have H2:=mul_nonneg (hB 0) (hA 2)
    have H3:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (hB 1)) (hA 1)
    have H4:=mul_nonneg (hB 2) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,H2,HG] with n hn0 hn1 hn2 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1 hgrid2
  dsimp only at hgrid0 hgrid1 hgrid2 ⊢
  intro U T t hU ht hT G forms initial x W hxsx hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T 1
  let f : Fin 4→ℝ:=fun i=>nativeFixedLowHighProfile n q U b h K T P i 1 1 0 t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0
  let J:=nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 2 1 1 0 t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T 1
  have Hf0:=hgrid0 U T 0 t (by norm_num) ht hT G forms initial x W hxsx hxW hmass []
  change |nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*siteMonomial T σ []) 0 1 1 0 t|≤_ at Hf0
  have Hf1:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  have Hf2:=hgrid2 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  simp only [siteMonomial,mul_one] at Hf0 Hf1 Hf2
  have hf i (hi : i.val≤2) : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · norm_num at hi
  have hg i (_hi : i.val≤2) : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W 0 (hxsx.trans hxW) hcut (by norm_num) hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 2*W^2*Z*Cost:=by
    have HH:=hgrid2 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    convert HH using 1
    dsimp only [J,A,a2,Z,Cost,Mclock,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_fixed_second_product_bound hW A B f g hB hJ hf hg
  apply HH.trans
  have HC : A 2+B 0*A 2+2*B 1*A 1+B 2*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 2)) hZ) hCost
  simpa only [nativeCenteredFixedLowHigh,f,g,J,Z,Cost,P,q,b,h,K,S,as] using HB

theorem eventually_actual_minimum_inherited_canonical_centered_fixed_low_one_two_high_budget_original_q
    (aDegree rBound dOld ellLow : ℕ) (ha : 0<aDegree) (hdOld : 0<dOld) (hellLow : 0<ellLow)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOld:ℝ))
    (hLowOrder : 2*(p/(p-2))≤((2*ellLow:ℕ):ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),U≤as.length →
          t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,
          |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalOriginalQSource M forms).product a z 1 2 t|≤
            C*W*sourceMonomialScale x W initial*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp0,Cq0,hCp0,hCq0,H0⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_two_high_budget_original_q
    (D:=D) aDegree 0 rBound dOld ellLow ha hdOld hellLow p hp hOrder (by norm_num)
    Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_two_high_budget_original_q
    (D:=D) aDegree 1 rBound dOld ellLow ha hdOld hellLow p hp hOrder (by simpa only [Nat.cast_one,mul_one] using hLowOrder)
    Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let a0:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 0*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let a1:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*(Cq1*(1+Ccut))
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else a1
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have Hpow : 0≤(2*Temp)^((p-2)/p):=Real.rpow_nonneg (mul_nonneg (by norm_num) hTemp) _
  have ha0 : 0≤a0:=by
    dsimp only [a0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) (by positivity)) Hpow) Hpow
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) (by positivity)) Hpow) Hpow) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 1+B 0*A 1+B 1*A 0+1
  have hC : 0<C:=by
    have HH1:=hA 1
    have HH2:=mul_nonneg (hB 0) (hA 1)
    have HH3:=mul_nonneg (hB 1) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,HG] with n hn0 hn1 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1
  dsimp only at hgrid0 hgrid1 ⊢
  intro U T t hU ht hT G forms initial x W hxsx hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p)
  let f : Fin 4→ℝ:=fun i=>nativeFixedLowHighProfile n q U b h K T P i 2 1 0 t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0
  let J:=nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 1 2 1 0 t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T (4/p)
  have Hf0:=hgrid0 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  have Hf1:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  simp only [siteMonomial,mul_one] at Hf0 Hf1
  have hf i (hi : i.val≤1) : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · norm_num at hi
    · norm_num at hi
  have hg i (_hi : i.val≤1) : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W 0 (hxsx.trans hxW) hcut (by norm_num) hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 1*W*Z*Cost:=by
    have HH:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    convert HH using 1
    dsimp only [J,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_fixed_first_product_bound hW A B f g hB hJ hf hg
  apply HH.trans
  have HC : A 1+B 0*A 1+B 1*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    hW) hZ) hCost
  simpa only [nativeCenteredFixedLowHigh,f,g,J,Z,Cost,P,q,b,h,K,S,as] using HB

theorem eventually_actual_minimum_inherited_canonical_centered_transient_HIGH_budget_original_q
    (aDegree rBound : ℕ) (ha : 0<aDegree)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,
          |nativeCenteredTransientHighThird n q U b h K T (G.canonicalOriginalQSource M forms).product a z l t|≤
            C*W^3*sourceMonomialScale x W initial*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cp0,hCp0,H0⟩:=eventually_actual_minimum_inherited_canonical_transient_high_zero_budget_original_q
    (D:=D) aDegree rBound ha Bclock Temp Cf Cmass hTemp hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_minimum_inherited_canonical_transient_high_budget_original_q
    (D:=D) aDegree 1 rBound ha (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,Cq2,hCp2,hCq2,H2⟩:=eventually_actual_minimum_inherited_canonical_transient_high_budget_original_q
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp3,Cq3,hCp3,hCq3,H3⟩:=eventually_actual_minimum_inherited_canonical_transient_high_budget_original_q
    (D:=D) aDegree 3 rBound ha (by norm_num) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let a0:=pairForkVariation rBound*(Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp2^aDegree)*(Cq2*(1+Ccut))^2
  let a3:=pairForkVariation rBound*absJetVariation (rBound+2) 3*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp3^aDegree)*(Cq3*(1+Ccut))^3
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else if i.val=2 then a2 else a3
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=mul_nonneg (pairForkVariation_nonneg _) (by positivity)
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha2 : 0≤a2:=by
    dsimp only [a2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha3 : 0≤a3:=by
    dsimp only [a3]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0+1
  have hC : 0<C:=by
    have H1:=hA 3
    have H2:=mul_nonneg (hB 0) (hA 3)
    have H3:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 1)) (hA 2)
    have H4:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 2)) (hA 1)
    have H5:=mul_nonneg (hB 3) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,H2,H3,HG] with n hn0 hn1 hn2 hn3 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh,hn3 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1 hgrid2 hgrid3
  dsimp only at hgrid0 hgrid1 hgrid2 hgrid3 ⊢
  intro U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalOriginalQSource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1
  let f : Fin 4→ℝ:=fun i=>nativeTransientHighJet n q U b h K T P 0 i l t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0
  let J:=nativeTransientHighJet n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 3 l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T 1
  have Hf0:=hgrid0 U T l t hl ht hT G forms initial x W hxsx hxW hmass []
  have Hf1:=hgrid1 U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass []
  have Hf2:=hgrid2 U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass []
  have Hf3:=hgrid3 U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass []
  simp only [siteMonomial,mul_one] at Hf0 Hf1 Hf2 Hf3
  have hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf3 using 1
      dsimp only [f,A,a3,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
  have hg i : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W l (hxsx.trans hxW) hcut hl hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 3*W^3*Z*Cost:=by
    have HH:=hgrid3 U T l t hU hl ht hT G forms initial x W hxsx hxW hcut hmass [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    convert HH using 1
    dsimp only [J,A,a3,Z,Cost,Mclock,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_third_HIGH_product_bound hW hZ hCost A B f g hA hB hJ hf hg
  apply HH.trans
  have HC : A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 3)) hZ) hCost
  simpa only [nativeCenteredTransientHighThird,f,g,J,Z,Cost,P,q,b,h,K,S,as] using HB

theorem eventually_actual_minimum_inherited_constant_centered_fixed_low_two_one_high_budget_original_q
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),U≤as.length →
          t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀a z : T.Slot,
          |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 2 1 t|≤
            C*W^2*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cq1,hCq1,H1⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (D:=D) 1 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq2,hCq2,H2⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (D:=D) 2 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let a0:=pairForkVariation rBound
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*(Cq2*(1+Ccut))^2
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else a2
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=pairForkVariation_nonneg _
  have ha1 : 0≤a1:=by dsimp only [a1];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have ha2 : 0≤a2:=by dsimp only [a2];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0+1
  have hC : 0<C:=by
    have H1:=hA 2
    have H2:=mul_nonneg (hB 0) (hA 2)
    have H3:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (hB 1)) (hA 1)
    have H4:=mul_nonneg (hB 2) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H1,H2,HG] with n hn1 hn2 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid1 hgrid2
  dsimp only at hgrid1 hgrid2 ⊢
  intro U T t hU ht hT W hxW hcut a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P : T.Assignment→ℝ:=fun _=>1
  let Z : ℝ:=1
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T 1
  let f : Fin 4→ℝ:=fun i=>nativeFixedLowHighProfile n q U b h K T P i 1 1 0 t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0
  let J:=nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 2 1 1 0 t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0≤Z:=by norm_num [Z]
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T 1
  have Hf0:=native_constant_fixed_zero_high_bound n U rBound q b h K T ho hT [] 1 0 t
  have Hf1:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut []
  have Hf2:=hgrid2 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut []
  simp only [siteMonomial] at Hf0 Hf1 Hf2
  have hf i (hi : i.val≤2) : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · norm_num at hi
  have hg i (_hi : i.val≤2) : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W 0 hxW hcut (by norm_num) hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 2*W^2*Z*Cost:=by
    have HH:=hgrid2 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    simp only [P,one_mul]
    convert HH using 1
    dsimp only [J,A,a2,Z,Cost,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_fixed_second_product_bound hW A B f g hB hJ hf hg
  apply HH.trans
  have HC : A 2+B 0*A 2+2*B 1*A 1+B 2*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 2)) hZ) hCost
  simpa only [nativeCenteredFixedLowHigh,f,g,J,Z,Cost,P,q,b,h,K,S,as,mul_one] using HB

theorem eventually_actual_minimum_inherited_constant_centered_fixed_low_one_two_high_budget_original_q
    (rBound ellLow : ℕ) (hellLow : 0<ellLow)
    (p : ℝ) (hp : 2<p)
    (hLowOrder : 2*(p/(p-2))≤((2*ellLow:ℕ):ℝ))
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),U≤as.length →
          t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀a z : T.Slot,
          |nativeCenteredFixedLowHigh n q U b h K T (fun _=>1) a z 1 2 t|≤
            C*W*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cq0,hCq0,H0⟩:=eventually_actual_minimum_inherited_constant_fixed_low_two_high_budget_original_q
    (D:=D) 0 rBound ellLow hellLow p hp (by norm_num)
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq1,hCq1,H1⟩:=eventually_actual_minimum_inherited_constant_fixed_low_two_high_budget_original_q
    (D:=D) 1 rBound ellLow hellLow p hp (by simpa only [Nat.cast_one,mul_one] using hLowOrder)
    Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let a0:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 0*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let a1:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 1*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*(Cq1*(1+Ccut))
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else a1
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have Hpow : 0≤(2*Temp)^((p-2)/p):=Real.rpow_nonneg (mul_nonneg (by norm_num) hTemp) _
  have ha0 : 0≤a0:=by
    dsimp only [a0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) Hpow) Hpow
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) Hpow) Hpow) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 1+B 0*A 1+B 1*A 0+1
  have hC : 0<C:=by
    have HH1:=hA 1
    have HH2:=mul_nonneg (hB 0) (hA 1)
    have HH3:=mul_nonneg (hB 1) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,HG] with n hn0 hn1 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hs0 hsxs hsource hxs L us hus hret hmesh,hn1 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1
  dsimp only at hgrid0 hgrid1 ⊢
  intro U T t hU ht hT W hxW hcut a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P : T.Assignment→ℝ:=fun _=>1
  let Z : ℝ:=1
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p)
  let f : Fin 4→ℝ:=fun i=>nativeFixedLowHighProfile n q U b h K T P i 2 1 0 t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0
  let J:=nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 1 2 1 0 t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0≤Z:=by norm_num [Z]
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T (4/p)
  have Hf0:=hgrid0 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut []
  have Hf1:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut []
  simp only [siteMonomial] at Hf0 Hf1
  have hf i (hi : i.val≤1) : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · norm_num at hi
    · norm_num at hi
  have hg i (_hi : i.val≤1) : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W 0 hxW hcut (by norm_num) hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 1*W*Z*Cost:=by
    have HH:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT W hxW hcut [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    simp only [P,one_mul]
    convert HH using 1
    dsimp only [J,A,a1,Z,Cost,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_fixed_first_product_bound hW A B f g hB hJ hf hg
  apply HH.trans
  have HC : A 1+B 0*A 1+B 1*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    hW) hZ) hCost
  simpa only [nativeCenteredFixedLowHigh,f,g,J,Z,Cost,P,q,b,h,K,S,as,mul_one] using HB

theorem eventually_actual_minimum_inherited_constant_centered_transient_HIGH_budget_original_q
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀a z : T.Slot,
          |nativeCenteredTransientHighThird n q U b h K T (fun _=>1) a z l t|≤
            C*W^3*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cq1,hCq1,H1⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (D:=D) 1 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq2,hCq2,H2⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (D:=D) 2 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq3,hCq3,H3⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget_original_q
    (D:=D) 3 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets_original_q
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let a0:=pairForkVariation rBound
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*(Cq2*(1+Ccut))^2
  let a3:=pairForkVariation rBound*absJetVariation (rBound+2) 3*(Cq3*(1+Ccut))^3
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else if i.val=2 then a2 else a3
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=pairForkVariation_nonneg _
  have ha1 : 0≤a1:=by dsimp only [a1];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have ha2 : 0≤a2:=by dsimp only [a2];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have ha3 : 0≤a3:=by dsimp only [a3];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0+1
  have hC : 0<C:=by
    have H1:=hA 3
    have H2:=mul_nonneg (hB 0) (hA 3)
    have H3:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 1)) (hA 2)
    have H4:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 2)) (hA 1)
    have H5:=mul_nonneg (hB 3) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H1,H2,H3,HG] with n hn1 hn2 hn3 hng
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn1 M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn2 M hs0 hsxs hsource hxs L us hus hret hmesh,hn3 M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid1 hgrid2 hgrid3
  dsimp only at hgrid1 hgrid2 hgrid3 ⊢
  intro U T l t hU hl ht hT W hxW hcut a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P : T.Assignment→ℝ:=fun _=>1
  let Z : ℝ:=1
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1
  let f : Fin 4→ℝ:=fun i=>nativeTransientHighJet n q U b h K T P 0 i l t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0
  let J:=nativeTransientHighJet n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 3 l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0≤Z:=by norm_num [Z]
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T 1
  have Hfixed (Q : T.Assignment→ℝ) (k : ℕ) : nativeFixedLowHighProfile n q U b h K T Q k 1 t l t=
      nativeTransientHighJet n q U b h K T Q 0 k l t:=rfl
  have Hf0:=native_constant_fixed_zero_high_bound n U rBound q b h K T ho hT [] t l t
  have Hf1:=hgrid1 U T l t t hU hl ht ht hT W hxW hcut []
  have Hf2:=hgrid2 U T l t t hU hl ht ht hT W hxW hcut []
  have Hf3:=hgrid3 U T l t t hU hl ht ht hT W hxW hcut []
  rw [Hfixed] at Hf0 Hf1 Hf2 Hf3
  simp only [siteMonomial] at Hf0 Hf1 Hf2 Hf3
  have hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf3 using 1
      dsimp only [f,A,a3,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
  have hg i : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hs0 hsxs hsource us jGrid hus U T W l hxW hcut hl hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 3*W^3*Z*Cost:=by
    have HH:=hgrid3 U T l t t hU hl ht ht hT W hxW hcut [a,z]
    rw [Hfixed] at HH
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    simp only [P,one_mul]
    convert HH using 1
    dsimp only [J,A,a3,Z,Cost,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_third_HIGH_product_bound hW hZ hCost A B f g hA hB hJ hf hg
  apply HH.trans
  have HC : A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 3)) hZ) hCost
  simpa only [nativeCenteredTransientHighThird,f,g,J,Z,Cost,P,q,b,h,K,S,as,mul_one] using HB

end OAI.SKFluctuations.Cavity
