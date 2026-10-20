module

public import ComparisonSignedCavityCanonicalTransientLowPartBudget
public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_low_error_radius_above_cut_zero (n U : ℕ) (b h K : ℕ→ℝ)
    (as : List PositiveMass) (law : ℕ→FullCoordinate n→ℝ) (j : ℕ) (hj : U≤j) :
    nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j=0 := by
  simp only [nativeWholeLawErrorRadius,nativeWholeLawErrorSecond,cutLowError,not_lt.mpr hj,ite_false,
    ReplicaTree.coordinateProfile,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,Real.sqrt_zero]

theorem native_transient_low_part_radius_le (n U i star : ℕ) (b h K : ℕ→ℝ)
    (as : List PositiveMass) (law : ℕ→FullCoordinate n→ℝ) (part : NativeTransientLowErrorPart) (j : ℕ) :
    nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K part) j≤
      nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j := by
  rw [native_transient_low_part_radius]
  cases part <;> split_ifs <;> first | exact le_refl _ | exact nativeWholeLawErrorRadius_nonneg _ _ _ _ _

theorem native_persistent_moving_low_profile_le_density (n U i star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hT : NativePersistentLowForks i star U T) (law : ℕ→FullCoordinate n→ℝ) :
    let R:=nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K .moving)
    T.forkCost R+ClockTree.edgeBudget 0 as R≤
      ClockTree.edgeBudget 0 as (nativeWholeLawErrorRadius n as law (cutLowError n U b h K)) := by
  dsimp only
  have HR : nativeWholeLawErrorRadius n as law (nativeTransientLowErrorPartDirection n U i star b h K .moving)=
      fun j=>if j≠i ∧ j≠star then nativeWholeLawErrorRadius n as law (cutLowError n U b h K) j else 0 := by
    funext j
    exact native_transient_low_part_radius n U i star b h K as law .moving j
  rw [HR,native_persistent_moving_low_profile_forkCost_zero T hT _
    (fun j hj=>native_low_error_radius_above_cut_zero n U b h K as law j hj),zero_add]
  apply actual_low_edgeBudget_mono ho
  intro j hj
  split_ifs
  · exact le_refl _
  · exact nativeWholeLawErrorRadius_nonneg _ _ _ _ _

theorem eventually_actual_minimum_bare_canonical_moving_low_density_budget
    (aDegree k rBound : ℕ) (hk : 0<k)
    (Bclock Temp Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Cp Cq : ℝ,0<Cp ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
          NativePersistentLowForks i star U T →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),W=M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀es : List T.Slot,
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalMinimumSource M forms).product σ*siteMonomial T σ es) 0 .moving k l t|≤
            ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
              (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                sourceMonomialScale M.xs W initial)*(Cq*(1+Ccut)*W)^k*
              (actualLowErrorComparisonConstant Mclock Temp*
                (M.actualOriginalLowErrorDensitySaving (Ccut+1)*M.xs^2+1/(n+1:ℕ))) := by
  obtain ⟨Cp,Cq,hCp,hCq,HP⟩:=eventually_actual_minimum_bare_canonical_transient_low_part_budget
    (D:=D) aDegree k rBound hk Bclock Temp Cmass Ccut hTemp hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cq,hCp,hCq,?_⟩
  filter_upwards [HP] with n hnP
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh,
    actual_minimum_current_low_error_density_on_every_final_net M hcl hAz Temp (Ccut+1)
      hTemp (by linarith) hb hh hxs us hus] with jGrid hgrid hgridDensity
  dsimp only at hgrid hgridDensity ⊢
  intro i star U T l t hU hl ht hT hpersistent G forms initial W hW hcut hmass es
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let C:=ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
      sourceMonomialScale M.xs W initial)*(Cq*(1+Ccut)*W)^k
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hxW : M.xs≤W:=hW ▸ M.canonical_direct_test_band_ge_scale
  have hWpos : 0<W:=hW ▸ M.canonical_direct_test_band_pos
  have hC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
        (source_factor_scale_pos M.hxs hWpos initial e).le))) (by positivity)
  have Hsource:=hgrid U T l t hU hl ht hT G forms initial W hxW hcut hmass i star .moving es
  have Hmoving:=native_persistent_moving_low_profile_le_density n U i star b h K T ho hpersistent law
  have hmasscut : partitionPoint 0 as U ≤ min ((Ccut+1)*M.canonicalDirectTestBandScale) 1 := by
    apply le_min
    · rw [←hW]
      nlinarith only [hcut,hWpos]
    · exact (partitionPoint_mem as ho U).2
  have HD:=hgridDensity U hU hmasscut l t hl ht
  exact Hsource.trans (mul_le_mul_of_nonneg_left (Hmoving.trans HD) hC)

end OAI.SKFluctuations.Cavity
