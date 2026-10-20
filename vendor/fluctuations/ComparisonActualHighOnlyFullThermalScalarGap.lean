module

public import ComparisonActualHighOnlyFullTargetTaylorBudget
public import ComparisonActualHighOnlyTargetRefinement
public import ComparisonActualHighOnlyComparableContext
public import ComparisonSignedCavityActualRetainedTargetCutGeometry

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity ActualHighOnlyOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
theorem actual_high_only_comparable_context_original_scalar_gap_pointwise_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0)) :
    ∃C : ℝ,0 ≤ C ∧ ∃rate : ℕ→ℝ,(∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀u : ℝ,0 < u → u ≤ Atarget*(M n).xs →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-
            scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
            C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
              (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(dim n+1:ℕ))+
                rate n*(M n).xs^3 := by
  let c:=Atarget+1+2*cu*(Az+1)
  let Ccut:=2*c
  have hc : 0 < c := by dsimp only [c];positivity
  have hcouter : 2*cu*(Az+1) ≤ c := by dsimp only [c];linarith
  have hCcut : 0 < Ccut := by dsimp only [Ccut];positivity
  have htarget : Atarget < Ccut := by dsimp only [Ccut,c];nlinarith [mul_pos hcu (by linarith : 0 < Az+1)]
  let Cf:=G.Cf
  have hCf:=G.hCf
  have Hsource:=G.source
  obtain ⟨CM,hCM,HM⟩:=eventually_actual_inherited_target_mean_correction_rate_high_only
    (D:=D) Bclock T Cf Ccut G.hT.le hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CG,hCG,HG⟩:=eventually_actual_minimum_inherited_target_G_thermal_density_along_high_only
    dim hdim Bclock T Cf Ccut G.hT.le hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CT,hCT,HT⟩:=eventually_actual_high_only_target_original_Taylor_full_thermal_budget
    (D:=D) Bclock T Cf Ccut G.hT.le hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
  let I:=fun n=>(∫u in (0:ℝ)..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
    (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))
  let invN:=fun n=>(1/(dim n+1:ℕ):ℝ)
  let pmean:=fun n=>((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)
  let rate:=fun n=>CM*pmean n+2*T*CG*(I n/(M n).xs^2+3*(invN n/(M n).xs^2))+
    CT*(I n/(M n).xs^2+3*(invN n/(M n).xs^2))+invN n
  have Hsite:=actual_low_error_omitted_site_ratio_tendsto_zero_along_high_only hm hC0 dim hdim M
  have Hinv : Tendsto invN atTop (𝓝 0) := by
    simpa only [invN,Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hpmean : Tendsto pmean atTop (𝓝 0) := by
    simpa only [pmean,Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hrate : Tendsto rate atTop (𝓝 0) := by
    have H:=((Hpmean.const_mul CM).add ((Hfull.add (Hsite.const_mul 3)).const_mul (2*T*CG))).add
      ((Hfull.add (Hsite.const_mul 3)).const_mul CT) |>.add Hinv
    simpa only [rate,I,invN,mul_zero,add_zero] using H
  have hrate n : 0 ≤ rate n := by
    have hI : 0 ≤ I n:=intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)
    have hx:=(M n).hxs
    have hT:=G.hT
    dsimp only [rate,pmean,invN]
    positivity
  have Hcut:=((G.xs_zero.const_mul Ccut).eventually
    (eventually_le_nhds (show Ccut*(0:ℝ)<1 by simp)))
  have Hxs1:=G.xs_zero.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨CT,hCT.le,rate,hrate,Hrate,?_⟩
  filter_upwards [hdim.eventually HM,HG,hdim.eventually HT,Hsource,G.total_root,
    G.eventually_geometric_gates,Hcut,Hxs1] with n hnM hnG hnT hnS hnTotal hnGates hnCut hnXs
  refine ⟨hnTotal.1,?_⟩
  intro u hu huA
  let target : PositiveMass:=⟨u,hu⟩
  let inner:=nativeActualTargetMassCut c (M n).xs hc (M n).hxs
  have hinner : inner.val ≤ 1:=hnCut
  have hut : target.val < inner.val:=huA.trans_lt (mul_lt_mul_of_pos_right htarget (M n).hxs)
  have hu1 : target.val ≤ 1:=hut.le.trans hinner
  obtain ⟨Lnet,hLnet⟩:=exists_nat_one_div_lt (M n).hxs
  have hmesh : ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs:=by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hLnet.le
  let us:=target::inner::uniformMasses Lnet
  have hus : ∀v∈us,v.val ≤ 1 := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact hu1
    rcases List.mem_cons.mp hv with rfl|hv
    · exact hinner
    · exact (uniformMasses_ordered Lnet).members_le_one v hv
  have hret : ∀v∈uniformMasses Lnet,v∈us:=fun v hv=>List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
  have htargetRet : target∈us:=by simp only [us,List.mem_cons_self]
  have hinnerRet : inner∈us:=by simp only [us,List.mem_cons];exact Or.inr (Or.inl trivial)
  have Hscalar:=(M n).inherited_continuum_scalar_pair_errors_on_all_retained_masses
    G.hT hnTotal.1 hnTotal.2 us hus (invN n*(M n).xs^3) (by dsimp only [invN];have :=(M n).hxs;positivity)
  have Hfixed : ∀ᶠjGrid in atTop,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-
        scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT hnTotal.1)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
      CT*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid)
        (retainedMassPrefixIndex u (finiteCutMasses us jGrid))+1/(dim n+1:ℕ))+rate n*(M n).xs^3 := by
    filter_upwards [hnM (M n) hnGates.2 hnGates.1 hnS hnTotal.1 hnTotal.2 hnXs us hus,
      hnG (M n) hnGates.2 hnGates.1 hnS hnXs Lnet us hus hret hmesh,
      hnT (M n) hnGates.2 hnGates.1 hnS hnXs Lnet us hus hret hmesh,Hscalar]
      with jGrid hjM hjG hjT hjScalar
    dsimp only at hjM hjG hjT hjScalar ⊢
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex target.val as
    let U:=retainedMassPrefixIndex inner.val as
    have ho:=finiteCutMasses_ordered us hus jGrid
    have htargetNode:=finiteCutMasses_nodes us jGrid htargetRet
    have hinnerNode:=finiteCutMasses_nodes us jGrid hinnerRet
    have hi : i<U:=actual_retained_mass_strict_index as ho target inner htargetNode hinnerNode hut
    have hU : U≤as.length:=retainedMassPrefixIndex_le_length inner.val as
    have Hret : partitionPoint 0 as i=u:=nativeRetainedCut_partitionPoint as ho target htargetNode
    have HU : partitionPoint 0 as U=Ccut*(M n).xs:=nativeRetainedCut_partitionPoint as ho inner hinnerNode
    have hmass : partitionPoint 0 as i ≤ Ccut*(M n).xs := by rw [Hret];exact huA.trans (mul_le_mul_of_nonneg_right htarget.le (M n).hxs.le)
    have HMbound:=hjM i U hi hU (M n).xs le_rfl hmass
    have HGbound:=(hjG i U hi hU (M n).xs le_rfl hmass).1
    have HTbound:=hjT i U (M n).xs hi hU le_rfl (M n).canonical_direct_test_band_ge_scale hnXs
      hnCut HU.le
    have hDI:=native_intervalIntegrable_sqrt_of_intervalIntegrable (high_only_original_thermal_intervalIntegrable (M n))
    have htail : (∫v in partitionPoint 0 as U..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf v-
        (orderedPathS (dim n+1) (M n).bf (M n).hf v)^2)) ≤ I n :=
      intervalIntegral.integral_mono_interval (partitionPoint_mem as ho U).1
        (partitionPoint_mem as ho U).2 le_rfl (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) hDI
    have hlow : (∫v in 0..Ccut*(M n).xs,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf v-
        (orderedPathS (dim n+1) (M n).bf (M n).hf v)^2)) ≤ I n :=
      intervalIntegral.integral_mono_interval le_rfl (by have :=(M n).hxs;positivity) hnCut
        (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) hDI
    have HR : |nativeActualTargetLongitudinalResponse_high_only (M n) as i U| ≤
        CG*(M n).xs*(I n+3/(dim n+1:ℕ)) := HGbound.trans
      (mul_le_mul_of_nonneg_left (add_le_add htail le_rfl) (by have :=(M n).hxs;positivity))
    have HT' : |nativeActualTargetOriginalTaylorPart_high_only (M n) as i U| ≤
        CT*((M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
          (M n).xs*(I n+3/(dim n+1:ℕ))) := HTbound
    have Htrans : |nativeActualTargetMeanTransportError_high_only (M n) as i U U| ≤ (0:ℝ) := by
      simp only [nativeActualTargetMeanTransportError_high_only,sub_self,mul_zero,abs_zero,le_refl]
    have HB:=actual_target_mean_gap_abs_le_of_bounds_high_only (M n) as i U U hi hU ho
      (CM*pmean n*(M n).xs^3) (CG*(M n).xs*(I n+3/(dim n+1:ℕ))) 0
      (CT*((M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
        (M n).xs*(I n+3/(dim n+1:ℕ)))) HMbound HR Htrans HT'
    dsimp only at HB
    have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_high_only (M n) as ho U (by omega) hU
    have hb:=((hnS u ⟨hu.le,hu1⟩).1)
    have hcoef : 2*((M n).bf u:ℝ)*
        (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as)))).H 0 0 ≤ 2*T := by
      nlinarith only [mul_le_mul hb Hchi.2 Hchi.1 G.hT.le]
    have Hcenter : nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i=
        orderedPathS (dim n+1) (M n).bf (M n).hf u := by
      have H:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
        (M n).bf_monotone (M n).hf_monotone (partitionPoint_mem as ho i)
      rw [Hret] at H
      unfold nativePhysicalResourceCenter
      rw [Hret]
      exact H.symm
    rw [Hcenter,Hret] at HB
    have HA:=(abs_add_le
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-nativeOriginalScalarPairMean as
        (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) i)
      (nativeOriginalScalarPairMean as (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) i-
        scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT hnTotal.1)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u))).trans (add_le_add HB (hjScalar target htargetRet))
    simp only [sub_add_sub_cancel] at HA
    have hI : 0 ≤ I n:=intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)
    have hResp : 0 ≤ CG*(M n).xs*(I n+3/(dim n+1:ℕ)):=by have :=(M n).hxs;positivity
    have Hcoef:=mul_le_mul_of_nonneg_right hcoef hResp
    have HE : rate n*(M n).xs^3=
        CM*pmean n*(M n).xs^3+2*T*(CG*(M n).xs*(I n+3/(dim n+1:ℕ)))+
          CT*((M n).xs*(I n+3/(dim n+1:ℕ)))+invN n*(M n).xs^3 := by
      dsimp only [rate,invN]
      have hx:=(M n).hxs.ne'
      field_simp
    rw [HE]
    dsimp only [as,i,target] at HA Hcoef ⊢
    nlinarith only [HA,Hcoef]
  have Hrad:=actual_original_retained_target_low_radius_with_site_tendsto_high_only (M n) us hus target htargetRet
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((Hrad.const_mul (CT*(M n).xs^2)).add_const (rate n*(M n).xs^3)) Hfixed

end OAI.SKFluctuations.LaplaceWindowFormalization
