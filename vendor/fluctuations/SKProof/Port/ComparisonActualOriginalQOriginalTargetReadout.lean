module

public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong
public import ComparisonSignedCavityActualInheritedClockMeanSaving
public import ComparisonSignedCavityActualSusceptibilitySourceNumerics
public import ComparisonSignedCavityActualConstantSourceRemainderParts
public import ComparisonSignedCavityInheritedOriginalTargetPairRMS
public import ComparisonSignedCavityInheritedOriginalFreshTargetRMS
public import ComparisonSignedCavityOriginalGTargetDensity
public import ComparisonSignedCavityActualTargetGResponse
public import ComparisonSignedCavityActualTargetGOriginalReadout
public import ComparisonSignedCavityActualMinimumConstantMeanExchange
public import ComparisonSignedCavityActualTargetCutConditionalMean
public import ComparisonSignedCavityActualTargetMeanTransport
public import ComparisonSignedCavityActualTargetMeanCorrections
public import ComparisonSignedCavityActualTargetMeanReadout
public import ComparisonSignedCavityActualTargetMeanCorrectionRate
public import ComparisonSignedCavityActualTargetGResponseAlong
public import SKProof.Port.ComparisonActualOriginalQPhysicalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import ComparisonActualGeneralTargetMeanReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_original_high_l1_density_on_all_final_nets_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠjGrid in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) →
      let as:=finiteCutMasses us jGrid
      ∀U : ℕ,U≤as.length → ClockTree.edgeBudget 0 as
        (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)) ≤
        (∫u in partitionPoint 0 as U..1,Real.sqrt
          (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+3/(n+1:ℕ) :=
  original_high_l1_density_on_all_final_nets n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone

theorem eventually_actual_inherited_continuum_clock_mass_upper_original_q
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃CK : ℝ,0 < CK ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      ActualOriginalQSmallSourceClocks M Temp Cf →
      ∀u∈Icc (0:ℝ) 1,actualMixedClock (n+1) M.sweepBf M.sweepHf u ≤ CK*(M.xs+u) := by
  obtain ⟨B,hB,HB⟩:=ActualThetaZeroOverlapMinimum.eventually_actual_mass_mean_upper_original_q
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+Cf+Temp*B,by positivity,?_⟩
  filter_upwards [HB] with n hn
  intro M hs0 hsxs hsource u hu
  have Hmean : orderedPathS (n+1) M.sweepBf M.sweepHf u ≤ B*(M.xs+u):=by
    by_cases hp : 0 < u
    · exact hn M hs0 hsxs u ⟨hp,hu.2⟩
    · have hz : u=0:=le_antisymm (le_of_not_gt hp) hu.1
      rw [hz,orderedPathS,orderedPathPair_zero]
      simpa only [add_zero] using mul_nonneg hB.le M.hxs.le
  have HC:=hsource u hu
  have Hprod:=mul_le_mul HC.1 Hmean (M.mass_mean_nonneg hu) hTemp
  have Hpos : 0 ≤ M.xs+u:=add_nonneg M.hxs.le hu.1
  dsimp only [actualMixedClock]
  nlinarith only [HC.2,Hprod,Hpos]

theorem eventually_actual_inherited_original_clock_longitudinal_mean_saving_original_q
    (r : ℕ) (Bclock Temp : ℝ) (hTemp : 0 ≤ Temp)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) → M.h 0=0 →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      ∀ᶠk : ℕ in atTop,
        let as := finiteCutMasses us k
        let b := fun j => (M.sweepBf (partitionPoint 0 as j):ℝ)
        let h := fun j => (M.sweepHf (partitionPoint 0 as j):ℝ)
        ∀(K : ℕ→ℝ) (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a : T.Slot),T.leaves ≤ r →
          |nativeOriginalLongitudinalMean T U K
            b h (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) a| ≤
              ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
  let A := 8*(r:ℝ)*(r+1)*(r+2)*Temp
  have hA : 0 ≤ A := by dsimp [A];positivity
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=(2:ℝ)/3+2*m) (s:=(1:ℝ)/3)
      (by linarith) 0 (2*A*C0^2))
  filter_upwards [Hrate] with n hn
  intro M hs0 hsxs htotal hroot0 us hus
  have hbf : MonotoneOn M.sweepBf (Icc (0:ℝ) 1) := M.sweep_bf_monotone
  have hhf : MonotoneOn M.sweepHf (Icc (0:ℝ) 1) := M.sweep_hf_monotone
  have hroot := M.inherited_zero_root_field hroot0
  let Cphys := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) M.sweepBf M.sweepHf)
  have Hmesh := (uniformMasses_mesh_tendsto.mul_const Cphys).eventually
    (gt_mem_nhds (show (0:ℝ)*Cphys<1/(n+1:ℕ) by simpa only [zero_mul] using
      (show (0:ℝ)<1/(n+1:ℕ) by positivity)))
  filter_upwards [Hmesh] with k hk
  dsimp only
  let as := finiteCutMasses us k
  let b := fun j => (M.sweepBf (partitionPoint 0 as j):ℝ)
  let h := fun j => (M.sweepHf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have Hcenter (j : ℕ) (hj : j ≤ as.length) :
      |finitePhysicalMean (n+1) as b h j-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as j| ≤
        1/(n+1:ℕ) := by
    exact (finite_physical_mean_uniform_continuum_error n M.sweepBf M.sweepHf hbf hhf hroot as ho
      (finiteCutMasses_end us hus k) (by positivity) (finiteCutMasses_mesh us hus k) j hj).trans hk.le
  have Hbond (j : ℕ) (_hj : j ≤ as.length) : |b j| ≤ Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have Htotal:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho j)
    linarith [(M.sweepHf (partitionPoint 0 as j)).coe_nonneg]
  have Hnum := M.actual_terminal_power_over_scale hC0 (show 0 ≤ 2*A by positivity)
    (gamma:=1) 1
  simp only [Nat.cast_one,mul_one] at Hnum
  rw [show (1:ℝ)-(1:ℝ)/3+2*m=(2:ℝ)/3+2*m by ring] at Hnum
  have Hsave : 2*A/((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos M.hxs)).mp
    have Hnorm : (2*A/((n+1:ℕ):ℝ))/M.xs^2 ≤
        (2*A*C0^2)*((n+1:ℕ):ℝ)^(-((2:ℝ)/3+2*m)) := by
      simpa only [ActualHighWallData.N,Real.rpow_neg_one,div_eq_mul_inv,mul_assoc] using Hnum
    exact Hnorm.trans (by simpa only [pow_zero,mul_one,neg_div] using hn)
  intro K T U a hleaves
  have HM := native_original_longitudinal_mean_abs_le T ho U K
    b h (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) a hTemp (by positivity) Hbond Hcenter
  have Hpoly : 8*(T.leaves:ℝ)*(T.leaves+1)*(T.leaves+2)*Temp ≤ A := by
    dsimp only [A]
    have Hle : (T.leaves:ℝ) ≤ r := by exact_mod_cast hleaves
    gcongr
  apply HM.trans
  apply le_trans _ Hsave
  have HH := mul_le_mul_of_nonneg_right Hpoly
    (show (0:ℝ) ≤ 1/(n+1:ℕ)+1/(n+1:ℕ) by positivity)
  convert HH using 1
  ring

theorem actual_minimum_continuum_susceptibility_mem_unit_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (hU0 : 0 < U) (hU : U ≤ as.length) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0∈Icc (0:ℝ) 1 := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  have hKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterm : K as.length ≤ Temp:=
    (native_continuum_mixed_clock_terminal_le n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,hU0])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  exact ⟨((Real.exp_pos (-4*Temp)).le.trans HH.1),HH.2⟩

def nativeActualConstantSourceMeanPart_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let S:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)

theorem actual_constant_source_mean_part_abs_le_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length)
    (hmesh : let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      |finitePhysicalMean (n+1) as b h star-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as star| ≤
        1/(n+1:ℕ)) :
    |nativeActualConstantSourceMeanPart_original_q M as star U| ≤ 2*Temp/(n+1:ℕ) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let mean:=finitePhysicalMean (n+1) as b h star
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit_original_q M htotal as ho U (by omega) hU
  have Hmean0 : 0 ≤ mean:=finitePhysicalMean_nonneg (n+1) as b h star
  have Hmean1 : mean ≤ 1:=finitePhysicalMean_le_one (n+1) ho b h star
  have Hb : b star ≤ Temp:=by
    have H:=M.inherited_total_clock_le htotal _ (partitionPoint_mem as ho star)
    dsimp only [b]
    linarith [(M.sweepHf (partitionPoint 0 as star)).coe_nonneg]
  have Hb0 : 0 ≤ b star:=NNReal.coe_nonneg _
  have Hchi2 : chi^2 ≤ 1:=by change chi∈Icc (0:ℝ) 1 at Hchi;nlinarith [Hchi.1,Hchi.2]
  have Hcoef : chi^2*b star ≤ Temp:=by nlinarith
  have HE : |mean-mean/(n+1:ℕ)-S star| ≤ 2/(n+1:ℕ):=by
    have HH:=abs_add_le (mean-S star) (-(mean/(n+1:ℕ)))
    simp only [abs_neg,←sub_eq_add_neg] at HH
    rw [abs_of_nonneg (div_nonneg Hmean0 (by positivity))] at HH
    have Hdiv:=div_le_div_of_nonneg_right Hmean1 (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    change |mean-S star| ≤ 1/(n+1:ℕ) at hmesh
    have Heq : mean-mean/(n+1:ℕ)-S star=mean-S star-mean/(n+1:ℕ):=by ring
    rw [Heq,show (2:ℝ)/(n+1:ℕ)=1/(n+1:ℕ)+1/(n+1:ℕ) by ring]
    exact HH.trans (add_le_add hmesh Hdiv)
  change |chi^2*b star*(mean-mean/(n+1:ℕ)-S star)| ≤ _
  rw [abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg _) Hb0)]
  have H:=mul_le_mul Hcoef HE (abs_nonneg _) (Hb0.trans Hb)
  convert H using 1
  ring

theorem eventually_actual_minimum_inherited_original_target_pair_rms_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
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
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        ∀(T : ClockTree (Spin n×Bool) as) (s z : T.Slot),s≠z→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as (T.splitIndex s z) ≤ Ccut*x→
          Real.sqrt (T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>(deletedOverlap n (joinSpin (T.atSlot σ s))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex s z))^2) 0) ≤ C*x := by
  obtain ⟨Cd,hCd,H⟩:=eventually_actual_minimum_inherited_continuum_centered_pair_moment_original_q
    (D:=D) 1 (by norm_num) Bclock Temp Cf hTemp hCf
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cd*(1+Ccut),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hk
  dsimp only at hk ⊢
  intro U l t hl ht T s z hsz x hxs hmass
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hu:=partitionPoint_mem (finiteCutMasses us jGrid) ho (T.splitIndex s z)
  have Hpair:=hk U l t hl ht (T.splitIndex s z) (T.splitIndex_le_clockLength s z)
  rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 _ 0
    s z hsz (fun u v=>(deletedOverlap n (joinSpin u) (joinSpin v)-
      orderedPathS (n+1) M.sweepBf M.sweepHf
        (partitionPoint 0 (finiteCutMasses us jGrid) (T.splitIndex s z)))^2)]
  apply (Real.sqrt_le_iff).2
  constructor
  · have hx:=M.hxs.trans_le hxs
    positivity
  · apply (show _ ≤ (Cd*(M.xs+partitionPoint 0 (finiteCutMasses us jGrid)
        (T.splitIndex s z)))^2 by simpa only [Nat.mul_one,sq_abs] using Hpair).trans
    apply pow_le_pow_left₀ (mul_nonneg hCd.le (add_nonneg M.hxs.le Hu.1))
    have Hscale : M.xs+partitionPoint 0 (finiteCutMasses us jGrid) (T.splitIndex s z) ≤
        (1+Ccut)*x := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hscale hCd.le

theorem eventually_actual_minimum_inherited_original_fresh_target_rms_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
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
        ∀(U : ℕ) (l t : ℝ),l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        ∀(T : ClockTree (Spin n×Bool) as) (s : T.Slot) (i : ℕ),i ≤ as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let g:=nativeFreshAtSlot T 0 s i
          Real.sqrt (g.tree.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
              (joinSpin (g.spin σ))-S i)^2) 0) ≤ C*x := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_original_target_pair_rms_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hk
  dsimp only at hk ⊢
  intro U l t hl ht T s i hi x hxs hmass
  let g:=nativeFreshAtSlot T 0 s i
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=i := by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hi]
  have Hpair:=hk U l t hl ht g.tree (g.embed s) g.mark
    (nativeFreshAtSlot_distinct T 0 s i s).symm x hxs (by simpa only [Hsplit] using hmass)
  change Real.sqrt (g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 _
    (fun σ=>(deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
      (joinSpin (g.spin σ))-orderedPathS (n+1) M.sweepBf M.sweepHf
        (partitionPoint 0 (finiteCutMasses us jGrid) i))^2) 0) ≤ C*x
  simp_rw [g.restrict_at,g.spin_at]
  simpa only [Hsplit] using Hpair

theorem actual_minimum_inherited_original_target_G_density_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i < U) (hU : U ≤ as.length) (A : ℝ) (hA : 0 ≤ A)
    (P : (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree.Assignment→ℝ)
    (hP :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
      let K:=fun j=>h j+b j*S j
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).tree.disorderExpect
        (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K) (fun σ=>(P σ)^2) 0 ≤ A^2) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
    abs (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
      g.tree P (g.embed (singleSlot as))) ≤
      A*forkVariation 2 3*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        edgeBudget 0 as (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)) := by
  dsimp only at hP ⊢
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n q U 1 1 b h K
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let f:=fun j=>if j<U then 0 else nativeWholeLawErrorRadius n as qfull (cutTSlope n U 0 b h K) j
  let Ccmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let R:=fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as j+1/(n+1:ℕ)
  have hleaves : g.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ _ _ _)
    simpa only [single_leaves_exact] using H
  have H:=native_original_longitudinal_abs_le_high_profile g.tree ho U hU b h K S
    (fun _=>rfl) qfull P (g.embed (singleSlot as)) A hA hP 2 hleaves
  dsimp only at H
  have Hfork : g.tree.forkCost f=0:=native_initial_seed_high_forkCost as 0 hi f
    (by intro j hj;exact ite_eq_left hj)
  change _ ≤ A*forkVariation 2 3*(g.tree.forkCost f+edgeBudget 0 as f) at H
  rw [Hfork,zero_add] at H
  have HR : edgeBudget 0 as f ≤ Ccmp*edgeBudget 0 as R:=by
    have Hpoint (j : ℕ) (hj : j ≤ as.length) : f j ≤ Ccmp*R j:=by
      have HE:=actual_minimum_inherited_current_high_error_radius_le_original_original_q M Temp Cf hTemp hCf
        hsource hxs ho U (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
        (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) j hj
      dsimp only [f,R,Ccmp]
      by_cases hjU : j<U
      · simp only [hjU,ite_true,mul_zero,le_refl]
      · simpa only [nativeOriginalHighErrorEnvelope,hjU,ite_false] using HE
    have HH:=actual_low_edgeBudget_mono ho Hpoint
    have HE : edgeBudget 0 as (fun j=>Ccmp*R j)=Ccmp*edgeBudget 0 as R:=by
      simpa only [zero_mul,add_zero] using actual_low_edgeBudget_linear as 0 Ccmp 0 R (fun _=>0)
    rw [HE] at HH
    exact HH
  exact H.trans ((mul_le_mul_of_nonneg_left HR (mul_nonneg hA (forkVariation_nonneg 2 3))).trans_eq (by ring))

def nativeActualTargetLongitudinalResponse_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 (singleSlot as) i
  nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S g.tree
    (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
      (joinSpin (g.spin σ))-S i) (g.embed (singleSlot as))

def nativeActualTargetConditionalResponse_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeOriginalConditionalLongitudinalPair (single (S:=Spin n×Bool) as) (singleSlot as)
    i U K b S 0 (cutFullVariance n q U 1 1 b h K) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S i)

theorem native_actual_target_longitudinal_eq_conditional_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    nativeActualTargetLongitudinalResponse_original_q M as i U=
      nativeActualTargetConditionalResponse_original_q M as i U := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  exact native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU K b S
    0 (cutFullVariance n q U 1 1 b h K) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S i)

theorem eventually_actual_minimum_inherited_target_G_thermal_density_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U→U≤as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let tail:=(∫u in partitionPoint 0 as U..1,
            Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+
              3/(n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse_original_q M as i U) ≤ C*x*tail ∧
          abs (nativeActualTargetConditionalResponse_original_q M as i U) ≤ C*x*tail := by
  obtain ⟨Cr,hCr,Hr⟩:=eventually_actual_minimum_inherited_original_fresh_target_rms_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let V:=forkVariation 2 3
  let Cmp:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hV : 0≤V:=forkVariation_nonneg 2 3
  have hCmp : 0≤Cmp:=actualLowErrorComparisonConstant_nonneg _ hTemp
  refine ⟨Cr*V*Cmp+1,by positivity,?_⟩
  filter_upwards [Hr] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh,
    actual_original_high_l1_density_on_all_final_nets_original_q M] with jGrid hj htail
  dsimp only at hj ⊢
  intro i U hi hU x hscale hmass
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hx : 0≤x:=M.hxs.le.trans hscale
  have HR:=hj U 1 1 (by norm_num) (by norm_num)
    (single (S:=Spin n×Bool) (finiteCutMasses us jGrid))
    (singleSlot (finiteCutMasses us jGrid)) i (Nat.le_trans hi.le hU) x hscale hmass
  have HP:=(Real.sqrt_le_iff.mp HR).2
  let T:=single (S:=Spin n×Bool) (finiteCutMasses us jGrid)
  let g:=nativeFreshAtSlot T 0 (singleSlot (finiteCutMasses us jGrid)) i
  let P:=fun σ=>deletedOverlap n
    (joinSpin (T.atSlot (g.restrict σ) (singleSlot (finiteCutMasses us jGrid))))
    (joinSpin (g.spin σ))-orderedPathS (n+1) M.sweepBf M.sweepHf
      (partitionPoint 0 (finiteCutMasses us jGrid) i)
  have HL:=actual_minimum_inherited_original_target_G_density_original_q M Temp Cf hTemp hCf
    hsource hxs (finiteCutMasses us jGrid) ho i U hi hU (Cr*x) (mul_nonneg hCr.le hx) P HP
  have HE:=htail us hus U hU
  let edge:=edgeBudget 0 (finiteCutMasses us jGrid)
    (fun j=>if j<U then 0 else nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf
      (finiteCutMasses us jGrid) j+1/(n+1:ℕ))
  have he : 0≤edge:=edgeBudget_nonneg ho (by
    intro j
    split_ifs
    · exact le_rfl
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HT : (0:ℝ)≤_:=he.trans HE
  change abs (nativeActualTargetLongitudinalResponse_original_q M (finiteCutMasses us jGrid) i U)≤
    (Cr*x)*V*Cmp*edge at HL
  have Hbound:=HL.trans (mul_le_mul_of_nonneg_left HE
    (mul_nonneg (mul_nonneg (mul_nonneg hCr.le hx) hV) hCmp))
  have Hfinal : abs (nativeActualTargetLongitudinalResponse_original_q M (finiteCutMasses us jGrid) i U)≤
      (Cr*V*Cmp+1)*x*((∫u in partitionPoint 0 (finiteCutMasses us jGrid) U..1,
        Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+3/(n+1:ℕ)) := by
    have Hcoef : (Cr*x)*V*Cmp=(Cr*V*Cmp)*x:=by ring
    rw [Hcoef] at Hbound
    exact Hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hx) HT)
  refine ⟨Hfinal,?_⟩
  rwa [←native_actual_target_longitudinal_eq_conditional_original_q M _ ho i U hi hU]

theorem native_actual_target_response_original_readout_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let T:=single (S:=Spin n×Bool) as
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    nativeActualTargetLongitudinalResponse_original_q M as i U=
      nativeOriginalLongitudinalPairing n 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 U K b C g.tree
        (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
          (joinSpin (g.spin σ))-C i) (g.embed s) := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  have HS : S=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf M.inherited_bf_monotone
      M.inherited_hf_monotone (partitionPoint_mem as ho j)
  have HQ : cutFullVariance n q U 1 1 b h K=
      finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  change nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
    g.tree (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
      (joinSpin (g.spin σ))-S i) (g.embed s)=_
  rw [HQ,HS]

theorem native_actual_target_conditional_original_readout_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    nativeActualTargetConditionalResponse_original_q M as i U=
      nativeOriginalConditionalLongitudinalPair (single (S:=Spin n×Bool) as) (singleSlot as)
        i U K b C 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i) := by
  dsimp only
  rw [←native_actual_target_longitudinal_eq_conditional_original_q M as ho i U hi hU,
    native_actual_target_response_original_readout_original_q M as ho i U]
  exact native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU
    (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)
    (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i)

theorem actual_minimum_constant_gap_eq_twice_old_longitudinal_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  exact actual_general_constant_gap_eq_twice_old_longitudinal M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone as i U hi hU ho

theorem actual_minimum_constant_gap_eq_twice_conditional_insertion_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalConditionalLongitudinalPair T s i U K b C 0 qfull 0 A+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_constant_gap_eq_twice_old_longitudinal_original_q M as i U hi hU ho
  dsimp only at H
  have HL:=native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU
    (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)
    (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
    0 (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun u v : Spin n×Bool=>deletedOverlap n (joinSpin u) (joinSpin v)-
      nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i)
  dsimp only at HL
  rw [HL] at H
  exact H

theorem actual_minimum_continuum_gap_eq_conditional_insertion_and_corrections_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) (hi : i < U) (hU : U ≤ as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    C i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      -(chi^2*b i*finitePhysicalMean (n+1) as b h i/(n+1:ℕ))+
      (chi^2*b i-1)*(finitePhysicalMean (n+1) as b h i-C i)+
      2*b i*chi*nativeOriginalConditionalLongitudinalPair T s i U K b C 0 qfull 0 A+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_constant_gap_eq_twice_conditional_insertion_original_q M as i U hi hU ho
  dsimp only at H
  linear_combination H

def nativeActualTargetMeanTransportError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  2*(M.sweepBf (partitionPoint 0 as i):ℝ)*chi*
    (nativeActualTargetLongitudinalResponse_original_q M as i U-nativeActualTargetLongitudinalResponse_original_q M as i V)

theorem actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ)
    (hU0 : 0<U) (hU : U≤as.length) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0∈Icc (0:ℝ) 1 := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  have hKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp only [relocatedClock,hU0,ite_true,zero_mul])
    (B:=K as.length) (by simp only [relocatedClock,not_lt.mpr hU,ite_false,le_refl])
  exact ⟨((Real.exp_pos (-4*K as.length)).le.trans HH.1),HH.2⟩

theorem actual_inherited_target_mean_transport_error_bound_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0≤Temp) (hsource : ActualOriginalQSmallSourceClocks M Temp Cf)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U V : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    abs (nativeActualTargetMeanTransportError_original_q M as i U V)≤2*Temp*
      abs (nativeActualTargetLongitudinalResponse_original_q M as i U-nativeActualTargetLongitudinalResponse_original_q M as i V) := by
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q M as ho U
    (Nat.zero_le i |>.trans_lt hi) hU
  have Hb:=(hsource _ (partitionPoint_mem as ho i)).1
  have HB:=mul_le_mul Hb Hchi.2 Hchi.1 hTemp
  simp only [mul_one] at HB
  unfold nativeActualTargetMeanTransportError_original_q
  dsimp only
  rw [abs_mul,abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  simpa only [←mul_assoc] using mul_le_mul_of_nonneg_left HB (by norm_num : (0:ℝ)≤2)

theorem actual_minimum_continuum_gap_eq_calibration_response_and_corrections_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
    let T:=single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    C i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      -(chi^2*b i*finitePhysicalMean (n+1) as b h i/(n+1:ℕ))+
      (chi^2*b i-1)*(finitePhysicalMean (n+1) as b h i-C i)+
      2*b i*chi*nativeActualTargetLongitudinalResponse_original_q M as i V+
      nativeActualTargetMeanTransportError_original_q M as i U V+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  have H:=actual_minimum_continuum_gap_eq_conditional_insertion_and_corrections_original_q M as i U hi hU ho
  dsimp only at H
  rw [←native_actual_target_conditional_original_readout_original_q M as ho i U hi hU,
    ←native_actual_target_longitudinal_eq_conditional_original_q M as ho i U hi hU] at H
  unfold nativeActualTargetMeanTransportError_original_q
  dsimp only
  linear_combination H

def nativeActualTargetOriginalConstantPart_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K i*(nativeOriginalLongitudinalPairing n 0 q 0 U K b C g.tree (fun _=>1) (g.embed (singleSlot as))+
    nativeOriginalLongitudinalPairing n 0 q 0 U K b C g.tree (fun _=>1) g.mark)

def nativeActualTargetOriginalMeanCorrection_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  nativeActualTargetOriginalConstantPart_original_q M as i U+nativeActualConstantSourceMeanPart_original_q M as i U-
    (finitePhysicalMean (n+1) as b h i-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i)

theorem actual_target_original_constant_part_abs_le_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i<U) (hU : U≤as.length)
    {R E : ℝ} (hK : nativeContinuumMixedClock n M.sweepBf M.sweepHf as i≤R)
    (hL : let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
      ∀a:g.tree.Slot,|nativeOriginalLongitudinalMean g.tree U K b h C a|≤E) :
    |nativeActualTargetOriginalConstantPart_original_q M as i U|≤2*R*E := by
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q M as ho U (by omega) hU
  have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho i
  have hR : 0≤R:=HK.trans hK
  unfold nativeActualTargetOriginalConstantPart_original_q
  dsimp only at hL ⊢
  simp only [native_original_clock_constant_pairing_eq_mean]
  rw [abs_mul,abs_mul,abs_of_nonneg Hchi.1,abs_of_nonneg HK]
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  have HL:=(abs_add_le _ _).trans (add_le_add (hL (g.embed (singleSlot as))) (hL g.mark))
  have HC:=mul_le_mul Hchi.2 hK HK (by norm_num : (0:ℝ)≤1)
  simp only [one_mul] at HC
  have H:=mul_le_mul HC HL (abs_nonneg _) hR
  nlinarith only [H]

theorem actual_target_original_mean_correction_abs_le_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp R E : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i<U) (hU : U≤as.length)
    (hL : |nativeActualTargetOriginalConstantPart_original_q M as i U|≤2*R*E)
    (hmesh : let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      |finitePhysicalMean (n+1) as b h i-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i|≤1/(n+1:ℕ)) :
    |nativeActualTargetOriginalMeanCorrection_original_q M as i U|≤2*R*E+(2*Temp+1)/(n+1:ℕ) := by
  have HM:=actual_constant_source_mean_part_abs_le_original_q M htotal as ho i U hi hU hmesh
  unfold nativeActualTargetOriginalMeanCorrection_original_q
  dsimp only at hmesh ⊢
  have H:=(abs_add_le
    (nativeActualTargetOriginalConstantPart_original_q M as i U+nativeActualConstantSourceMeanPart_original_q M as i U)
    (-(finitePhysicalMean (n+1) as (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
      (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) i-nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i))).trans
        (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_neg,←sub_eq_add_neg] at H
  have HH:=(add_le_add (add_le_add hL HM) hmesh)
  apply H.trans
  convert HH using 1
  ring

def nativeActualTargetOriginalTaylorPart_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark

theorem actual_target_mean_eq_correction_response_transport_taylor_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i-nativeOriginalScalarPairMean as K i=
      nativeActualTargetOriginalMeanCorrection_original_q M as i U+
      2*(M.sweepBf (partitionPoint 0 as i):ℝ)*chi*nativeActualTargetLongitudinalResponse_original_q M as i V+
      nativeActualTargetMeanTransportError_original_q M as i U V+
      nativeActualTargetOriginalTaylorPart_original_q M as i U := by
  dsimp only
  have H:=actual_minimum_continuum_gap_eq_calibration_response_and_corrections_original_q M as i U V hi hU ho
  dsimp only at H
  unfold nativeActualTargetOriginalMeanCorrection_original_q nativeActualTargetOriginalConstantPart_original_q
    nativeActualConstantSourceMeanPart_original_q nativeActualTargetOriginalTaylorPart_original_q
  dsimp only
  linear_combination H

theorem actual_target_mean_gap_abs_le_four_parts_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i-nativeOriginalScalarPairMean as K i|≤
      |nativeActualTargetOriginalMeanCorrection_original_q M as i U|+
      2*(M.sweepBf (partitionPoint 0 as i):ℝ)*chi*|nativeActualTargetLongitudinalResponse_original_q M as i V|+
      |nativeActualTargetMeanTransportError_original_q M as i U V|+
      |nativeActualTargetOriginalTaylorPart_original_q M as i U| := by
  dsimp only
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q M as ho U (by omega) hU
  rw [actual_target_mean_eq_correction_response_transport_taylor_original_q M as i U V hi hU ho]
  have Hcoef : 0≤2*(M.sweepBf (partitionPoint 0 as i):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.sweepBf M.sweepHf as)))).H 0 0:=
    mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1
  have Habs (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d|:=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  apply (Habs _ _ _ _).trans_eq
  rw [abs_mul,abs_of_nonneg Hcoef]

theorem actual_target_mean_gap_abs_le_of_bounds_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U V : ℕ) (hi : i<U) (hU : U≤as.length)
    (ho : MassOrdered 0 as) (Emean R Etransport Etaylor : ℝ)
    (Hmean : |nativeActualTargetOriginalMeanCorrection_original_q M as i U|≤Emean)
    (Hresponse : |nativeActualTargetLongitudinalResponse_original_q M as i V|≤R)
    (Htransport : |nativeActualTargetMeanTransportError_original_q M as i U V|≤Etransport)
    (Htaylor : |nativeActualTargetOriginalTaylorPart_original_q M as i U|≤Etaylor) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativePhysicalResourceCenter n M.sweepBf M.sweepHf as i-nativeOriginalScalarPairMean as K i|≤
      Emean+2*(M.sweepBf (partitionPoint 0 as i):ℝ)*chi*R+Etransport+Etaylor := by
  dsimp only
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_original_q M as ho U (by omega) hU
  apply (actual_target_mean_gap_abs_le_four_parts_original_q M as i U V hi hU ho).trans
  exact add_le_add (add_le_add (add_le_add Hmean
    (mul_le_mul_of_nonneg_left Hresponse
      (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1))) Htransport) Htaylor

theorem eventually_actual_inherited_target_mean_correction_rate_original_q
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp) → M.h 0=0 → M.xs≤1 →
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) →∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U : ℕ,i<U → U≤as.length →∀x : ℝ,M.xs≤x →
          partitionPoint 0 as i≤Ccut*x →
          |nativeActualTargetOriginalMeanCorrection_original_q M as i U|≤
            C*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3 := by
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper_original_q
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HL:=eventually_actual_inherited_original_clock_longitudinal_mean_saving_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    2 Bclock Temp hTemp hm hC0
  have HO:=eventually_actual_omitted_product_cubic_cost_saved_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 (2*Temp+1) (by positivity)
  let C:=2*CK*(1+Ccut)+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HK,HL,HO] with n hnK hnL hnO
  intro M hs0 hsxs hs ht hroot hxs1 us hus
  have HM:=eventually_native_finite_physical_mean_uniform_center n M.sweepBf M.sweepHf
    M.inherited_bf_monotone M.inherited_hf_monotone (M.inherited_zero_root_field hroot)
    us hus (1/(n+1:ℕ)) (by positivity)
  filter_upwards [hnL M hs0 hsxs ht hroot us hus,HM] with jGrid hL hmesh
  dsimp only at hL hmesh ⊢
  intro i U hi hU x hxs hmass
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  have hx:=M.hxs.trans_le hxs
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hK : K i≤CK*(1+Ccut)*x := by
    have H:=hnK M hs0 hsxs hs (partitionPoint 0 as i) (partitionPoint_mem as ho i)
    change K i≤CK*(M.xs+partitionPoint 0 as i) at H
    nlinarith only [H,hCK,hxs,hmass]
  have hleaves : g.tree.leaves≤2 := by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ 0 (singleSlot as) i)
    simpa only [single_leaves_exact] using H
  have Hpart:=actual_target_original_constant_part_abs_le_original_q M as ho i U hi hU
    (E:=((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2) hK
    (fun a=>hL K g.tree U a hleaves)
  have Hcorr:=actual_target_original_mean_correction_abs_le_original_q M ht as ho i U hi hU Hpart
    (hmesh i (hi.le.trans hU))
  have hN : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have Hexp : ((n+1:ℕ):ℝ)^(-(1:ℝ)/3)≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have Hsq : M.xs^2≤x^2:=pow_le_pow_left₀ M.hxs.le hxs 2
  have Hscale : x*M.xs^2≤x^3 := by nlinarith only [mul_le_mul_of_nonneg_left Hsq hx.le]
  have HA : (2*Temp+1)/(n+1:ℕ)≤((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3 := by
    have Hden : (n+1:ℕ)*M.xs≤(n+1:ℕ)*(1:ℝ):=mul_le_mul_of_nonneg_left hxs1 (by positivity)
    have Hdiv:=div_le_div_of_nonneg_left (show (0:ℝ)≤2*Temp+1 by positivity)
      (show (0:ℝ)<(n+1:ℕ)*M.xs by have :=M.hxs;positivity) Hden
    simp only [mul_one] at Hdiv
    exact Hdiv.trans ((hnO M x hxs).trans
      (mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg (by positivity) _)))
  have HB : 2*(CK*(1+Ccut)*x)*(((n+1:ℕ):ℝ)^(-(1:ℝ)/3)*M.xs^2)≤
      (2*CK*(1+Ccut))*(((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*x^3) := by
    have HP:=mul_le_mul Hexp Hscale (by positivity : (0:ℝ)≤x*M.xs^2)
      (Real.rpow_nonneg (by positivity) (-(1:ℝ)/6))
    have Hmul:=mul_le_mul_of_nonneg_left HP (show (0:ℝ)≤2*CK*(1+Ccut) by positivity)
    convert Hmul using 1
    ring
  apply Hcorr.trans
  dsimp only [C]
  have H:=add_le_add HB HA
  convert H using 1
  ring

theorem eventually_actual_minimum_inherited_target_G_thermal_density_along_original_q
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U→U≤as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let tail:=(∫u in partitionPoint 0 as U..1,
            Real.sqrt (orderedPathB (dim n+1) M.sweepBf M.sweepHf u-(orderedPathS (dim n+1) M.sweepBf M.sweepHf u)^2))+
              3/(dim n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse_original_q M as i U) ≤ C*x*tail ∧
          abs (nativeActualTargetConditionalResponse_original_q M as i U) ≤ C*x*tail := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_target_G_thermal_density_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
