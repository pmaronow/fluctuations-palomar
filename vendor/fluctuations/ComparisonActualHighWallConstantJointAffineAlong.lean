module

public import ComparisonActualHighWallConstantForestPriceEnvelopeAlong
public import ComparisonActualHighWallConstantFrozenCorrectionCubicAlong
public import ComparisonActualHighWallFreshPairPowerAlong
public import ComparisonActualHighWallTerminalSamePairGrid
public import ComparisonActualHighWallTerminalReadout
public import ComparisonActualGeneralConstantJointAffineNumerics
public import ComparisonActualGeneralConstantCorrectionCongruence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_constant_joint_source_affine_on_strong_master_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK T0 : ℝ}
    (dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    (hCx : 0 < Cx) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) (hL : 0 < L)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK) (_hT0 : 0 < T0)
    (hKroom : cK ≤ 3*T0*(starMassBandConstant cu Az/cu)/8)
    (hbandRoom : calibratedBandStart cu Az+4*L ≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0 ≤ (M n).data.T)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃depth : ℕ,0 < depth ∧ ∃saving : ℝ,0 < saving ∧ ∃Apair : ℝ,1 ≤ Apair ∧ ∃A B : ℝ,0 < A ∧ 0 < B ∧
      ∀ᶠn in atTop,∀source outer : PositiveMass,
        ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer →
      ∀Lnet : ℕ,((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
        (∀u∈uniformMasses Lnet,u∈us) ∧ (w n).star∈us ∧ source∈us ∧ outer∈us ∧
        (∀j ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us) ∧
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex source.val as
        ∃_hs : star < U,∃_hU : U ≤ as.length,
        ActualHighWallFreshPairPowerBudgetsOnGrid depth Apair (actualSlowWindowExponent m delta/128) Cmass cK (M n) (w n).star as ∧
        ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass (M n) (w n).star as ∧
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |actualGeneralConstantJointSource (n:=dim n) (M n).bf (M n).hf as star U| ≤
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| *A*
            ((dim n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/256))*(M n).data.d+
          B*(M n).data.d^3 := by
  let gamma:=actualSlowWindowExponent m delta/128
  have hgamma : 0 < gamma:=by dsimp only [gamma];positivity [actualSlowWindowExponent_pos hm hdelta hroom]
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨depth,hdepth,saving,hsaving,HTerminal⟩:=
    exists_actual_high_wall_cubic_terminal_on_same_square_pair_grid_along
      (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
      (Cmass:=Cmass) hm hC0 hgamma hcK dim hdim
  obtain ⟨Cstage,hCstage,HStages⟩:=eventually_actual_high_wall_constant_forest_all_levels_cubic_prices_along
    (D:=D) depth dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut
    hCx heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
    hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
  obtain ⟨Ccorrection,hCcorrection,HCorrection⟩:=eventually_actual_high_wall_constant_source_frozen_correction_cubic_along
    (D:=D) dOrder hd p hp hOrder Bclock Cmass Ccut Rmacro F Cx hCm0 hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    c hc hcout htheta1 htheta2 hdeficit dim hdim M hfixed hdlim hsRatio
  obtain ⟨Apair,hApair,HMaster⟩:=actual_high_wall_fresh_pair_power_master_at_calibrated_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hL Cmass hCm0 hcK dim hdim M hfixed hdlim Cs hCs w hw depth
  let den:=Real.exp (-4*Bclock)*cK
  let A:=Bclock*(depth:ℝ)/den
  let B:=Bclock*(depth:ℝ)*(Cstage/den+Cstage+Cstage)+12*Bclock+Ccorrection
  have hBclock : 0 < Bclock:=(M 0).data.hTpos.trans_le (M 0).hT
  have hden : 0 < den:=by dsimp only [den];positivity
  have hA : 0 < A:=by
    have HD : 0 < (depth:ℝ):=by exact_mod_cast hdepth
    dsimp only [A]
    positivity
  have hB : 0 < B:=by dsimp only [B];positivity
  have HCalibration : ∀ᶠn in atTop,(w n).star.val ≤ Cmass*(M n).data.d ∧
      cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val:=by
    filter_upwards [hw] with n hn
    have Hmass:=actual_high_wall_calibrated_star_mass_mem_band hn
    have Hclock:=(M n).calibrated_slow_window_clock_lower hn
    have Hmass' :=mul_le_mul_of_nonneg_right hbandRoom (M n).data.hd.le
    have hcstar : 0 < starMassBandConstant cu Az/cu:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    have hdn:=(M n).data.hd
    have HT:=mul_le_mul_of_nonneg_right (hT n)
      (show 0 ≤ 3*(starMassBandConstant cu Az/cu)/8*(M n).data.d by positivity)
    have HKroom:=mul_le_mul_of_nonneg_right hKroom (M n).data.hd.le
    have HKbaseline : 3*T0*(starMassBandConstant cu Az/cu)/8*(M n).data.d ≤
        3*(M n).data.T*(starMassBandConstant cu Az/cu)/8*(M n).data.d:=by nlinarith only [HT]
    exact ⟨Hmass.2.trans Hmass',HKroom.trans (HKbaseline.trans Hclock)⟩
  refine ⟨depth,hdepth,saving,hsaving,Apair,hApair,A,B,hA,hB,?_⟩
  filter_upwards [HStages,HCorrection,HMaster,HTerminal depth le_rfl Apair hApair,HCalibration]
    with n hnStages hnCorrection hnMaster hnTerminal hnCalibration
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨base,hbase,hsource0,houter0,hretain0,hcoarse0,hnodes0,_⟩:=
    Hgeometry.exists_dyadic_retained_net Lnet extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,HgridPair⟩:=hnMaster Lnet hmesh base hbase
  have hsource:=hretain source hsource0
  have houter:=hretain outer houter0
  have hnodes : ∀j ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us:=
    fun j hj=>hretain _ (hnodes0 j hj)
  refine ⟨us,hus,(fun u hu=>hretain u (hretain0 u hu)),hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [HgridPair,hnStages Lnet us hus hcoarse hmesh hstar source outer Hgeometry hsource houter
    hnodes hnCalibration.1 hnCalibration.2,hnCorrection Lnet us hus hcoarse hmesh] with jGrid hjPair hjStages hjCorrection
  dsimp only at hjStages hjCorrection ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hw:=finiteCutMasses_nodes us jGrid hstar
  obtain ⟨hstar0,hs,hUV,hV,HmassStar,HmassU,HmassV,hcut,hvcut,hhigh,h4,hz,hri,hrs⟩:=
    Hgeometry.retained_source_geometry as ho (w n).star Hw (finiteCutMasses_nodes us jGrid hsource)
      (finiteCutMasses_nodes us jGrid houter) hnCalibration.1
  have hU : U ≤ as.length:=hUV.le.trans hV
  have hK : cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho (w n).star Hw]
    exact hnCalibration.2
  have HTerm:=hnTerminal (M n) (hfixed n) (w n).star as ho hK hjPair.1
  have HTermChildren:=HTerm.constant_source_children hCm0 ho U hs hU
  have HtermPow : ((dim n+1:ℕ):ℝ)^(-saving) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ dim n+1 by omega)) (neg_nonpos.mpr hsaving.le)
  have Hterminal : _ ≤ 12*(M n).data.d^3:=HTermChildren.trans (by
    have HH:=mul_le_mul_of_nonneg_right HtermPow (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) (pow_nonneg (M n).data.hd.le 3))
    convert HH using 1 <;> ring)
  let mid:=as.take star
  let tail:=as.drop star
  have hparts : as=mid++tail:=by dsimp only [mid,tail];exact (List.take_append_drop star as).symm
  have hindex : mid.length=star:=by dsimp only [mid];rw [List.length_take,Nat.min_eq_left (retainedMassPrefixIndex_le_length (w n).star.val as)]
  have hms : partitionPoint 0 as star ≤ Cmass*(M n).data.d:=by
    dsimp only [star]
    rw [HmassStar]
    exact hnCalibration.1
  have hcutlo : 2*c*(M n).data.d ≤ partitionPoint 0 as U:=by
    dsimp only [U]
    rw [HmassU]
    exact Hgeometry.high_lower
  have HC0:=hjCorrection mid tail hparts (by simpa only [hindex] using hstar0) U
    (by simpa only [hindex] using hs) hU (by simpa only [hindex] using hms) hcut hcutlo
    Hgeometry.scale_small h4 hz hri (by simpa only [hindex] using hrs)
    source.val source.property Hgeometry.source_lower HmassU hnodes
  have Hcorrection : |actualGeneralConstantSourceFrozenCorrection (n:=dim n) (M n).bf (M n).hf as star U hs hU (M n).data.d| ≤
      Ccorrection*(M n).data.d^3:=by
    have hs' : mid.length < U:=by simpa only [hindex] using hs
    rw [actual_general_constant_frozen_correction_index_congr (n:=dim n) (M n).bf (M n).hf as hs hs' hU hindex.symm (M n).data.d]
    exact HC0
  obtain ⟨hs',hU',Hlevels⟩:=hjStages
  have Hprice level (hlevel : level < depth):=
    Hlevels level hlevel
  have HPpair level (hlevel : level < depth):=
    (hjPair.2 level hlevel.le ho U hs hU hK).1
  have htotal : ∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ) ≤ Bclock:=
    fun u hu=>((M n).data.total_clock_le (M n).alpha u hu).trans (M n).hT
  have H:=actual_general_constant_joint_source_affine_bound_of_cubic_four_prices
    (n:=dim n) (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
    ((M n).data.hf_monotone (M n).alpha) htotal (M n).data.hd (M n).data.hd1 hcK
    (by positivity : 0 ≤ ((dim n+1:ℕ):ℝ)^(-gamma/2)) hCstage.le hCstage.le hCstage.le
    (by norm_num : (0:ℝ) ≤ 12) hCcorrection.le ho hs hU hK depth
    HPpair (fun level hl=>(Hprice level hl).1) (fun level hl=>(Hprice level hl).2.1)
    (fun level hl=>(Hprice level hl).2.2) Hterminal Hcorrection
  have HEgamma : -gamma/2=-(actualSlowWindowExponent m delta/256):=by dsimp only [gamma];ring
  dsimp only at H
  rw [HEgamma] at H
  refine ⟨hs,hU,hjPair,HTerm,?_⟩
  simpa only [A,B,den,as,star,U,mul_comm,mul_left_comm,mul_assoc] using H

end OAI.SKFluctuations.Cavity
