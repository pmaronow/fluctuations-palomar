module

public import ComparisonActualHighWallConstantJointAffineAlong
public import ComparisonActualHighWallScalarFeedbackAlong
public import ComparisonActualGeneralAffineSourceFeedbackAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false
 theorem eventually_actual_high_wall_scalar_defect_quadratic_on_same_strong_master_along
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
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK) (hT0 : 0 < T0)
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
    ∃depth : ℕ,0 < depth ∧ ∃saving : ℝ,0 < saving ∧ ∃Apair : ℝ,1 ≤ Apair ∧ ∃Cd : ℝ,0 < Cd ∧
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
        |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*(M n).data.d^2 := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨depth,hdepth,saving,hsaving,Apair,hApair,A,B,hA,hB,HSource⟩:=
    eventually_actual_high_wall_constant_joint_source_affine_on_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  obtain ⟨R,hR,Cfb,hCfb,HFeedback⟩:=
    eventually_actual_high_wall_original_scalar_feedback_at_calibrated_star_along
      (D:=D) Bclock Cmass (Ccut+1) hCm0 (by linarith) hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let cmean:=3*(starMassBandConstant cu Az/cu)/4
  have hcmean : 0 < cmean:=by
    have HC:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cmean];positivity
  let Cd:=2*(B+Cfb)/cmean
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have Hsmall:=(hdlim.const_mul R).eventually
    (eventually_le_nhds (show R*(0:ℝ) < 1 by simp))
  have HAbsorb:=eventually_scalar_defect_quadratic_of_original_joint_feedback_along
    (saving:=actualSlowWindowExponent m delta/256) (c:=cmean)
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)) hcmean A B Cfb dim hdim
  refine ⟨depth,hdepth,saving,hsaving,Apair,hApair,Cd,hCd,?_⟩
  filter_upwards [HSource,HFeedback,Hsmall,HAbsorb,hw] with n hnSource hnFeedback hnSmall hnAbsorb hnWindow
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnSource source outer Hgeometry Lnet hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [Hgrid,hnFeedback (M n) (hfixed n) hnSmall L Cs (w n) hnWindow us hus hstar]
    with jGrid hjGrid hjFeedback
  dsimp only at hjGrid hjFeedback ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  let V:=retainedMassPrefixIndex outer.val as
  obtain ⟨hs,hU,HPair,HTerm,Hjoint⟩:=hjGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have HmassStar:=nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us jGrid hstar)
  have HmassU:=nativeRetainedCut_partitionPoint as ho source (finiteCutMasses_nodes us jGrid hsource)
  have HmassV:=nativeRetainedCut_partitionPoint as ho outer (finiteCutMasses_nodes us jGrid houter)
  have hUV : U < V:=actual_retained_mass_strict_index as ho source outer
    (finiteCutMasses_nodes us jGrid hsource) (finiteCutMasses_nodes us jGrid houter) Hgeometry.source_lt_outer
  have hV : V ≤ as.length:=retainedMassPrefixIndex_le_length outer.val as
  have hhigh : (M n).data.s ≤ partitionPoint 0 as U:=by rw [HmassU];exact Hgeometry.above_wall
  have hbuffer : partitionPoint 0 as U < partitionPoint 0 as V:=by rw [HmassU,HmassV];exact Hgeometry.source_lt_outer
  have hsize : partitionPoint 0 as V ≤ (Ccut+1)*(M n).data.d:=by rw [HmassV];exact Hgeometry.outer_upper
  have hmass : partitionPoint 0 as star ≤ Cmass*(M n).data.d:=by
    rw [HmassStar]
    exact (actual_high_wall_calibrated_star_mass_mem_band hnWindow).2.trans
      (mul_le_mul_of_nonneg_right hbandRoom (M n).data.hd.le)
  have HF:=hjFeedback U V hs hUV.le hV hhigh hbuffer hsize hmass
  refine ⟨hs,hU,HPair,HTerm,?_⟩
  exact hnAbsorb _ (M n).data.d _ (abs_nonneg _) (M n).data.hd HF Hjoint

end OAI.SKFluctuations.Cavity
