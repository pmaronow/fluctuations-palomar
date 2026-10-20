module

public import ComparisonActualHighWallTargetMeanOnStrongMasterAlong
public import ComparisonActualHighWallSlowWindowProducerAlong
public import ComparisonActualHighWallConcreteCalibrationRoom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum PositiveLaplaceAssembly
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false
 theorem eventually_actual_high_wall_omitted_mean_cubic_from_regular_physical_minimum_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK T0 : ℝ}
    (dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass)
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
    (hmmax : m < 1/300)
    (hconcrete : ∀n,(M n).data.d=wallHighD m (dim n+1))
    (hepsilon : ∀n,upperInitialEpsilon m (dim n+1) ≤ (M n).data.epsilon) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (M n).data.s,
      orderedPathS (dim n+1) (M n).bf (M n).hf u ≤
        wallMeanScale C (M n).data.d (M n).data.epsilon := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨Cs,hCs,w,hw⟩:=ActualHighWallOverlapMinimum.exists_actual_high_wall_calibrated_slow_window_sequence_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M (fun n=>(M n).data.d)
    (fun n=>(hfixed n).le) (fun _=>le_rfl) hdlim hsRatio hT
  obtain ⟨Ccut,hCcut,HGeometry⟩:=exists_actual_high_wall_strong_source_masses_along
    Cmass Cx c Rmacro hCm0 hCx hc hmacro hcl hcu hAz dim M hfixed hdlim
  obtain ⟨Cd,Cgap,hCd,hCgap,HMean⟩:=
    eventually_actual_high_wall_original_target_mean_cubic_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut.le hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  obtain ⟨R,hR,HScalar⟩:=eventually_actual_high_wall_original_scalar_remainder_of_buffer_along
    (D:=D) Bclock (Ccut+1) (by linarith) hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let Cr:=nativeScalarLowRemainderConstant (Ccut+1) R R
  have hCr : 0 ≤ Cr:=nativeScalarLowRemainderConstant_nonneg (by linarith) hR.le hR.le
  let C:=4*Bclock*(Cgap+Cr+1/16)
  have hBclock : 0 < Bclock:=(M 0).data.hTpos.trans_le (M 0).hT
  have hC : 0 < C:=by dsimp only [C];positivity
  have HSmall:=(hdlim.const_mul R).eventually
    (eventually_le_nhds (show R*(0:ℝ) < 1 by simp))
  have HRoom:=eventually_actual_concrete_high_wall_defect_calibration_room_along hm hmmax Bclock Cd dim hdim
  have hStart : 1 ≤ calibratedBandStart cu Az:=by
    have H:=mul_nonneg hcu.le hAz
    unfold calibratedBandStart starMassBandConstant
    nlinarith only [H,hcu]
  refine ⟨C,hC,?_⟩
  filter_upwards [HMean,HGeometry,HScalar,HSmall,HRoom,hw] with n hnMean hnGeometry hnScalar hnSmall hnRoom hnWindow
  obtain ⟨source,outer,hsourceExact,houterExact,Hgeometry⟩:=hnGeometry
  have hRoom : (Cd+1)*(M n).data.d^2 ≤ 1/2 ∧
      4*Bclock*(Cd+1)*(M n).data.d^2 ≤ (M n).data.epsilon:=by
    simpa only [←hconcrete n] using hnRoom (M n).data.epsilon (hepsilon n)
  intro u hu
  by_cases hu0 : u=0
  · simp only [hu0,orderedPathS,orderedPathPair_zero]
    unfold wallMeanScale
    exact div_nonneg (mul_nonneg hC.le (pow_nonneg (M n).data.hd.le 3)) (M n).data.hepsilon.1.le
  have huPos : 0 < u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have huOne : u ≤ 1:=hu.2.le.trans (M n).data.hs1
  let target : PositiveMass:=⟨u,huPos⟩
  obtain ⟨Lnet,hLnet⟩:=exists_nat_one_div_lt (M n).data.hd
  have hmesh : ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs:=by
    rw [hfixed n]
    simpa only [one_div,Nat.cast_add,Nat.cast_one] using hLnet.le
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnMean source outer Hgeometry Lnet hmesh [target] (by intro v hv;obtain rfl:=List.mem_singleton.mp hv;exact huOne)
  have htarget : target∈us:=hretain target (List.mem_singleton_self target)
  obtain ⟨jGrid,hjGrid⟩:=Hgrid.exists
  dsimp only at hjGrid
  let as:=finiteCutMasses us jGrid
  let i:=retainedMassPrefixIndex target.val as
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  let V:=retainedMassPrefixIndex outer.val as
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Htarget:=finiteCutMasses_nodes us jGrid htarget
  have Hw:=finiteCutMasses_nodes us jGrid hstar
  have HS:=finiteCutMasses_nodes us jGrid hsource
  have HV:=finiteCutMasses_nodes us jGrid houter
  have HmassI : partitionPoint 0 as i=u:=nativeRetainedCut_partitionPoint as ho target Htarget
  have HmassStar:=nativeRetainedCut_partitionPoint as ho (w n).star Hw
  have HmassU:=nativeRetainedCut_partitionPoint as ho source HS
  have HmassV:=nativeRetainedCut_partitionPoint as ho outer HV
  have hhighStar : (M n).data.s ≤ (w n).star.val:=
    ((M n).hsxs.trans (by rw [hfixed n];simpa only [one_mul] using mul_le_mul_of_nonneg_right hStart (M n).data.hd.le)).trans
      (actual_high_wall_calibrated_star_mass_mem_band hnWindow).1
  have hi : i < star:=actual_retained_mass_strict_index as ho target (w n).star Htarget Hw
    (hu.2.trans_le hhighStar)
  have hi0 : 0 < i:=by
    by_contra hn
    have hz : i=0:=by omega
    rw [hz] at HmassI
    simp only [partitionPoint,partitionValues_zero,id_eq] at HmassI
    exact hu0 HmassI.symm
  have hmi : partitionPoint 0 as i ≤ Cmass*(M n).data.d:=by
    rw [HmassI]
    apply hu.2.le.trans
    apply (M n).hsxs.trans
    rw [hfixed n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hCm (M n).data.hd.le
  obtain ⟨hs,hU,HD,HG⟩:=hjGrid
  have hUV : U < V:=actual_retained_mass_strict_index as ho source outer HS HV Hgeometry.source_lt_outer
  have hV : V ≤ as.length:=retainedMassPrefixIndex_le_length outer.val as
  have hhigh : (M n).data.s ≤ partitionPoint 0 as U:=by rw [HmassU];exact Hgeometry.above_wall
  have hbuffer : partitionPoint 0 as U < partitionPoint 0 as V:=by rw [HmassU,HmassV];exact Hgeometry.source_lt_outer
  have hsize : partitionPoint 0 as V ≤ (Ccut+1)*(M n).data.d:=by rw [HmassV];exact Hgeometry.outer_upper
  have HSscalar:=hnScalar (M n) (hfixed n) as ho (M n).data.d (M n).data.hd.le
    (hfixed n).le hnSmall i U V (hi.trans hs) hUV.le hV hhigh hbuffer hsize
  have H:=actual_high_wall_omitted_mean_suppression_of_finite_original_prices (M n) as ho i star U
    hi.le hs hU (by rw [HmassStar];exact hhighStar) (by rw [HmassI];exact hu.2)
    hCd.le hRoom.1 hRoom.2 HD (HG i hi0 hi hmi) HSscalar
  simpa only [HmassI] using H

end OAI.SKFluctuations.Cavity
