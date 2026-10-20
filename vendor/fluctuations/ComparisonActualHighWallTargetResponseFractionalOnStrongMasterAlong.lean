module

public import ComparisonActualHighWallInitialSavedResponseModulus
public import ComparisonActualHighWallStarOriginalLowRadiusSavingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false
 theorem eventually_actual_high_wall_original_target_response_fractional_on_same_strong_master_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK T0 : ℝ}
    (dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 < Ccut)
    (hCx : 0 < Cx) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
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
    ∃pReader : ℕ,0 < pReader ∧ ∃Cr : ℝ,0 < Cr ∧ ∃e : ℕ→ℝ,
      (∀n,0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
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
        ∀i : ℕ,i < star → partitionPoint 0 as i ≤ Cmass*(M n).data.d →
          |actualGeneralTargetLongitudinalResponse (n:=dim n) (M n).bf (M n).hf as i U| ≤
            Cr*actualHighWallFractionalReaderModulus pReader (M n).data.d (e n)
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)) := by
  obtain ⟨depth,hdepth,saving,hsaving,Apair,hApair,Cd,Ci,hCd,hCi,P,Hsaved⟩:=
    eventually_actual_high_wall_original_target_response_saved_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut.le hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  have hBc : 0 ≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  obtain ⟨Cr,hCr,Hreader⟩:=exists_actual_high_wall_initial_saved_response_fractional_constant
    depth P Bclock cK Cd Ci hBc hcK hCd.le hCi.le
  let e:=fun n=>actualHighWallInitialSavedResponseRate (M n) saving eta Ccut+(M n).data.d^2
  have he : ∀n,0 ≤ e n:=fun n=>add_nonneg
    (actual_high_wall_initial_saved_response_rate_nonneg (M n) saving eta Ccut hCcut.le)
    (sq_nonneg _)
  have He : Tendsto e atTop (𝓝 0):=by
    change Tendsto (fun n=>e n) atTop (𝓝 0)
    have Hrate:=actual_high_wall_initial_saved_response_rate_tendsto_zero_along
      saving eta Ccut hsaving heta hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD
      dim hdim M hfixed hdlim hsRatio
    simpa only [e,zero_add,zero_pow (by decide : 2 ≠ 0)] using Hrate.add (hdlim.pow 2)
  have Hstar:=eventually_actual_high_wall_star_original_low_radius_saving_along
    hm hdelta hC0 (1+actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0))
    (by have H:=actualLowErrorComparisonConstant_nonneg (2*max Bclock 0) (le_max_right Bclock 0);linarith)
    dim hdim M hfixed w hw
  refine ⟨2*(depth+2),by omega,Cr,hCr,e,he,He,?_⟩
  filter_upwards [Hsaved,Hstar] with n hnSaved hnStar
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnSaved source outer Hgeometry Lnet hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [Hgrid,hnStar us hus hstar] with jGrid hjGrid hjStar
  dsimp only at hjGrid hjStar ⊢
  obtain ⟨hs,hU,HPair,HTerm,HD,Hresponse⟩:=hjGrid
  refine ⟨hs,hU,?_⟩
  intro i hi hmi
  exact (Hresponse i hi hmi).trans (Hreader (M n) (finiteCutMasses us jGrid) i
    (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us jGrid)) saving eta Ccut hCcut.le hjStar)

end OAI.SKFluctuations.Cavity
