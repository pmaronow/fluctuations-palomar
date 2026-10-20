module

public import ComparisonActualHighWallTargetResponseFractionalOnStrongMasterAlong
public import ComparisonActualHighWallOriginalTaylorFractionalReaderAlong
public import ComparisonActualHighWallOriginalMeanCorrectionQuarticAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_target_three_fractional_prices_on_same_strong_master_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK T0 : ℝ}
    (dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 < Ccut)
    (hcutgap : Cmass < Ccut) (hCx : 0 < Cx) (heta : 0 < eta)
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
    ∃pReader : ℕ,0 < pReader ∧ ∃Cm Cr Ctaylor : ℝ,
      0 < Cm ∧ 0 < Cr ∧ 0 < Ctaylor ∧ ∃e : ℕ→ℝ,
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
          |actualGeneralTargetOriginalMeanCorrection (n:=dim n) (M n).bf (M n).hf as i U| ≤
            Cm*(M n).data.d^4 ∧
          |actualGeneralTargetLongitudinalResponse (n:=dim n) (M n).bf (M n).hf as i U| ≤
            Cr*actualHighWallFractionalReaderModulus pReader (M n).data.d (e n)
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)) ∧
          |actualGeneralTargetOriginalTaylorPart (n:=dim n) (M n).bf (M n).hf as i U| ≤
            Ctaylor*actualHighWallFractionalReaderModulus pReader (M n).data.d (e n)
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)) := by
  obtain ⟨pReader,hpReader,Cr,hCr,eResponse,heResponse,HeResponse,Hresponse⟩:=
    eventually_actual_high_wall_original_target_response_fractional_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hD hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  obtain ⟨Cm,hMean,Hmean⟩:=eventually_actual_high_wall_original_mean_correction_quartic_price_along
    (D:=D) Bclock hm hC0 dim hdim
  have hCmass : 0 < Cmass:=lt_of_lt_of_le zero_lt_one hCm
  obtain ⟨Ctaylor,hCtaylor,HTaylor⟩:=
    eventually_actual_high_wall_original_Taylor_fractional_reader_price_along
      pReader Bclock Cmass Ccut c hCmass hcutgap hm hdelta hroom hcl hcu hAz hC0 hCt
      hc hcout dim hdim M hfixed hdlim hsRatio
  let e:=fun n=>eResponse n+actualHighWallOriginalTaylorThermalRate dim M Ccut n
  have heTaylor : ∀n,0 ≤ actualHighWallOriginalTaylorThermalRate dim M Ccut n:=
    actual_high_wall_original_taylor_thermal_rate_nonneg dim M hCcut.le
  have he : ∀n,0 ≤ e n:=fun n=>add_nonneg (heResponse n) (heTaylor n)
  have HeTaylor:=actual_high_wall_original_taylor_thermal_rate_tendsto_zero_along
    hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have He : Tendsto e atTop (𝓝 0):=by
    change Tendsto (fun n=>e n) atTop (𝓝 0)
    simpa only [e,zero_add] using HeResponse.add HeTaylor
  refine ⟨pReader,hpReader,Cm,Cr,Ctaylor,hMean,hCr,hCtaylor,e,he,He,?_⟩
  filter_upwards [Hresponse,Hmean,HTaylor] with n hnResponse hnMean hnTaylor
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnResponse source outer Hgeometry Lnet hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [Hgrid,hnMean (M n) (hfixed n) us hus,
    hnTaylor Lnet us hus hcoarse hmesh] with jGrid hjGrid hjMean hjTaylor
  dsimp only at hjGrid hjMean hjTaylor ⊢
  obtain ⟨hs,hU,Hfinite⟩:=hjGrid
  refine ⟨hs,hU,?_⟩
  intro i hi hmi
  have hiU:=hi.trans hs
  have HU:=nativeRetainedCut_partitionPoint (finiteCutMasses us jGrid)
    (finiteCutMasses_ordered us hus jGrid) source (finiteCutMasses_nodes us jGrid hsource)
  have hsourceMass : partitionPoint 0 (finiteCutMasses us jGrid)
      (retainedMassPrefixIndex source.val (finiteCutMasses us jGrid)) ≤ Ccut*(M n).data.d:=by
    rw [HU]
    exact Hgeometry.source_upper
  have hsourceLow : 2*c*(M n).data.d ≤ partitionPoint 0 (finiteCutMasses us jGrid)
      (retainedMassPrefixIndex source.val (finiteCutMasses us jGrid)):=by
    rw [HU]
    exact Hgeometry.high_lower
  have Hresp:=Hfinite i hi hmi
  have Htaylor:=hjTaylor i _ hiU hU hmi hsourceMass hsourceLow
  have HmonoResponse:=actual_high_wall_fractional_reader_modulus_mono_rate pReader
    (Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) i+1/(dim n+1:ℕ))
    (M n).data.hd.le (show eResponse n ≤ e n from le_add_of_nonneg_right (heTaylor n))
  have HmonoTaylor:=actual_high_wall_fractional_reader_modulus_mono_rate pReader
    (Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) i+1/(dim n+1:ℕ))
    (M n).data.hd.le (show actualHighWallOriginalTaylorThermalRate dim M Ccut n ≤ e n from
      le_add_of_nonneg_left (heResponse n))
  exact ⟨hjMean i _ hiU hU,Hresp.trans (mul_le_mul_of_nonneg_left HmonoResponse hCr.le),
    Htaylor.trans (mul_le_mul_of_nonneg_left HmonoTaylor hCtaylor.le)⟩

end OAI.SKFluctuations.Cavity
