module

public import ComparisonActualHighWallTargetResponseOnStrongMasterAlong
public import ComparisonActualHighWallOriginalTargetTaylorCubicAlong
public import ComparisonActualHighWallOriginalMeanCorrectionAlong
public import ComparisonActualGeneralTargetMeanSameCut

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false
 theorem eventually_actual_high_wall_original_target_mean_cubic_on_same_strong_master_along
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
    ∃Cd Cgap : ℝ,0 < Cd ∧ 0 < Cgap ∧
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
        (let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*(M n).data.d^2) ∧
        ∀i : ℕ,0 < i → i < star → partitionPoint 0 as i ≤ Cmass*(M n).data.d →
          |nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i-
            nativeOriginalScalarPairMean as (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) i| ≤ Cgap*(M n).data.d^3 := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨Cd,Cr,hCd,hCr,HResponse⟩:=
    eventually_actual_high_wall_original_target_response_cubic_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  obtain ⟨Cm,hCmprice,HMean⟩:=eventually_actual_high_wall_original_mean_correction_cubic_price_along
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) Bclock hm hC0 dim hdim
  obtain ⟨Ctaylor,hCtaylor,HTaylor⟩:=eventually_actual_high_wall_original_target_Taylor_cubic_along
    (D:=D) dOrder hd p hp hOrder Bclock Cmass Ccut Rmacro F Cx hCm0 hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    c hc hcout htheta1 htheta2 hdeficit dim hdim M hfixed hdlim hsRatio
  let Cgap:=Cm+2*Bclock*Cr+Ctaylor
  have hBclock : 0 < Bclock:=(M 0).data.hTpos.trans_le (M 0).hT
  have hCgap : 0 < Cgap:=by dsimp only [Cgap];positivity
  refine ⟨Cd,Cgap,hCd,hCgap,?_⟩
  filter_upwards [HResponse,HMean,HTaylor,hw] with n hnResponse hnMean hnTaylor hnWindow
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnResponse source outer Hgeometry Lnet hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [Hgrid,hnMean (M n) (hfixed n) us hus,hnTaylor Lnet us hus hcoarse hmesh]
    with jGrid hjGrid hjMean hjTaylor
  dsimp only at hjGrid hjMean hjTaylor ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  obtain ⟨hs,hU,HD,HR⟩:=hjGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hmass : (w n).star.val ≤ Cmass*(M n).data.d:=
    (actual_high_wall_calibrated_star_mass_mem_band hnWindow).2.trans
      (mul_le_mul_of_nonneg_right hbandRoom (M n).data.hd.le)
  obtain ⟨hstar0,hs0,hUV,hV,HmassStar,HmassU,HmassV,hcut,hvcut,hhigh,h4,hz,hri0,hrs⟩:=
    Hgeometry.retained_source_geometry as ho (w n).star (finiteCutMasses_nodes us jGrid hstar)
      (finiteCutMasses_nodes us jGrid hsource) (finiteCutMasses_nodes us jGrid houter) hmass
  have hcutlo : 2*c*(M n).data.d ≤ partitionPoint 0 as U:=by dsimp only [U];rw [HmassU];exact Hgeometry.high_lower
  have htotal : ∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ) ≤ Bclock:=
    fun u hu=>((M n).data.total_clock_le (M n).alpha u hu).trans (M n).hT
  refine ⟨hs,hU,HD,?_⟩
  intro i hi0 hi hmi
  let mid:=as.take i
  let tail:=as.drop i
  have hindex : mid.length=i:=by dsimp only [mid];rw [List.length_take,Nat.min_eq_left (hi.le.trans (hs.le.trans hU))]
  have hparts : as=mid++tail:=by dsimp only [mid,tail];exact (List.take_append_drop i as).symm
  have hri : (M n).data.wallRadius (M n).alpha (partitionPoint 0 as i) ≤
      min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4):=by
    dsimp only [U]
    rw [HmassU]
    exact Hgeometry.low_radius _ (partitionPoint_mem as ho i) hmi
  have HT:=hjTaylor mid tail hparts (by simpa only [hindex] using hi0) U
    (by simpa only [hindex] using hi.trans hs) hU (by simpa only [hindex] using hmi) hcut hcutlo
    Hgeometry.scale_small h4 hz hri0 (by simpa only [hindex] using hri)
    source.val source.property Hgeometry.source_lower HmassU hnodes
  have HTprice : |actualGeneralTargetOriginalTaylorPart (n:=dim n) (M n).bf (M n).hf as i U| ≤ Ctaylor*(M n).data.d^3:=by
    simpa only [hindex] using HT
  exact actual_general_target_mean_same_cut_cubic_of_original_reader_prices
    (n:=dim n) (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
    ((M n).data.hf_monotone (M n).alpha) (M n).data.hd.le hCr.le htotal as ho i U
    (hi.trans hs) hU (hjMean i U (hi.trans hs) hU) (HR i hi hmi) HTprice

end OAI.SKFluctuations.Cavity
