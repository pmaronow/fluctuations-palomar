module

public import ComparisonActualHighWallScalarDefectOnStrongMasterAlong
public import ComparisonActualHighWallInitialSavedLevelCoefficients
public import ComparisonActualHighWallInitialFrozenResponseAlong
public import ComparisonActualGeneralTargetResponseLevelVariableSavedNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

def actualHighWallInitialSavedTargetResponsePrice
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (depth : ℕ) (P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val)
    (Cd Ci saving eta Ccut cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star : ℕ) : ℝ :=
  let d:=M.data.d
  let den:=Real.exp (-4*Bclock)*cK
  let Q:=((n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2)
  let T:=2*((n+1:ℕ):ℝ)^(-saving)
  (depth:ℝ)*(d^2*(∑j : Fin depth,(P j).B Ccut cK M as i star)/den+
    d^3*((Cd*Q+(∑j : Fin depth,(P j).A eta cK M as i))/den+
      (∑j : Fin depth,(P j).F M)+(∑j : Fin depth,(P j).Cfr)*d^2))+
    T*d^3+Ci*d^5

 theorem eventually_actual_high_wall_original_target_response_saved_on_same_strong_master_along
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
    ∃depth : ℕ,0 < depth ∧ ∃saving : ℝ,0 < saving ∧ ∃Apair : ℝ,1 ≤ Apair ∧
      ∃Cd Ci : ℝ,0 < Cd ∧ 0 < Ci ∧
      ∃P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val,
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
        (let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*(M n).data.d^2) ∧
        ∀i : ℕ,i < star → partitionPoint 0 as i ≤ Cmass*(M n).data.d →
          |actualGeneralTargetLongitudinalResponse (n:=dim n) (M n).bf (M n).hf as i U| ≤
            actualHighWallInitialSavedTargetResponsePrice depth P Cd Ci saving eta Ccut cK
              (M n) as i star := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨depth,hdepth,saving,hsaving,Apair,hApair,Cd,hCd,HDefect⟩:=
    eventually_actual_high_wall_scalar_defect_quadratic_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK hT0 hKroom hbandRoom dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  obtain ⟨P,HStages⟩:=exists_actual_high_wall_initial_forest_all_levels_saved_prices_along
    (D:=D) depth dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut
    hCx heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
    hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_high_wall_initial_frozen_response_quintic_price_along
    (D:=D) Bclock Cmass hCm0 hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
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
  refine ⟨depth,hdepth,saving,hsaving,Apair,hApair,Cd,Ci,hCd,hCi,P,?_⟩
  filter_upwards [HDefect,HStages,HI,HCalibration] with n hnDefect hnStages hnI hnCalibration
  intro source outer Hgeometry Lnet hmesh extra hextra
  obtain ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,Hgrid⟩:=
    hnDefect source outer Hgeometry Lnet hmesh extra hextra
  refine ⟨us,hus,hretain,hcoarse,hstar,hsource,houter,hnodes,?_⟩
  filter_upwards [Hgrid,hnStages Lnet us hus hcoarse hmesh hstar source outer Hgeometry hsource houter
    hnodes hnCalibration.1 hnCalibration.2,hnI (M n) (hfixed n) Lnet us hus hcoarse hmesh]
    with jGrid hjGrid hjStages hjI
  dsimp only at hjGrid hjStages hjI ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  obtain ⟨hs,hU,HPair,HTerm,HD⟩:=hjGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hw:=finiteCutMasses_nodes us jGrid hstar
  have HmassStar:=nativeRetainedCut_partitionPoint as ho (w n).star Hw
  have hms : partitionPoint 0 as star ≤ Cmass*(M n).data.d:=by dsimp only [star];rw [HmassStar];exact hnCalibration.1
  have hK : cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho (w n).star Hw]
    exact hnCalibration.2
  have htotal : ∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ) ≤ Bclock:=
    fun u hu=>((M n).data.total_clock_le (M n).alpha u hu).trans (M n).hT
  let q:=((dim n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2)
  have hq : 0 ≤ q:=by dsimp only [q];positivity
  refine ⟨hs,hU,HPair,HTerm,HD,?_⟩
  intro i hi hmi
  have HP level (hlevel : level < depth):=(HPair.2 level hlevel.le ho U hs hU hK).2 i hi.le hmi 0
  have Hlevel : ∀j : Fin depth,(P j).PriceOnGrid eta Ccut cK (M n) as i star U hi hs hU := by
    intro j
    obtain ⟨hs',hU',H⟩:=hjStages j
    exact H i hi hmi
  have Hprices (j : Fin depth):=(P j).saved_prices eta Ccut cK (M n) as i star U hi hs hU (Hlevel j)
  have Hpositive (j : Fin depth):=(P j).coefficients_nonneg eta Ccut cK hcK hCcut (M n) as i star
  have Hfrozen:=hjI i star U hi.le hs hU hmi hms
  have Hterm:=HTerm.initial_target U i hi.le hs hU hmi
  have Hterminal:=Hterm.trans_eq (show
    2*(((dim n+1:ℕ):ℝ)^(-saving)*(M n).data.d^3)=
      (2*((dim n+1:ℕ):ℝ)^(-saving))*(M n).data.d^3 by ring)
  have H:=actual_general_target_response_level_variable_saved_of_original_four_prices
    (n:=dim n) (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
    ((M n).data.hf_monotone (M n).alpha) htotal (M n).data.hd hcK hq
    ho hi.le hs hU hK HD depth
    (fun j=>(P j).A eta cK (M n) as i) (fun j=>(P j).B Ccut cK (M n) as i star)
    (fun j=>(P j).F (M n)) (fun j=>(P j).Cfr)
    (fun j=>(Hpositive j).1) (fun j=>(Hpositive j).2.1)
    (fun j=>(Hpositive j).2.2.1) (fun j=>(Hpositive j).2.2.2)
    HP (fun j=>(Hprices j).1) (fun j=>(Hprices j).2.1) (fun j=>(Hprices j).2.2) Hterminal Hfrozen
  simpa only [actualHighWallInitialSavedTargetResponsePrice,q] using H

end OAI.SKFluctuations.Cavity
