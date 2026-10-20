module

public import ComparisonActualHighWallInitialOtherSourceSavedForestAlong
public import ComparisonActualHighWallInitialFirstHighSavedAlong
public import ComparisonActualHighWallFrozenInitialForestAlong
public import ComparisonActualHighWallStrongSourceReadout
public import ComparisonActualGeneralForestReadoutCongruence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

def ActualHighWallInitialForestSavedLevelPricesOnGrid
    {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd : ℝ)
    (C CiU CiB CiM : Fin (1+level)→ℝ) (Cf Cr Cfirst Cfr eta Ccut cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star U : ℕ) (hi : i < star)
    (hs : star < U) (hU : U ≤ as.length) : Prop :=
    let d:=M.data.d
    let Di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
    let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
    let Dstar:=(1+CB)*(nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ))
    let I:=∫u in 0..Ccut*d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)
    let qsecond:=actualHighWallInitialFullB0Envelope (1+level) C CiU CiB CiM Cf Cr
      (originalHighWallInitialPairErrorScale M as i) d (n:ℝ) eta
    let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
      (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level
    let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
      (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level
    let rho:=((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
    let rows:=actualGeneralFourCenteredForest M.bf M.hf hs hU d level
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.le.trans (hs.le.trans hU))]
    |actualGeneralFourOtherSourceErrorSum M.bf M.hf U d rows| ≤
      d^4*(Ca*((n:ℝ)^(-eta))+Cg*((n:ℝ)^(-eta))+
        Cd*((n+1:ℕ):ℝ)^(-m)+2*qsecond)*(2*V)+
      d^3*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)*(2*V)+
      d^2*(Ca+2*Cl+Cj+C4+CY)*(2*VP*rho*d^2)+
      d^3*(Ca+2*Cl+Cj+C4+CY+Ch)*(2*VP*rho*d) ∧
    |actualGeneralFourFirstHighErrorSum M.bf M.hf U d rows| ≤ Cfirst*rho*d^3 ∧
    |actualGeneralFourFrozenChildSum M.bf M.hf hs hU d rows| ≤ Cfr*d^5

theorem eventually_actual_high_wall_initial_forest_saved_level_prices_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK : ℝ}
    (level dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    (hCx : 0 < Cx) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) (hL : 0 < L)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd : ℝ,
      0 < Ca ∧ 0 < Cg ∧ 0 < Cl ∧ 0 < Cj ∧ 0 < C4 ∧ 0 < CY ∧ 0 < Ch ∧
      0 < Cgl ∧ 0 < Cjl ∧ 0 < Cd ∧
      ∃C CiU CiB CiM : Fin (1+level)→ℝ,∃Cf Cr Cfirst Cfr : ℝ,
      (∀a,0 < C a ∧ 0 < CiU a ∧ 0 < CiB a ∧ 0 < CiM a) ∧
      0 < Cf ∧ 0 < Cr ∧ 0 < Cfirst ∧ 0 < Cfr ∧
      ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses Lnet,u∈us) →
        ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀source outer : PositiveMass,
        ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer →
        source∈us → outer∈us →
        (∀j ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us) →
        (w n).star.val ≤ Cmass*(M n).data.d →
        cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex source.val as
        ∃hs : star < U,∃hU : U ≤ as.length,
          ∀i : ℕ,∀hi : i < star,partitionPoint 0 as i ≤ Cmass*(M n).data.d →
            ActualHighWallInitialForestSavedLevelPricesOnGrid
              Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd C CiU CiB CiM Cf Cr Cfirst Cfr eta Ccut cK
              (M n) as i star U hi hs hU := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
    C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,HO⟩:=
    eventually_actual_high_wall_initial_other_source_saved_forest_along
      (D:=D) level dOrder hd p hp hOrder htheta1 htheta2 hdeficit
      Cmass Ccut Rmacro F Cx hCm hCcut hCx heta hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
  obtain ⟨Cfirst,hCfirst,HF⟩:=eventually_actual_high_wall_initial_first_HIGH_saved_along
    (D:=D) level Cmass Rmacro F hCm0 hm hdelta hroom hcl hcu hAz hC0 hCt
    hmacro hRhalf hFmass hFradius hc hcout hcK dim hdim M hfixed hdlim hsRatio
  obtain ⟨Cfr,hCfr,HFR⟩:=eventually_actual_high_wall_initial_frozen_level_quintic_price_along
    (D:=D) level Bclock Cmass cK hCm0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
    C,CiU,CiB,CiM,Cf,Cr,Cfirst,Cfr,hpositive,hCf,hCr,hCfirst,hCfr,?_⟩
  filter_upwards [HO,HF,HFR] with n hnO hnF hnFR
  intro Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock
  filter_upwards [hnO Lnet us hus hret hmesh hstar,hnF Lnet us hus hret hmesh,
    hnFR (M n) (hfixed n) Lnet us hus hret hmesh] with jGrid hjO hjF hjFR
  dsimp only at hjO hjF hjFR ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  have ho:=finiteCutMasses_ordered us hus jGrid
  have Hw:=finiteCutMasses_nodes us jGrid hstar
  obtain ⟨hstar0,hs,hUV,hV,HmassStar,HmassU,HmassV,hcut,hvcut,hhigh,h4,hz,hri0,hrs⟩:=
    Hgeometry.retained_source_geometry as ho (w n).star Hw (finiteCutMasses_nodes us jGrid hsource)
      (finiteCutMasses_nodes us jGrid houter) hmass
  have hU : U ≤ as.length:=hUV.le.trans hV
  have hK : cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho (w n).star Hw]
    exact hclock
  have hms : partitionPoint 0 as star ≤ Cmass*(M n).data.d:=by
    dsimp only [star];rw [HmassStar];exact hmass
  have hcutlo : 2*c*(M n).data.d ≤ partitionPoint 0 as U:=by
    dsimp only [U];rw [HmassU];exact Hgeometry.high_lower
  refine ⟨hs,hU,?_⟩
  intro i hi hmi
  let pre:=as.take i
  let rem:=as.drop i
  let mid:=rem.take (star-i)
  let tail:=rem.drop (star-i)
  have hipre : pre.length=i:=by
    dsimp only [pre];rw [List.length_take,Nat.min_eq_left (hi.le.trans (hs.le.trans hU))]
  have hmidlen : mid.length=star-i:=by
    dsimp only [mid,rem];rw [List.length_take,List.length_drop,Nat.min_eq_left (by omega)]
  have histar : pre.length+mid.length=star:=by rw [hipre,hmidlen];exact Nat.add_sub_of_le hi.le
  have hmid : 0 < mid.length:=by rw [hmidlen];exact Nat.sub_pos_of_lt hi
  have hparts : as=pre++(mid++tail):=by
    have H1 : rem=mid++tail:=by dsimp only [mid,tail];exact (List.take_append_drop (star-i) rem).symm
    rw [←H1];dsimp only [pre,rem];exact (List.take_append_drop i as).symm
  have hri : (M n).data.wallRadius (M n).alpha (partitionPoint 0 as i) ≤
      min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4):=by
    dsimp only [U];rw [HmassU]
    exact Hgeometry.low_radius _ (partitionPoint_mem as ho i) hmi
  have hs' : pre.length+mid.length < U:=by simpa only [histar] using hs
  have hU' : U ≤ (pre++(mid++tail)).length:=by simpa only [←hparts] using hU
  have HOpoint:=hjO pre mid tail hparts histar hmid U hs' hU'
    (by simpa only [hipre] using hmi) (by simpa only [histar] using hms) hcut
    Hgeometry.scale_small Hgeometry.low_radius_small h4 hz (by simpa only [hipre] using hri)
    (by simpa only [histar] using hrs) source.val source.property Hgeometry.source_lower HmassU
    hnodes hcutlo (by simpa only [histar] using hK)
  have HFpoint:=hjF i star U hi.le hs hU hmi hms Hgeometry.scale_small
    Hgeometry.low_radius_small hcutlo hK 0
  have HFRpoint:=hjFR i star U hi.le hs hU hmi hms hK
  dsimp only [ActualHighWallInitialForestSavedLevelPricesOnGrid]
  have HObound : |actualGeneralFourOtherSourceErrorSum (M n).bf (M n).hf U (M n).data.d
      (actualGeneralFourCenteredForest (n:=dim n) (M n).bf (M n).hf hs hU (M n).data.d level
        [nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.le.trans (hs.le.trans hU))])| ≤
      (M n).data.d^4*(Ca*((dim n:ℝ)^(-eta))+Cg*((dim n:ℝ)^(-eta))+
        Cd*((dim n+1:ℕ):ℝ)^(-m)+2*actualHighWallInitialFullB0Envelope (1+level)
          C CiU CiB CiM Cf Cr (originalHighWallInitialPairErrorScale (M n) as i)
          (M n).data.d (dim n:ℝ) eta)*(2*nativeActualWeightedFrontierCost
            nativeActualOriginalFourGCenteredBranches (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level)+
      (M n).data.d^3*(CY*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
        (CY+Cgl+Cjl)*((1+actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0))*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as star+1/(dim n+1:ℕ)))+
        CY*(∫u in 0..Ccut*(M n).data.d,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)))*
          (2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
            (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level)+
      (M n).data.d^2*(Ca+2*Cl+Cj+C4+CY)*(2*nativeActualWeightedProfileFrontierCost
        nativeActualOriginalFourGCenteredBranches (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level*
          ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))*(M n).data.d^2)+
      (M n).data.d^3*(Ca+2*Cl+Cj+C4+CY+Ch)*(2*nativeActualWeightedProfileFrontierCost
        nativeActualOriginalFourGCenteredBranches (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level*
          ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))*(M n).data.d):=by
    have HE:=actual_general_initial_forest_other_readout_congr (n:=dim n)
      (M n).bf (M n).hf hi.le (by omega : pre.length ≤ pre.length+mid.length) hs hs' hU hU'
      hparts hipre.symm histar.symm (M n).data.d 0 level
    rw [HE]
    conv_rhs =>
      rw [←histar, ←hipre]
    exact HOpoint
  exact ⟨HObound,HFpoint,HFRpoint⟩

end OAI.SKFluctuations.Cavity
