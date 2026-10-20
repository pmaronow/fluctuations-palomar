module

public import ComparisonActualHighWallConstantChildrenOtherSourceCubicAlong
public import ComparisonActualHighWallConstantChildrenFirstHighAlong
public import ComparisonActualHighWallFrozenConstantChildrenAlong
public import ComparisonActualHighWallStrongSourceReadout
public import ComparisonActualGeneralFinitePriceEnvelope
public import ComparisonActualGeneralForestReadoutCongruence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

 def ActualHighWallConstantForestCubicPricesOnGrid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (level : ℕ) (C : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) (hs : star < U) (hU : U ≤ as.length) : Prop :=
    let rows:=actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU M.data.d level
      (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as star U hs hU)
    |actualGeneralFourOtherSourceErrorSum M.bf M.hf U M.data.d rows| ≤ C*M.data.d^3 ∧
    |actualGeneralFourFirstHighErrorSum M.bf M.hf U M.data.d rows| ≤ C*M.data.d^2 ∧
    |actualGeneralFourFrozenChildSum M.bf M.hf hs hU M.data.d rows| ≤ C*M.data.d^4

 theorem eventually_actual_high_wall_constant_forest_level_cubic_prices_along
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
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
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
          ActualHighWallConstantForestCubicPricesOnGrid level C (M n) as star U hs hU := by
  have hCm0 : 0 ≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨Co,hCo,HO⟩:=eventually_actual_high_wall_constant_children_other_source_cubic_along
    (D:=D) level dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut
    hCx heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
    hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
  obtain ⟨Cf,hCf,HF⟩:=eventually_actual_high_wall_constant_children_first_HIGH_quadratic_along
    (D:=D) level Cmass Rmacro F hCm0 hm hdelta hroom hcl hcu hAz hC0 hCt hmacro hRhalf
    hFmass hFradius hc hcout hcK dim hdim M hfixed hdlim hsRatio
  obtain ⟨Cfr,hCfr,HFR⟩:=eventually_actual_high_wall_constant_children_frozen_level_quartic_price_along
    (D:=D) level Bclock Cmass cK hCm0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let C:=Co+Cf+Cfr
  refine ⟨C,by dsimp only [C];positivity,?_⟩
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
  have HS:=finiteCutMasses_nodes us jGrid hsource
  have HV:=finiteCutMasses_nodes us jGrid houter
  obtain ⟨hstar0,hs,hUV,hV,HmassStar,HmassU,HmassV,hcut,hvcut,hhigh,h4,hz,hri,hrs⟩:=
    Hgeometry.retained_source_geometry as ho (w n).star Hw HS HV hmass
  have hU : U ≤ as.length:=hUV.le.trans hV
  have hK : cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho (w n).star Hw]
    exact hclock
  let mid:=as.take star
  let tail:=as.drop star
  have hparts : as=mid++tail:=by dsimp only [mid,tail];exact (List.take_append_drop star as).symm
  have hindex : mid.length=star:=by
    dsimp only [mid]
    rw [List.length_take,Nat.min_eq_left (retainedMassPrefixIndex_le_length (w n).star.val as)]
  have hms : partitionPoint 0 as star ≤ Cmass*(M n).data.d:=HmassStar ▸ hmass
  have hcutlo : 2*c*(M n).data.d ≤ partitionPoint 0 as U:=HmassU ▸ Hgeometry.high_lower
  have HOpoint:=hjO mid tail hparts hindex (by simpa only [hindex] using hstar0)
    U (by simpa only [hindex] using hs) (by simpa only [←hparts] using hU)
    (by simpa only [hindex] using hms) hcut Hgeometry.scale_small Hgeometry.low_radius_small
    h4 hz hri (by simpa only [hindex] using hrs)
    source.val source.property Hgeometry.source_lower HmassU hnodes hcutlo (by simpa only [hindex] using hK)
  have HFpoint:=hjF star U hs hU hms Hgeometry.scale_small Hgeometry.low_radius_small hcutlo hK
  have HFRpoint:=hjFR star U hs hU hms hK
  refine ⟨hs,hU,?_⟩
  dsimp only [ActualHighWallConstantForestCubicPricesOnGrid]
  have HObound : |actualGeneralFourOtherSourceErrorSum (M n).bf (M n).hf U (M n).data.d
      (actualGeneralFourCenteredForest (n:=dim n) (M n).bf (M n).hf hs hU (M n).data.d level
        (actualGeneralConstantSourceChildren (n:=dim n) (M n).bf (M n).hf as star U hs hU))| ≤ Co*(M n).data.d^3:=by
    have hs' : mid.length < U:=by simpa only [hindex] using hs
    have hU' : U ≤ (mid++tail).length:=by simpa only [←hparts] using hU
    have HE:=actual_general_constant_forest_other_readout_congr (n:=dim n)
      (M n).bf (M n).hf hs hs' hU hU' hparts hindex.symm (M n).data.d level
    rw [HE]
    exact HOpoint
  have HCo : Co ≤ C:=by dsimp only [C];linarith
  have HCf : Cf ≤ C:=by dsimp only [C];linarith
  have HCfr : Cfr ≤ C:=by dsimp only [C];linarith
  exact ⟨HObound.trans (mul_le_mul_of_nonneg_right HCo (pow_nonneg (M n).data.hd.le 3)),
    HFpoint.trans (mul_le_mul_of_nonneg_right HCf (sq_nonneg (M n).data.d)),
    HFRpoint.trans (mul_le_mul_of_nonneg_right HCfr (pow_nonneg (M n).data.hd.le 4))⟩

end OAI.SKFluctuations.Cavity
