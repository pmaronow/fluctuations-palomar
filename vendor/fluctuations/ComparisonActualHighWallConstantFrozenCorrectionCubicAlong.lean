module

public import ComparisonActualHighWallConstantFrozenCorrectionReductionAlong
public import ComparisonActualHighWallOriginalTargetTaylorCubicAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_constant_source_frozen_correction_cubic_along
    (dOrder : ℕ) (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut Rmacro F Cx : ℝ) {eta : ℝ}
    (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCx : 0 < Cx) (heta : 0 < eta)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (c : ℝ) (hc : 0 < c) (hcout : cu*Az < c)
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(mid tail : List PositiveMass),as=mid++tail → 0 < mid.length →
      ∀(U : ℕ) (hs : mid.length < U) (hU : U ≤ as.length),
      partitionPoint 0 as mid.length ≤ Cmass*(M n).data.d →
      partitionPoint 0 as U ≤ Ccut*(M n).data.d →
      2*c*(M n).data.d ≤ partitionPoint 0 as U →
      (M n).data.d ≤ Rmacro/2 →
      4*(M n).data.d ≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as 0) ≤
        min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as mid.length) ≤
        min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
      ∀sourceMass : ℝ,∀hsourceMass : 0 < sourceMass,
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
      |actualGeneralConstantSourceFrozenCorrection (n:=dim n) (M n).bf (M n).hf as
        mid.length U hs hU (M n).data.d| ≤ C*(M n).data.d^3 := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_constant_source_frozen_correction_cubic_reduction_along
    (D:=D) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  obtain ⟨Ctaylor,hTaylor,HT⟩:=eventually_actual_high_wall_original_target_Taylor_cubic_along
    (D:=D) dOrder hd p hp hOrder Bclock Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    c hc hcout htheta1 htheta2 hdeficit dim hdim M hfixed hdlim hsRatio
  refine ⟨Cr+Ctaylor,by positivity,?_⟩
  filter_upwards [HR,HT] with n hnR hnT
  intro L us hus hret hmesh
  filter_upwards [hnR (M n) (hfixed n) L us hus hret hmesh,hnT L us hus hret hmesh]
    with jGrid hjR hjT
  dsimp only at hjR hjT ⊢
  intro mid tail hparts hmid U hs hU hmass hcut hcutlo hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  have Hcorrection:=hjR mid.length U hs hU hmass
  have HTaylor:=hjT mid tail hparts hmid U hs hU hmass hcut hcutlo hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  exact Hcorrection.trans (by nlinarith only [HTaylor])

end OAI.SKFluctuations.Cavity
