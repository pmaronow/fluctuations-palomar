module

public import SKProof.Port.ComparisonActualOriginalQActualFourGaCurrent
public import ComparisonSignedCavityActualSharpSourceCurrentGaAlong
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQPullbackFourCutReadout
public import SKProof.Port.ComparisonActualOriginalQInheritedFourGaCurrentRootsAlong

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualSharpSourceGaInitialOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
      ∃hs : pre.length+mid.length<U,∃hU : U≤(pre++(mid++tail)).length,
      ∀a x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
      ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum ≤
        C*(dim n:ℝ)^(-eta)*(M n).xs^2*x

def ActualSharpSourceGaConstantOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta C : ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(mid tail : List PositiveMass),mid++tail=as →
      mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∃hs : mid.length<U,∃hU : U≤(mid++tail).length,
      ((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
        [(nativeActualConstantState (mid++tail) 0 mid.length).projection (hs.le.trans hU)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q (M n) U (W n) Q|)).sum ≤
        C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualFourGaCurrentInitialOnEveryFinalNetAlong_original_q.on_sharp_source_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualFourGaCurrentInitialOnEveryFinalNetAlong_original_q depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualSharpSourceGaInitialOnEveryFinalNetAlong_original_q depth eta Cmass C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  intro pre mid tail hcut hindex hmid
  have hs : pre.length+mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
    rw [hindex]
    exact Hs
  have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(pre++(mid++tail)).length:=by
    rw [hcut]
    exact HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  intro a x hx hxW hmi
  have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
  have Hmass' : partitionPoint 0 (finiteCutMasses us j) (pre.length+mid.length) ≤ Cmass*W n:=by
    rw [hindex]
    exact Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
  exact hj pre mid tail hcut hindex Hmass' hmid _ hs hU a x (radius n) hx hxW hmi
    Hrad Hrad1 HRU (by simpa only [hindex] using HRstar) Hrz
    (by simpa only [hindex] using HK)

theorem ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong_original_q.on_sharp_source_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong_original_q depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualSharpSourceGaConstantOnEveryFinalNetAlong_original_q depth eta C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  intro mid tail hcut hindex
  have hs : mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
    rw [hindex]
    exact Hs
  have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(mid++tail).length:=by
    rw [hcut]
    exact HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
  have Hmass' : partitionPoint 0 (finiteCutMasses us j) mid.length ≤ Cmass*W n:=by
    rw [hindex]
    exact Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
  exact hj mid tail hcut hindex Hmass' _ hs hU (radius n)
    Hrad Hrad1 HRU (by simpa only [hindex] using HRstar) Hrz
    (by simpa only [hindex] using HK)

end OAI.SKFluctuations.Cavity
