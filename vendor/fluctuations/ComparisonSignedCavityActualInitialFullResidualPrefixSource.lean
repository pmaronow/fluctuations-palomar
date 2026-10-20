module

public import ComparisonSignedCavityActualInitialTwoThermalModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_initial_full_residual_reindex
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as as' : List PositiveMass} {i i' star star' U depth : ℕ} {W : ℝ}
    (has : as'=as) (hindex : i'=i) (hstar : star'=star)
    (hs' : star'<U) (hs : star<U) (hU' : U ≤ as'.length) (hU : U ≤ as.length)
    (hi' : i' ≤ as'.length) (hi : i ≤ as.length) :
    nativeActualMinimumFourResidualSum M hs' hU' W depth
        [nativeActualInitialState as' i' star' 0 hi']=
      nativeActualMinimumFourResidualSum M hs hU W depth
        [nativeActualInitialState as i star 0 hi] := by
  subst as'
  subst i'
  subst star'
  rfl

theorem native_actual_initial_retained_target_prefix_split
    (as : List PositiveMass) (i star : ℕ) (hi : i < star) (hs : star ≤ as.length) :
    ∃pre mid tail : List PositiveMass,pre++(mid++tail)=as ∧ pre.length=i ∧
      pre.length+mid.length=star ∧ 0 < mid.length := by
  let pre:=as.take i
  let mid:=(as.drop i).take (star-i)
  let tail:=as.drop star
  have hilen:i ≤ as.length:=hi.le.trans hs
  have hpre:pre.length=i:=List.length_take_of_le hilen
  have hjoin:pre++mid=as.take star := by
    dsimp only [pre,mid]
    rw [←List.take_add]
    congr 1
    omega
  have hparts:pre++(mid++tail)=as := by
    rw [←List.append_assoc,hjoin]
    exact List.take_append_drop star as
  have hindex:pre.length+mid.length=star := by
    have HH:=congrArg List.length hjoin
    simpa only [List.length_append,List.length_take_of_le hs] using HH
  exact ⟨pre,mid,tail,hparts,hpre,hindex,by omega⟩

def ActualInitialResidualFullModulusOnStrongCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]| ≤ Ci*(M n).xs^2*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3

end OAI.SKFluctuations.Cavity
