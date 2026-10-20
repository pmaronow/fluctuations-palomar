module

public import ComparisonSignedCavityActualSquareConstantPairAlong
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualInheritedSquareResourceAlong

@[expose] public section
set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum

def ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
      let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k T P→k≤ degree→
        ∀x a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        P.PairMomentBudget (fullWeight (dim n)) (fullFeature (dim n)) 0
          (finitePhysicalCavitySquareVariance (dim n) U as b h a t)
          (fun σ τ=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter (dim n) (M n).sweepBf (M n).sweepHf as) 0
          A x (W n) (((dim n+1:ℕ):ℝ)^(-saving))

theorem actual_square_constant_resource_pair_budget_of_actual_star_producer_along_original_q
    (degree : ℕ) (hd : 0 < degree)
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualOriginalSquareStarMomentOnEveryFinalNetAlong_original_q (degree-1) saving M W w) :
    ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_original_q degree 1 saving M W w := by
  filter_upwards [Hstar] with n hsn
  intro us hus hstar
  filter_upwards [hsn us hus hstar] with j hsj
  dsimp only at hsj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).sweepBf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).sweepHf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let center:=nativePhysicalResourceCenter (dim n) (M n).sweepBf (M n).sweepHf as
  let ε:=((dim n+1:ℕ):ℝ)^(-saving)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have heps : 0 < ε := by dsimp only [ε];positivity
  have hNode : partitionPoint 0 as star=(w n).star.val :=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have hCenterStar : center star=orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val := by
    dsimp only [center]
    rw [native_physical_resource_center_at_positive_cut (dim n) (M n).sweepBf (M n).sweepHf
      ((M n).sweep_bf_monotone) ((M n).sweep_hf_monotone) as ho star
      (by rw [hNode];exact (w n).star.property),hNode]
  intro U i k T P hP hdegree x a t ha ht
  let q:=finitePhysicalCavitySquareVariance (dim n) U as b h a t
  let R:=fun σ τ : Spin (dim n)×Bool=>deletedOverlap (dim n) (joinSpin σ) (joinSpin τ)
  apply hP.pairMomentBudget_of_constant_star_bounds degree hdegree (fullWeight (dim n)) (fullFeature (dim n))
    0 q R center 0 1 x (W n) ε
  intro l hl hlD
  let V:=ClockTree.pairClock (S:=Spin (dim n)×Bool) as star
  let F:=fun σ : V.Assignment=>R (ClockTree.pairSpin as star σ).1
    (ClockTree.pairSpin as star σ).2-center star
  have horder : degree-1+1=degree := by omega
  have Hstar' := hsj U a t ha ht
  simp only [horder] at Hstar'
  have HH : V.disorderExpect (fullWeight (dim n)) (fullFeature (dim n)) 0 q
      (fun σ=>|F σ|^(2*degree)) 0≤(ε*W n)^(2*degree) := by
    change nativeOriginalSquareCenteredMoment (dim n) degree U as b h star (center star) a t≤_
    rw [hCenterStar]
    exact Hstar'
  have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos (dim n)) (fullFeature (dim n)) ho 0 q 0 F
    (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*l by omega))
    (by exact_mod_cast (show 2*l≤2*degree by omega)) (by positivity : 0≤ε*W n)
    (by simpa only [Real.rpow_natCast] using HH)
  simpa only [Real.rpow_natCast,V,F,one_mul] using Hlow

end OAI.SKFluctuations.LaplaceWindowFormalization
