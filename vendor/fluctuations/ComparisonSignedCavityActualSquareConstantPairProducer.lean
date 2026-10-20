module

public import ComparisonSignedCavityActualSquareResourcePairProducer

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Fintype ι]
variable {as : List PositiveMass}

theorem NativeActualResourceGenerated.pairMomentBudget_of_constant_star_bounds
    {i star U k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [] k T P)
    (degree : ℕ) (hd : k≤degree)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hStar : ∀l : ℕ,0 < l → l≤degree →
      (pairClock (S:=S) as star).disorderExpect w φ v q
        (fun σ=>|R (pairSpin as star σ).1 (pairSpin as star σ).2-C star|^(2*l)) x₀≤
          (A*(ε*W))^(2*l)) :
    P.PairMomentBudget w φ v q R C x₀ A x W ε := by
  refine P.pairMomentBudget_of_canonical_bounds degree ?_ w φ v q R C x₀ A x W ε ?_
  · rw [hP.total_factor_depth]
    simpa only [List.length_nil,zero_add] using hd
  · intro m hm l hl hlD
    rw [hP.resource_word,List.nil_append] at hm
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
    exact hStar l hl hlD

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualSquareConstantResourcePairBudgetOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
      let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
      ∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k T P→k≤degree→
        ∀x a t : ℝ,a∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as b h a t)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n (M n).bf (M n).hf as) 0
          A x (W n) (((n+1:ℕ):ℝ)^(-saving))

theorem actual_square_constant_resource_pair_budget_of_actual_star_producer
    (degree : ℕ) (hd : 0 < degree)
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n)
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ActualOriginalSquareStarMomentOnEveryFinalNet (degree-1) saving M W w) :
    ActualSquareConstantResourcePairBudgetOnEveryFinalNet degree 1 saving M W w := by
  filter_upwards [Hstar] with n hsn
  intro us hus hstar
  filter_upwards [hsn us hus hstar] with j hsj
  dsimp only at hsj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun k=>((M n).bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>((M n).hf (partitionPoint 0 as k):ℝ)
  let ho:=finiteCutMasses_ordered us hus j
  let center:=nativePhysicalResourceCenter n (M n).bf (M n).hf as
  let ε:=((n+1:ℕ):ℝ)^(-saving)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have heps : 0 < ε := by dsimp only [ε];positivity
  have hNode : partitionPoint 0 as star=(w n).star.val :=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hCenterStar : center star=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val := by
    dsimp only [center]
    rw [native_physical_resource_center_at_positive_cut n (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho star
      (by rw [hNode];exact (w n).star.property),hNode]
  intro U i k T P hP hdegree x a t ha ht
  let q:=finitePhysicalCavitySquareVariance n U as b h a t
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  apply hP.pairMomentBudget_of_constant_star_bounds degree hdegree (fullWeight n) (fullFeature n)
    0 q R center 0 1 x (W n) ε
  intro l hl hlD
  let V:=ClockTree.pairClock (S:=Spin n×Bool) as star
  let F:=fun σ : V.Assignment=>R (ClockTree.pairSpin as star σ).1
    (ClockTree.pairSpin as star σ).2-center star
  have horder : degree-1+1=degree := by omega
  have Hstar' := hsj U a t ha ht
  simp only [horder] at Hstar'
  have HH : V.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|F σ|^(2*degree)) 0≤(ε*W n)^(2*degree) := by
    change nativeOriginalSquareCenteredMoment n degree U as b h star (center star) a t≤_
    rw [hCenterStar]
    exact Hstar'
  have Hlow:=V.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 q 0 F
    (p:=(2*l:ℕ)) (r:=(2*degree:ℕ)) (by exact_mod_cast (show 0<2*l by omega))
    (by exact_mod_cast (show 2*l≤2*degree by omega)) (by positivity : 0≤ε*W n)
    (by simpa only [Real.rpow_natCast] using HH)
  simpa only [Real.rpow_natCast,V,F,one_mul] using Hlow

end OAI.SKFluctuations.LaplaceWindowFormalization
