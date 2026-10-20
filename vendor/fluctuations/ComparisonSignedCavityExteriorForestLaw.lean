module

public import ComparisonSignedCavityExteriorForest

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def exteriorForestTree (pre mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail) : ReplicaTree ι S (pre++(mid++tail)) :=
  prependReplicaTree pre (Ei.fork (prependReplicaTree mid (Es.fork D)))

def exteriorForestRead (pre mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) :
    (exteriorForestTree pre mid Ei Es D).Assignment→ℝ :=
  fun σ=>
    let z:=prependAssignmentEquiv pre (Ei.fork (prependReplicaTree mid (Es.fork D))) σ
    let u:=prependAssignmentEquiv mid (Es.fork D) z.2
    Q z.1 u.1 u.2

theorem exteriorForestTree_expect_eq_prefix (pre mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail) {a : ℝ} (ho : OrderedSteps a (pre++(mid++tail)))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (x : ι→ℝ) :
    (exteriorForestTree pre mid Ei Es D).expect w φ (exteriorForestRead pre mid Ei Es D Q) x =
      prefixTest pre (gaussianHierarchy w φ (mid++tail))
        (fun xi=>prefixTest mid (gaussianHierarchy w φ tail)
          (exteriorForestConditionalTest Ei Es D w φ Q xi) xi) x := by
  let T:=Ei.fork (prependReplicaTree mid (Es.fork D))
  let Q0 : T.Assignment→ℝ := fun z=>
    let u:=prependAssignmentEquiv mid (Es.fork D) z.2
    Q z.1 u.1 u.2
  have hcore : T.expect w φ Q0 =fun xi=>prefixTest mid (gaussianHierarchy w φ tail)
      (exteriorForestConditionalTest Ei Es D w φ Q xi) xi := by
    funext xi
    dsimp only [T,Q0]
    rw [ReplicaTree.expect_fork]
    have he (η : Ei.Assignment) := actual_prepend_expect hw φ mid (Es.fork D)
      (ho.suffix pre _) (fun σ=>Q η σ.1 σ.2) xi
    simp_rw [he]
    exact (prefixTest_exterior_sum_swap hw φ Ei Es D (ho.suffix pre _) Q xi).symm
  have hpre:=actual_prepend_expect hw φ pre T ho Q0 x
  change (prependReplicaTree pre T).expect w φ
    (fun σ=>Q0 (prependAssignmentEquiv pre T σ)) x = _
  rw [hpre,hcore]

theorem exteriorForestConditionalPrefix_smooth (mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail) {a : ℝ} (ho : OrderedSteps a (mid++tail))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (r : ℕ) :
    BddSmooth r (fun xi=>prefixTest mid (gaussianHierarchy w φ tail)
      (exteriorForestConditionalTest Ei Es D w φ Q xi) xi) := by
  have he : (exteriorForestTree [] mid Ei Es D).expect w φ (exteriorForestRead [] mid Ei Es D Q) =
      fun xi=>prefixTest mid (gaussianHierarchy w φ tail)
        (exteriorForestConditionalTest Ei Es D w φ Q xi) xi :=
    funext fun xi=>exteriorForestTree_expect_eq_prefix [] mid hw φ Ei Es D ho Q xi
  rw [←he]
  exact (exteriorForestTree [] mid Ei Es D).expect_smooth hw φ ho _ r

variable [MeasurableSpace S] [StandardBorelSpace S]

def exteriorForestRootLaw (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre mid tail : List (GaussianStep ι)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P→ι→ℝ) (hx : Measurable x) :
    Measure ((P×(ι→ℝ))×(ι→ℝ)) :=
  departedAnchorRootLaw w φ pre mid tail μ x hx

def exteriorForestIRoot {P : Type} : ((P×(ι→ℝ))×(ι→ℝ))→ι→ℝ :=
  departedAnchorTargetRoot

def exteriorForestStarRoot {P : Type} : ((P×(ι→ℝ))×(ι→ℝ))→ι→ℝ :=
  departedAnchorExteriorRoot

theorem exteriorForest_original_law_eq_conditional (pre mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail) {a : ℝ} (ho : OrderedSteps a (pre++(mid++tail)))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→ι→ℝ) (hx : Measurable x) :
    (∫ p,(exteriorForestTree pre mid Ei Es D).expect w φ
      (exteriorForestRead pre mid Ei Es D Q) (x p) ∂μ) =
    ∫ z,exteriorForestConditionalTest Ei Es D w φ Q
      (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂exteriorForestRootLaw w φ pre mid tail μ x hx := by
  let B := fun z : (ι→ℝ)×(ι→ℝ)=>exteriorForestConditionalTest Ei Es D w φ Q z.1 z.2
  have hB := exteriorForestConditionalTest_smooth_joint hw φ Ei Es D (ho.suffix pre _) Q 0
  obtain ⟨C,hC,hbound⟩ := hB.bound
  have hμ := retainedPrefixFieldLaw_finite hw φ pre (mid++tail) ho μ x hx
  have HB := integral_retainedPrefixFieldLaw hw φ mid tail (ho.suffix pre _)
    (retainedPrefixFieldLaw w φ pre (mid++tail) μ x hx) Prod.snd measurable_snd
    (fun z xs=>B (z.2,xs))
    (hB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z=>exteriorForestConditionalTest_smooth_star hw φ Ei Es D (ho.suffix pre _) Q z.2 0)
    C (fun z xs=>hbound _)
  have hA := exteriorForestConditionalPrefix_smooth mid hw φ Ei Es D (ho.suffix pre _) Q 0
  obtain ⟨C',hC',hbound'⟩ := hA.bound
  have HA := integral_retainedPrefixFieldLaw hw φ pre (mid++tail) ho μ x hx
    (fun _ xi=>prefixTest mid (gaussianHierarchy w φ tail)
      (exteriorForestConditionalTest Ei Es D w φ Q xi) xi)
    (hA.continuous.measurable.comp measurable_snd) (fun _=>hA)
    C' (fun _ xi=>hbound' xi)
  unfold exteriorForestRootLaw exteriorForestIRoot exteriorForestStarRoot
    departedAnchorRootLaw departedAnchorTargetRoot departedAnchorExteriorRoot
  rw [HB,HA]
  apply integral_congr_ae
  exact Eventually.of_forall fun p=>exteriorForestTree_expect_eq_prefix pre mid hw φ Ei Es D ho Q (x p)

def exteriorForestAveragedFourth {mid tail : List (GaussianStep ι)}
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  D.expect w φ (fun σ=>(exteriorForestMean Ei Es w φ (fun η ζ=>Q η ζ σ) xi xs)^4) xs

theorem exteriorForest_four_tooth_original_law (pre mid : List (GaussianStep ι))
    {tail : List (GaussianStep ι)} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ReplicaTree ι S (mid++tail))
    (Es D : ReplicaTree ι S tail) {a : ℝ} (ho : OrderedSteps a (pre++(mid++tail)))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→ι→ℝ) (hx : Measurable x) :
    (∫ p,(exteriorForestTree pre mid (exteriorQuad Ei) (exteriorQuad Es) D).expect w φ
      (exteriorForestRead pre mid (exteriorQuad Ei) (exteriorQuad Es) D
        (fun η ζ σ=>Q η.1.1 ζ.1.1 σ*Q η.1.2 ζ.1.2 σ*
          Q η.2.1 ζ.2.1 σ*Q η.2.2 ζ.2.2 σ)) (x p) ∂μ) =
    ∫ z,exteriorForestAveragedFourth Ei Es D w φ Q
      (exteriorForestIRoot z) (exteriorForestStarRoot z)
      ∂exteriorForestRootLaw w φ pre mid tail μ x hx := by
  rw [exteriorForest_original_law_eq_conditional pre mid hw φ
    (exteriorQuad Ei) (exteriorQuad Es) D ho _ μ x hx]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only [exteriorForestConditionalTest,exteriorForestAveragedFourth]
  apply congrArg (fun F : D.Assignment→ℝ=>D.expect w φ F (exteriorForestStarRoot z))
  funext σ
  exact exteriorForest_four_copy_mean Ei Es w φ (fun η ζ=>Q η ζ σ) _ _

end OAI.SKFluctuations.Cavity
