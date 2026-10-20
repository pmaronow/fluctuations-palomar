module

public import ComparisonSignedCavityDepartedAnchorLaw
public import ComparisonSignedCavityActualGroupedLayers

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def exteriorQuad {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) :
    ReplicaTree ι S steps := (T.fork T).fork (T.fork T)

omit [Nonempty S] in
theorem exteriorQuad_expect_product {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (A B C D : T.Assignment→ℝ) (x : ι→ℝ) :
    (exteriorQuad T).expect w φ
      (fun σ=>A σ.1.1*B σ.1.2*C σ.2.1*D σ.2.2) x =
      T.expect w φ A x*T.expect w φ B x*T.expect w φ C x*T.expect w φ D x := by
  unfold exteriorQuad
  have hf : (fun σ : ((T.fork T).fork (T.fork T)).Assignment=>
      A σ.1.1*B σ.1.2*C σ.2.1*D σ.2.2) =
      fun σ=>(A σ.1.1*B σ.1.2)*(C σ.2.1*D σ.2.2) := by
    funext σ;ring
  rw [hf]
  calc
    _ = (T.fork T).expect w φ (fun η=>A η.1*B η.2) x*
        (T.fork T).expect w φ (fun η=>C η.1*D η.2) x :=
      ReplicaTree.expect_fork_product w φ (T.fork T) (T.fork T) _ _ x
    _ = _ := by
      rw [ReplicaTree.expect_fork_product,ReplicaTree.expect_fork_product]
      ring

def exteriorForestMean {mid tail : List (GaussianStep ι)}
    (Ei : ReplicaTree ι S (mid++tail)) (Es : ReplicaTree ι S tail)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Q : Ei.Assignment→Es.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  Ei.expect w φ (fun η=>Es.expect w φ (Q η) xs) xi

def exteriorForestConditionalTest {mid tail : List (GaussianStep ι)}
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  D.expect w φ (fun σ=>exteriorForestMean Ei Es w φ (fun η ζ=>Q η ζ σ) xi xs) xs

omit [Nonempty S] in
theorem exteriorForestConditionalTest_eq_joint {mid tail : List (GaussianStep ι)}
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) :
    exteriorForestConditionalTest Ei Es D w φ Q xi xs =
      Ei.expect w φ (fun η=>(Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2) xs) xi := by
  unfold exteriorForestConditionalTest exteriorForestMean
  simp only [ReplicaTree.expect,ReplicaTree.weight,Fintype.sum_prod_type,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ζ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [Nonempty S] in
theorem exteriorForest_four_copy_mean {mid tail : List (GaussianStep ι)}
    (Ei : ReplicaTree ι S (mid++tail)) (Es : ReplicaTree ι S tail)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Q : Ei.Assignment→Es.Assignment→ℝ) (xi xs : ι→ℝ) :
    exteriorForestMean (exteriorQuad Ei) (exteriorQuad Es) w φ
      (fun η ζ=>Q η.1.1 ζ.1.1*Q η.1.2 ζ.1.2*Q η.2.1 ζ.2.1*Q η.2.2 ζ.2.2) xi xs =
      (exteriorForestMean Ei Es w φ Q xi xs)^4 := by
  unfold exteriorForestMean
  simp_rw [exteriorQuad_expect_product]
  calc
    _ = (Ei.expect w φ (fun η=>Es.expect w φ (Q η) xs) xi)*
        (Ei.expect w φ (fun η=>Es.expect w φ (Q η) xs) xi)*
        (Ei.expect w φ (fun η=>Es.expect w φ (Q η) xs) xi)*
        (Ei.expect w φ (fun η=>Es.expect w φ (Q η) xs) xi) :=
      exteriorQuad_expect_product Ei w φ _ _ _ _ xi
    _ = _ := by ring

theorem exteriorForestConditionalTest_smooth_joint {mid tail : List (GaussianStep ι)}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    {a : ℝ} (ho : OrderedSteps a (mid++tail))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (r : ℕ) :
    BddSmooth r (fun z : (ι→ℝ)×(ι→ℝ)=>
      exteriorForestConditionalTest Ei Es D w φ Q z.1 z.2) := by
  simp_rw [exteriorForestConditionalTest_eq_joint]
  unfold ReplicaTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply BddSmooth.mul
  · exact (Ei.weight_smooth hw φ ho r η).compCLM
      (ContinuousLinearMap.fst ℝ (ι→ℝ) (ι→ℝ))
  · exact ((Es.fork D).expect_smooth hw φ (ho.suffix mid _) (fun σ=>Q η σ.1 σ.2) r).compCLM
      (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ))

theorem exteriorForestConditionalTest_smooth_star {mid tail : List (GaussianStep ι)}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    {a : ℝ} (ho : OrderedSteps a (mid++tail))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi : ι→ℝ) (r : ℕ) :
    BddSmooth r (exteriorForestConditionalTest Ei Es D w φ Q xi) := by
  have he : exteriorForestConditionalTest Ei Es D w φ Q xi =
      fun xs=>Ei.expect w φ (fun η=>(Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2) xs) xi :=
    funext fun xs=>exteriorForestConditionalTest_eq_joint Ei Es D w φ Q xi xs
  rw [he]
  unfold ReplicaTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  exact ((Es.fork D).expect_smooth hw φ (ho.suffix mid _) (fun σ=>Q η σ.1 σ.2) r).const_mul
    (Ei.weight w φ η xi)

theorem prefixTest_fintype_sum {κ : Type} [Fintype κ]
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (pre tail : List (GaussianStep ι)) {a : ℝ} (ho : OrderedSteps a (pre++tail))
    (B : κ→(ι→ℝ)→ℝ) (hB : ∀ k,BddSmooth 0 (B k)) (x : ι→ℝ) :
    prefixTest pre (gaussianHierarchy w φ tail) (fun y=>∑ k,B k y) x =
      ∑ k,prefixTest pre (gaussianHierarchy w φ tail) (B k) x := by
  induction pre generalizing a x with
  | nil => rfl
  | cons st pre ih =>
    have he : prefixTest pre (gaussianHierarchy w φ tail) (fun y=>∑ k,B k y) =
        fun y=>∑ k,prefixTest pre (gaussianHierarchy w φ tail) (B k) y :=
      funext fun y=>ih ho.2.2.2 y
    change shiftedMean _ st.1 (prefixContinuation pre (gaussianHierarchy w φ tail))
      (prefixTest pre (gaussianHierarchy w φ tail) (fun y=>∑ k,B k y)) x = _
    rw [he,prefixContinuation_hierarchy]
    have ht := ho.2.2.2.suffix pre tail
    obtain ⟨L,hL⟩ := gaussianHierarchy_lipschitz hw φ tail ht
    have hpre : ∀ s∈pre,0<s.1 := fun s hs=>ho.2.2.2.mem_pos s (List.mem_append_left tail hs)
    simpa only [prefixTest,prefixContinuation_hierarchy] using
      shiftedMean_sum (fun k=>prefixTest_smooth0 hL (hB k) pre hpre)
        (gaussianHierarchy_integrable hw φ (pre++tail) ho.2.2.2 st.1 st.2 x)

theorem prefixTest_scalar_mul (pre : List (GaussianStep ι))
    (F B : (ι→ℝ)→ℝ) (c : ℝ) (x : ι→ℝ) :
    prefixTest pre F (fun y=>c*B y) x=c*prefixTest pre F B x := by
  induction pre generalizing x with
  | nil => rfl
  | cons st pre ih =>
    have he : prefixTest pre F (fun y=>c*B y)=fun y=>c*prefixTest pre F B y :=
      funext fun y=>ih y
    simp only [prefixTest]
    rw [he,shiftedMean_const_mul]

theorem prefixTest_exterior_sum_swap {mid tail : List (GaussianStep ι)}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ReplicaTree ι S (mid++tail)) (Es D : ReplicaTree ι S tail)
    {a : ℝ} (ho : OrderedSteps a (mid++tail))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi : ι→ℝ) :
    prefixTest mid (gaussianHierarchy w φ tail)
      (exteriorForestConditionalTest Ei Es D w φ Q xi) xi =
      Ei.expect w φ (fun η=>prefixTest mid (gaussianHierarchy w φ tail)
        ((Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2)) xi) xi := by
  have he : exteriorForestConditionalTest Ei Es D w φ Q xi =
      fun xs=>Ei.expect w φ (fun η=>(Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2) xs) xi :=
    funext fun xs=>exteriorForestConditionalTest_eq_joint Ei Es D w φ Q xi xs
  rw [he]
  change prefixTest mid (gaussianHierarchy w φ tail)
    (fun y=>∑ η,Ei.weight w φ η xi*(Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2) y) xi =
    ∑ η,Ei.weight w φ η xi*prefixTest mid (gaussianHierarchy w φ tail)
      ((Es.fork D).expect w φ (fun σ=>Q η σ.1 σ.2)) xi
  rw [prefixTest_fintype_sum hw φ mid tail ho _ (fun η=>
    ((Es.fork D).expect_smooth hw φ (ho.suffix mid _) (fun σ=>Q η σ.1 σ.2) 0).const_mul
      (Ei.weight w φ η xi)) xi]
  apply Finset.sum_congr rfl
  intro η _
  exact prefixTest_scalar_mul mid _ _ _ xi

end OAI.SKFluctuations.Cavity
