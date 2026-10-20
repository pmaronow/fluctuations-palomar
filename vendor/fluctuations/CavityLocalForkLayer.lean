module

public import CavityCutLayerRecursion
public import CavityPrefixCauchy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def actualForkResamplingSquare {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : T.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  (T.fork T).expect w φ (fun σ => (P σ.1-P σ.2)^2) x

def actualSingleResamplingSquare (steps : List (GaussianStep ι))
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (F : S → ℝ) (x : ι → ℝ) : ℝ :=
  actualForkResamplingSquare (ReplicaTree.single steps) w φ
    (fun σ => F (ReplicaTree.singleEquiv (S := S) steps σ)) x

theorem actual_boundary_radius_sq_eq_resampling {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ho : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    (actualBoundaryCovarianceRadius T w φ P F x)^2 =
      actualForkResamplingSquare T w φ P x *
        actualSingleResamplingSquare steps w φ F x / 4 := by
  have hp := actual_fork_resampling_eq_twice_variance hw φ T ho P x
  have hf := actual_fork_resampling_eq_twice_variance hw φ
    (ReplicaTree.single steps) ho
    (fun σ => F (ReplicaTree.singleEquiv (S := S) steps σ)) x
  rw [ReplicaTree.single_expect hw φ steps ho F x] at hf
  rw [ReplicaTree.single_expect hw φ steps ho
    (fun σ => (F σ-gaussianHierarchyMean w φ F steps x)^2) x] at hf
  unfold actualBoundaryCovarianceRadius
  rw [Real.sq_sqrt (mul_nonneg (T.expect_nonneg hw φ ho (fun _ => sq_nonneg _) x)
    (gaussianHierarchyMean_nonneg hw φ (fun _ => sq_nonneg _) steps ho x))]
  change _ = (T.fork T).expect w φ (fun σ => (P σ.1-P σ.2)^2) x *
    ((ReplicaTree.single steps).fork (ReplicaTree.single steps)).expect w φ
      (fun σ => (F (ReplicaTree.singleEquiv (S := S) steps σ.1)-
        F (ReplicaTree.singleEquiv (S := S) steps σ.2))^2) x / 4
  rw [hp, hf]
  ring

theorem actual_cut_layer_resampling_sq_le {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a v z : ℝ} (ho : OrderedSteps a steps) (hav : a ≤ v)
    (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    (actualCutRow T w φ a z P F x-actualCutRow T w φ a v P F x)^2 ≤
      (3*(T.leaves:ℝ)*v)^2*actualForkResamplingSquare T w φ P x *
        actualSingleResamplingSquare steps w φ F x := by
  have hl := actual_cut_layer_abs_le hw φ T ho hav hvz hz P F x
  have hv : 0 ≤ v := ho.nonneg.trans hav
  have hrad : 0 ≤ actualBoundaryCovarianceRadius T w φ P F x := Real.sqrt_nonneg _
  have hs : (actualCutRow T w φ a z P F x-actualCutRow T w φ a v P F x)^2 ≤
      (6*(T.leaves:ℝ)*v*actualBoundaryCovarianceRadius T w φ P F x)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
      (by positivity : 0 ≤ 6*(T.leaves:ℝ)*v) hrad)).mpr hl
  rw [mul_pow, actual_boundary_radius_sq_eq_resampling hw φ T ho P F x] at hs
  convert hs using 1
  ring

theorem actual_prefix_cut_layer_resampling_sq_le {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a v z : ℝ} (ho : OrderedSteps a steps) (hav : a ≤ v)
    (hvz : v ≤ z) (hz : z ≤ 2*v)
    (pre : List (GaussianStep ι)) (hp : ∀ st ∈ pre, 0 < st.1)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    (prefixTest pre (gaussianHierarchy w φ steps)
      (fun y => actualCutRow T w φ a z P F y-actualCutRow T w φ a v P F y) x)^2 ≤
    (3*(T.leaves:ℝ)*v)^2 *
      prefixTest pre (gaussianHierarchy w φ steps)
        (actualForkResamplingSquare T w φ P) x *
      prefixTest pre (gaussianHierarchy w φ steps)
        (actualSingleResamplingSquare steps w φ F) x := by
  obtain ⟨L, hL⟩ := gaussianHierarchy_lipschitz hw φ steps ho
  apply actual_prefix_gram_sq_le hL
    ((T.fork T).expect_smooth hw φ ho _ 0)
    (((ReplicaTree.single steps).fork (ReplicaTree.single steps)).expect_smooth hw φ ho _ 0)
    ((actualCutRow_smooth hw φ T ho z P F 0).sub
      (actualCutRow_smooth hw φ T ho v P F 0))
  · intro y
    exact (T.fork T).expect_nonneg hw φ ho (fun _ => sq_nonneg _) y
  · intro y
    exact ((ReplicaTree.single steps).fork (ReplicaTree.single steps)).expect_nonneg
      hw φ ho (fun _ => sq_nonneg _) y
  · intro y
    exact actual_cut_layer_resampling_sq_le hw φ T ho hav hvz hz P F y
  · exact hp

end OAI.SKFluctuations.Cavity
