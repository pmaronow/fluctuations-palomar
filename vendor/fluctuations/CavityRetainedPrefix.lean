module

public import CavityLocalForkLayer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

def prependReplicaTree (pre : List (GaussianStep ι)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) : ReplicaTree ι S (pre ++ steps) :=
  match pre with
  | [] => T
  | st :: pre => (prependReplicaTree pre T).step st

def prependAssignmentEquiv (pre : List (GaussianStep ι)) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) : (prependReplicaTree pre T).Assignment ≃ T.Assignment :=
  match pre with
  | [] => Equiv.refl _
  | _ :: pre => prependAssignmentEquiv pre T

def prefixEndMass (a : ℝ) : List (GaussianStep ι) → ℝ
  | [] => a
  | st :: pre => prefixEndMass st.1 pre

theorem prefixEndMass_ordered {a : ℝ} (pre steps : List (GaussianStep ι))
    (ho : OrderedSteps a (pre ++ steps)) :
    OrderedSteps (prefixEndMass a pre) steps := by
  induction pre generalizing a with
  | nil => exact ho
  | cons st pre ih => exact ih ho.2.2.2

theorem prefixEndMass_le {a v : ℝ} (pre : List (GaussianStep ι))
    (hav : a ≤ v) (hp : ∀ st ∈ pre, st.1 ≤ v) : prefixEndMass a pre ≤ v := by
  induction pre generalizing a with
  | nil => exact hav
  | cons st pre ih =>
    exact ih (hp st List.mem_cons_self) (fun st hst => hp st (List.mem_cons_of_mem _ hst))

theorem actual_retained_prefix_cut_layer {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (pre : List (GaussianStep ι)) {a v z : ℝ}
    (ho : OrderedSteps a (pre ++ steps)) (hp : ∀ st ∈ pre, st.1 ≤ v)
    (hvz : v ≤ z) (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    actualCutRow (prependReplicaTree pre T) w φ a z
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x-
      actualCutRow (prependReplicaTree pre T) w φ a v
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x =
    prefixTest pre (gaussianHierarchy w φ steps)
      (fun y => actualCutRow T w φ (prefixEndMass a pre) z P F y-
        actualCutRow T w φ (prefixEndMass a pre) v P F y) x := by
  induction pre generalizing a x with
  | nil => rfl
  | cons st pre ih =>
    have hp' : ∀ r ∈ pre, r.1 ≤ v := fun r hr => hp r (List.mem_cons_of_mem _ hr)
    have hi : (fun y => actualCutRow (prependReplicaTree pre T) w φ st.1 z
        (fun σ => P (prependAssignmentEquiv pre T σ)) F y-
      actualCutRow (prependReplicaTree pre T) w φ st.1 v
        (fun σ => P (prependAssignmentEquiv pre T σ)) F y) =
        prefixTest pre (gaussianHierarchy w φ steps)
          (fun y => actualCutRow T w φ (prefixEndMass st.1 pre) z P F y-
            actualCutRow T w φ (prefixEndMass st.1 pre) v P F y) := by
      funext y
      exact ih ho.2.2.2 hp' y
    change actualCutRow ((prependReplicaTree pre T).step st) w φ a z
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x-
      actualCutRow ((prependReplicaTree pre T).step st) w φ a v
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x = _
    rw [actual_cut_layer_shared_step hw φ (prependReplicaTree pre T) st.1 st.2 ho
      (hp st List.mem_cons_self) hvz, hi]
    simp only [prefixTest, prefixEndMass]
    rw [prefixContinuation_hierarchy]

theorem actual_retained_prefix_cut_layer_sq_le {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (pre : List (GaussianStep ι)) {a v z : ℝ}
    (ho : OrderedSteps a (pre ++ steps)) (hp : ∀ st ∈ pre, st.1 ≤ v)
    (hav : a ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    (actualCutRow (prependReplicaTree pre T) w φ a z
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x-
      actualCutRow (prependReplicaTree pre T) w φ a v
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x)^2 ≤
      (3*(T.leaves:ℝ)*v)^2 *
        prefixTest pre (gaussianHierarchy w φ steps)
          (actualForkResamplingSquare T w φ P) x *
        prefixTest pre (gaussianHierarchy w φ steps)
          (actualSingleResamplingSquare steps w φ F) x := by
  rw [actual_retained_prefix_cut_layer hw φ T pre ho hp hvz P F x]
  exact actual_prefix_cut_layer_resampling_sq_le hw φ T (prefixEndMass_ordered pre steps ho)
    (prefixEndMass_le pre hav hp) hvz hz pre
    (fun st hst => ho.mem_pos st (List.mem_append_left steps hst)) P F x

theorem actual_retained_prefix_cut_layer_abs_le {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (pre : List (GaussianStep ι)) {a v z : ℝ}
    (ho : OrderedSteps a (pre ++ steps)) (hp : ∀ st ∈ pre, st.1 ≤ v)
    (hav : a ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ)
    {MP MF : ℝ} (hMP : 0 ≤ MP) (hMF : 0 ≤ MF)
    (hP : prefixTest pre (gaussianHierarchy w φ steps)
      (actualForkResamplingSquare T w φ P) x ≤ MP^2)
    (hF : prefixTest pre (gaussianHierarchy w φ steps)
      (actualSingleResamplingSquare steps w φ F) x ≤ MF^2) :
    |actualCutRow (prependReplicaTree pre T) w φ a z
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x-
      actualCutRow (prependReplicaTree pre T) w φ a v
        (fun σ => P (prependAssignmentEquiv pre T σ)) F x| ≤
      3*(T.leaves:ℝ)*v*MP*MF := by
  have hs := actual_retained_prefix_cut_layer_sq_le hw φ T pre ho hp hav hvz hz P F x
  have htail := prefixEndMass_ordered pre steps ho
  obtain ⟨L, hL⟩ := gaussianHierarchy_lipschitz hw φ steps htail
  have hpos : ∀ st ∈ pre, 0 < st.1 := fun st hst => ho.mem_pos st (List.mem_append_left steps hst)
  have hBn : 0 ≤ prefixTest pre (gaussianHierarchy w φ steps)
      (actualSingleResamplingSquare steps w φ F) x := prefixTest_nonneg hL
    (fun y => ((ReplicaTree.single steps).fork (ReplicaTree.single steps)).expect_nonneg
      hw φ htail (fun _ => sq_nonneg _) y) pre hpos x
  have hprod := mul_le_mul hP hF hBn (sq_nonneg MP)
  have hv : 0 ≤ v := ho.nonneg.trans hav
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3*(T.leaves:ℝ)*v*MP*MF)).mp
  rw [sq_abs]
  calc
    _ ≤ _ := hs
    _ ≤ (3*(T.leaves:ℝ)*v)^2*(MP^2*MF^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = _ := by ring

end OAI.SKFluctuations.Cavity
