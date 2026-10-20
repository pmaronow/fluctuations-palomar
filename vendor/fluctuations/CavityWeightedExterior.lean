module

public import CavityMomentAllocation
public import CavityPhysicalFreshTooth

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy

theorem finite_weighted_vector_fourth {A E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w H : A → ℝ) (y : A → E) (hw : ∀ a, 0≤w a) :
    ‖∑ a, (w a*H a) • y a‖^4≤
      (∑ a, w a*(H a)^2)^2*
        (∑ z : A×A, w z.1*w z.2*(inner ℝ (y z.1) (y z.2))^2) := by
  let V := ∑ a, (w a*H a) • y a
  have he : ‖V‖^2=∑ z : A×A, (w z.1*w z.2)*(H z.1*H z.2)*inner ℝ (y z.1) (y z.2) := by
    rw [←real_inner_self_eq_norm_sq]
    dsimp only [V]
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [real_inner_comm (y b) (y a)]
    ring
  have Hcs := finite_weighted_cauchy_schwarz
    (fun z : A×A=>w z.1*w z.2) (fun z=>H z.1*H z.2)
    (fun z=>inner ℝ (y z.1) (y z.2)) (fun z=>mul_nonneg (hw z.1) (hw z.2))
  rw [←he] at Hcs
  have hs : (∑ z : A×A, (w z.1*w z.2)*(H z.1*H z.2)^2)=(∑ a, w a*(H a)^2)^2 := by
    simp only [Fintype.sum_prod_type,pow_two,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs,←pow_mul] at Hcs
  exact Hcs

namespace ReplicaTree
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def weightedExteriorVector {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (H : T.Assignment → ℝ) (y : T.Assignment → E) (x : ι → ℝ) : E :=
  ∑ σ, (T.weight w φ σ x*H σ) • y σ

theorem weighted_exterior_vector_fourth {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (H : T.Assignment → ℝ) (y : T.Assignment → E) (x : ι → ℝ) :
    ‖T.weightedExteriorVector w φ H y x‖^4≤
      (T.expect w φ (fun σ=>(H σ)^2) x)^2*
        (T.fork T).expect w φ (fun σ=>(inner ℝ (y σ.1) (y σ.2))^2) x := by
  simpa only [weightedExteriorVector,expect,weight] using finite_weighted_vector_fourth
    (fun σ=>T.weight w φ σ x) H y (fun σ=>T.weight_nonneg hw φ ho σ x)

theorem weighted_exterior_average (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (H : T.Assignment → ℝ) (y : T.Assignment → E)
    (Z : U.Assignment → ℝ) (d : U.Assignment → E) (x : ι → ℝ) :
    (T.fork U).expect w φ
      (fun σ=>Z σ.2*H σ.1*inner ℝ (d σ.2) (y σ.1)) x=
    U.expect w φ (fun σ=>Z σ*inner ℝ (d σ) (T.weightedExteriorVector w φ H y x)) x := by
  unfold expect weightedExteriorVector
  simp only [weight,Fintype.sum_prod_type,inner_sum,real_inner_smul_right,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

end ReplicaTree
end OAI.SKFluctuations.Hierarchy
