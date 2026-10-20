module

public import CavityWeightedExterior
public import CavityCenteringMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy

theorem finite_weighted_vector_even {A E : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w H : A → ℝ) (y : A → E) (hw : ∀ a, 0≤w a)
    (hmass : ∑ a, w a=1) (l : ℕ) :
    ‖∑ a, (w a*H a) • y a‖^(4*l)≤
      (∑ a, w a*|H a|^(4*l))*
        (∑ z : A×A, w z.1*w z.2*|inner ℝ (y z.1) (y z.2)|^(2*l)) := by
  have H4 := finite_weighted_vector_fourth w H y hw
  have Hpow := pow_le_pow_left₀ (by positivity) H4 l
  have JH := finite_weighted_mean_abs_pow_le w (fun a=>(H a)^2) hw hmass (2*l)
  have hpair : (∑ z : A×A, w z.1*w z.2)=1 := by
    simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,hmass,mul_one]
  have JR := finite_weighted_mean_abs_pow_le (fun z : A×A=>w z.1*w z.2)
    (fun z=>(inner ℝ (y z.1) (y z.2))^2)
    (fun z=>mul_nonneg (hw z.1) (hw z.2)) hpair l
  have hHn : 0≤∑ a, w a*(H a)^2 := Finset.sum_nonneg fun a _=>mul_nonneg (hw a) (sq_nonneg _)
  have hRn : 0≤∑ z : A×A, w z.1*w z.2*(inner ℝ (y z.1) (y z.2))^2 :=
    Finset.sum_nonneg fun z _=>mul_nonneg (mul_nonneg (hw z.1) (hw z.2)) (sq_nonneg _)
  simp only [abs_of_nonneg hHn,abs_pow,←pow_mul] at JH
  simp only [abs_of_nonneg hRn,abs_pow,←pow_mul] at JR
  have heH : 2*(2*l)=4*l := by omega
  rw [heH] at JH
  have hmul := mul_le_mul JH JR (pow_nonneg hRn l)
    (Finset.sum_nonneg fun a _=>mul_nonneg (hw a) (pow_nonneg (abs_nonneg _) _))
  simp only [mul_pow,←pow_mul] at Hpow
  exact Hpow.trans hmul

namespace ReplicaTree
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weighted_exterior_vector_even {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps)
    (H : T.Assignment → ℝ) (y : T.Assignment → E) (x : ι → ℝ) (l : ℕ) :
    ‖T.weightedExteriorVector w φ H y x‖^(4*l)≤
      T.expect w φ (fun σ=>|H σ|^(4*l)) x*
        (T.fork T).expect w φ (fun σ=>|inner ℝ (y σ.1) (y σ.2)|^(2*l)) x := by
  simpa only [weightedExteriorVector,expect,weight] using finite_weighted_vector_even
    (fun σ=>T.weight w φ σ x) H y (fun σ=>T.weight_nonneg hw φ ho σ x)
    (T.weight_sum hw φ ho x) l

end ReplicaTree
end OAI.SKFluctuations.Hierarchy
