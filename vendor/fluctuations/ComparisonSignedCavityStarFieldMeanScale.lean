module

public import ComparisonSignedCavityStarFieldJointClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_star_field_test_mean_const_mul
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (c : ℝ) (J : (ι→ℝ)→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeStarFieldTestMean w φ T s star q (fun y σ=>c*J y σ) x=
      c*nativeStarFieldTestMean w φ T s star q J x := by
  induction T generalizing star q x with
  | leaf=>simp only [nativeStarFieldTestMean,expect,Finset.mul_sum,mul_left_comm]
  | step b T ih=>
    cases star with
    | zero=>simp only [nativeStarFieldTestMean,expect,Finset.mul_sum,mul_left_comm]
    | succ star=>
      change shiftedMean _ _ _ _ x=c*shiftedMean _ _ _ _ x
      have H : nativeStarFieldTestMean w φ T s star (fun j=>q (j+1)) (fun y σ=>c*J y σ)=
          fun y=>c*nativeStarFieldTestMean w φ T s star (fun j=>q (j+1)) J y := by
        funext y
        exact ih s star _ J y
      rw [H,shiftedMean_const_mul]
  | fork T V ihT ihV=>
    cases star with
    | zero=>simp only [nativeStarFieldTestMean,expect,Finset.mul_sum,mul_left_comm]
    | succ star=>
      cases s with
      | inl s=>
        change (∑τ,V.weight w φ q τ x*_) = c*(∑τ,V.weight w φ q τ x*_)
        simp_rw [ihT s (star+1) q (fun y σ=>J y (σ,_)) x]
        simp only [Finset.mul_sum,mul_left_comm]
      | inr s=>
        change (∑σ,T.weight w φ q σ x*_) = c*(∑σ,T.weight w φ q σ x*_)
        simp_rw [ihV s (star+1) q (fun y τ=>J y (_,τ)) x]
        simp only [Finset.mul_sum,mul_left_comm]

omit [Nonempty S] in
theorem native_star_field_disorder_mean_const_mul
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (c : ℝ) (J : (ι→ℝ)→T.Assignment→ℝ) (x : ι→ℝ) :
    nativeStarFieldDisorderMean w φ T s star v q (fun y σ=>c*J y σ) x=
      c*nativeStarFieldDisorderMean w φ T s star v q J x := by
  unfold nativeStarFieldDisorderMean
  simp_rw [native_star_field_test_mean_const_mul]
  exact integral_const_mul c _

end OAI.SKFluctuations.Hierarchy.ClockTree
