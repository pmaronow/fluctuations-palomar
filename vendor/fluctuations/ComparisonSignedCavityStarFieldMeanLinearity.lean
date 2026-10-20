module

public import ComparisonSignedCavityStarFieldMeanRegularity

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_field_test_mean_sub
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (J K : (ι→ℝ)→T.Assignment→ℝ)
    (hJ : ∀σ,BddSmooth 0 (fun y=>J y σ))
    (hK : ∀σ,BddSmooth 0 (fun y=>K y σ)) (x : ι→ℝ) :
    nativeStarFieldTestMean w φ T s star q (fun y σ=>J y σ-K y σ) x=
    nativeStarFieldTestMean w φ T s star q J x-nativeStarFieldTestMean w φ T s star q K x := by
  induction T generalizing a star q x with
  | leaf=>simp [nativeStarFieldTestMean,expect,mul_sub,Finset.sum_sub_distrib]
  | step b T ih=>
    cases star with
    | zero=>simp [nativeStarFieldTestMean,expect,mul_sub,Finset.sum_sub_distrib]
    | succ star=>
      change shiftedMean _ _ _ _ x=shiftedMean _ _ _ _ x-shiftedMean _ _ _ _ x
      have HH : nativeStarFieldTestMean w φ T s star (fun j=>q (j+1))
          (fun y σ=>J y σ-K y σ)=
          (fun y=>nativeStarFieldTestMean w φ T s star (fun j=>q (j+1)) J y-
            nativeStarFieldTestMean w φ T s star (fun j=>q (j+1)) K y):=by
        funext y
        exact ih s star ho.2.2 _ J K hJ hK y
      rw [HH]
      exact shiftedMean_sub
        (native_star_field_test_mean_smooth T s star hw φ ho.2.2 _ J 0 hJ)
        (native_star_field_test_mean_smooth T s star hw φ ho.2.2 _ K 0 hK)
        (gaussianHierarchy_integrable hw φ _ (clockSteps_ordered ho.2.2 _) b.val (q 0) x)
  | fork T V ihT ihV=>
    cases star with
    | zero=>simp [nativeStarFieldTestMean,expect,mul_sub,Finset.sum_sub_distrib]
    | succ star=>
      cases s with
      | inl s=>
        change (∑τ,V.weight w φ q τ x*_)=(∑τ,V.weight w φ q τ x*_)-(∑τ,V.weight w φ q τ x*_)
        simp_rw [ihT s (star+1) ho q (fun y σ=>J y (σ,_))
          (fun y σ=>K y (σ,_)) (fun σ=>hJ (σ,_)) (fun σ=>hK (σ,_)) x]
        simp only [mul_sub,Finset.sum_sub_distrib]
      | inr s=>
        change (∑σ,T.weight w φ q σ x*_)=(∑σ,T.weight w φ q σ x*_)-(∑σ,T.weight w φ q σ x*_)
        simp_rw [ihV s (star+1) ho q (fun y τ=>J y (_,τ))
          (fun y τ=>K y (_,τ)) (fun τ=>hJ (_,τ)) (fun τ=>hK (_,τ)) x]
        simp only [mul_sub,Finset.sum_sub_distrib]

theorem native_star_field_disorder_mean_sub
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (J K : (ι→ℝ)→T.Assignment→ℝ)
    (hJ : ∀σ,BddSmooth 0 (fun y=>J y σ))
    (hK : ∀σ,BddSmooth 0 (fun y=>K y σ)) (x : ι→ℝ) :
    nativeStarFieldDisorderMean w φ T s star v q (fun y σ=>J y σ-K y σ) x=
    nativeStarFieldDisorderMean w φ T s star v q J x-
      nativeStarFieldDisorderMean w φ T s star v q K x := by
  unfold nativeStarFieldDisorderMean
  simp_rw [native_star_field_test_mean_sub T s star hw φ ho _ J K hJ hK]
  exact integral_sub
    (native_star_field_test_mean_integrable T s star hw φ ho _ J hJ _ x)
    (native_star_field_test_mean_integrable T s star hw φ ho _ K hK _ x)

end OAI.SKFluctuations.Hierarchy.ClockTree
