module

public import ComparisonSignedCavityActualOriginalOneStep
public import ComparisonSignedCavityActualResourceResponseOperations

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set
set_option maxHeartbeats 8000000

theorem native_full_endpoint_clock_mixed_independent (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (l : ℝ) (b h K₁ K₂ : ℕ→ℝ) :
    cutFullVariance n q U l 1 b h K₁=cutFullVariance n q U l 1 b h K₂ := by
  funext j a
  rcases a with (a|a)|(a|a) <;>
    simp only [cutFullVariance,fullVariance,Sum.elim_inl,Sum.elim_inr,sub_self,zero_mul]

theorem native_original_rest_test_expectation_mixed_independent (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K₁ K₂ : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeOriginalRestTestExpectation n q U b h K₁ T P=
      nativeOriginalRestTestExpectation n q U b h K₂ T P := by
  unfold nativeOriginalRestTestExpectation
  rw [native_full_endpoint_clock_mixed_independent n q U 1 b h K₁ K₂]

theorem native_original_centered_rest_test_mixed_independent (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K₁ K₂ : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeOriginalCenteredRestTest n q U b h K₁ T P=
      nativeOriginalCenteredRestTest n q U b h K₂ T P := by
  unfold nativeOriginalCenteredRestTest
  rw [native_original_rest_test_expectation_mixed_independent n q U b h K₁ K₂ T P]

theorem native_original_site_pair_expectation_mixed_independent (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K₁ K₂ : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) :
    nativeOriginalSitePairExpectation n q U b h K₁ T P a c=
      nativeOriginalSitePairExpectation n q U b h K₂ T P a c := by
  unfold nativeOriginalSitePairExpectation
  rw [native_full_endpoint_clock_mixed_independent n q U 1 b h K₁ K₂]

theorem native_resource_value_original_mixed_independent {n : ℕ} {as : List PositiveMass}
    {i star : ℕ} {T : ClockTree (Spin n×Bool) as} (P : NativeResourceTerm i star T)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K₁ K₂ C : ℕ→ℝ)
    (R : (Spin n×Bool)→(Spin n×Bool)→ℝ) (v x : FullCoordinate n→ℝ) :
    P.value (fullWeight n) (fullFeature n) v (cutFullVariance n q U 1 1 b h K₁) R C x=
      P.value (fullWeight n) (fullFeature n) v (cutFullVariance n q U 1 1 b h K₂) R C x := by
  rw [native_full_endpoint_clock_mixed_independent n q U 1 b h K₁ K₂]

end OAI.SKFluctuations.Cavity
