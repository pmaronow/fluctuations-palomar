module

public import ComparisonSignedCavityJointBaseErrorFourth

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeTwoLevelPowerErrorProduct (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (s t : D.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (E : D.Assignment→ℝ) (xi xs : RestCoordinate n → ℝ) : ℝ :=
  nativeTwoLevelPowerProduct n j k Ei Es D (fun η ζ δ=>Z η ζ δ*E δ)
    s t qi qs center xi xs

theorem native_two_level_power_error_product_bound (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (s t : D.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    (E : D.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxs : Measurable xs)
    {B H C R : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hZ8 : (∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
      (fun η ζ δ=>Z η ζ δ^8) (xi z) (xs z) ∂μ) ≤ H^8)
    (hE8 : nativeRootTestExpect n D qs μ xs (fun _ δ=>E δ^8) ≤ C^8)
    (hA4 : nativeRootTestExpect n D qs μ xs (fun z δ=>
      (nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)-
        nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s))^4) ≤ B^4)
    (hY4 : nativeRootTestExpect n D qs μ xs (fun z δ=>
      (nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s)^(2*j)*
        nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)^(2*k))^2) ≤ R^4) :
    |∫z,nativeTwoLevelPowerErrorProduct n j k Ei Es D Z s t qi qs center E (xi z) (xs z) ∂μ| ≤
      B^2*H*R*C := by
  have HZE:=native_three_root_base_error_fourth n Ei Es D hoi hot qi qs μ xi xs hxi hxs Z E hZ8 hE8
  have HF:=native_two_level_power_product_bound n j k Ei Es D hoi hot
    (fun η ζ δ=>Z η ζ δ*E δ) s t qi qs center μ xi xs hxi hxs
    hB (mul_nonneg hH hC) hR HZE hA4 hY4
  simpa only [nativeTwoLevelPowerErrorProduct,mul_assoc,mul_comm,mul_left_comm] using HF

end OAI.SKFluctuations.Cavity
