module

public import ComparisonSignedCavityJointSavedSquare

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeTwoLevelPowerProduct (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (s t : D.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (xi xs : RestCoordinate n → ℝ) : ℝ :=
  let Y:=nativeStarCenteredProjection n tas qs center xs
  nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
    (fun η ζ δ=>(Y (D.atSlot δ t)-Y (D.atSlot δ s))^2*Z η ζ δ*
      (Y (D.atSlot δ s)^j*Y (D.atSlot δ t)^k)) xi xs

theorem native_two_level_power_product_bound (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es D : ClockTree (Spin n) tas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (s t : D.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxs : Measurable xs)
    {B H R : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hZ4 : (∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
      (fun η ζ δ=>Z η ζ δ^4) (xi z) (xs z) ∂μ) ≤ H^4)
    (hA4 : nativeRootTestExpect n D qs μ xs (fun z δ=>
      (nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)-
        nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s))^4) ≤ B^4)
    (hY4 : nativeRootTestExpect n D qs μ xs (fun z δ=>
      (nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s)^(2*j)*
        nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)^(2*k))^2) ≤ R^4) :
    |∫z,nativeTwoLevelPowerProduct n j k Ei Es D Z s t qi qs center (xi z) (xs z) ∂μ| ≤ B^2*H*R := by
  let A:=fun z δ=>nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)-
    nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s)
  let Y:=fun z δ=>nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s)^j*
    nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)^k
  let w:=nativeThreeRootWeight n Ei Es D qi qs xi xs xs
  have hSm (δ) : Measurable (fun z=>nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ s)):=
    (native_star_centered_projection_smooth n hot qs center (D.atSlot δ s) 0).continuous.measurable.comp hxs
  have hTm (δ) : Measurable (fun z=>nativeStarCenteredProjection n tas qs center (xs z) (D.atSlot δ t)):=
    (native_star_centered_projection_smooth n hot qs center (D.atSlot δ t) 0).continuous.measurable.comp hxs
  have hAb (z δ) : |A z δ| ≤ 2*(1+|center|) := by
    apply (abs_sub _ _).trans
    have HS:=native_star_centered_projection_bound n hot qs center (xs z) (D.atSlot δ s)
    have HT:=native_star_centered_projection_bound n hot qs center (xs z) (D.atSlot δ t)
    linarith
  have hYb (z δ) : |Y z δ| ≤ (1+|center|)^(j+k) := by
    dsimp only [Y]
    rw [abs_mul,abs_pow,abs_pow,pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) (native_star_centered_projection_bound n hot qs center (xs z) (D.atSlot δ s)) j)
      (pow_le_pow_left₀ (abs_nonneg _) (native_star_centered_projection_bound n hot qs center (xs z) (D.atSlot δ t)) k)
      (by positivity) (by positivity)
  have HZ : jointFiniteExpect μ w (fun _ a=>Z a.1 a.2.1 a.2.2^4) ≤ H^4 := by
    dsimp only [w]
    rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun _ η ζ δ=>Z η ζ δ^4)]
    simpa only [nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork] using hZ4
  have HA : jointFiniteExpect μ w (fun z a=>A z a.2.2^4) ≤ B^4 := by
    dsimp only [w]
    rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun z _ _ δ=>A z δ^4)]
    simp_rw [Es.expect_const (restWeight_pos n) (restFeature n) hot qs,
      Ei.expect_const (restWeight_pos n) (restFeature n) hoi qi]
    exact hA4
  have HY : jointFiniteExpect μ w (fun z a=>Y z a.2.2^4) ≤ R^4 := by
    dsimp only [w]
    rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun z _ _ δ=>Y z δ^4)]
    simp_rw [Es.expect_const (restWeight_pos n) (restFeature n) hot qs,
      Ei.expect_const (restWeight_pos n) (restFeature n) hoi qi]
    convert hY4 using 1
    unfold nativeRootTestExpect Y
    congr 1
    funext z
    congr 1
    funext δ
    dsimp only
    simp only [mul_pow,←pow_mul]
    congr 1 <;> congr 1 <;> omega
  have Hfinal:=jointFiniteExpect_saved_square_mixed μ w
    (nativeThreeRootWeight_nonneg n Ei Es D hoi hot qi qs xi xs xs)
    (nativeThreeRootWeight_sum n Ei Es D hoi hot qi qs xi xs xs)
    (nativeThreeRootWeight_measurable n Ei Es D hoi hot qi qs xi xs xs hxi hxs hxs)
    (fun a=>Z a.1 a.2.1 a.2.2) (fun z a=>A z a.2.2) (fun z a=>Y z a.2.2)
    (fun a=>(hTm a.2.2).sub (hSm a.2.2))
    (fun a=>((hSm a.2.2).pow_const j).mul ((hTm a.2.2).pow_const k))
    (2*(1+|center|)) ((1+|center|)^(j+k)) (by positivity)
    (fun z a=>hAb z a.2.2) (fun z a=>hYb z a.2.2) hB hH hR HZ HA HY
  dsimp only [w] at Hfinal
  rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun z η ζ δ=>A z δ^2*Z η ζ δ*Y z δ)] at Hfinal
  simpa only [nativeTwoLevelPowerProduct,nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork,A,Y] using Hfinal

end OAI.SKFluctuations.Cavity
