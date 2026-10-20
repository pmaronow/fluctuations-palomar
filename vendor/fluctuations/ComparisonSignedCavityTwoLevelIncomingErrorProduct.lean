module

public import ComparisonSignedCavityRootFourFactorSaving
public import ComparisonSignedCavityActualMixedStarProjectionPowers
public import ComparisonSignedCavityActualCanonicalTwoLevelProjection
public import ComparisonSignedCavityCalibratedStarSubtreeProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeTwoLevelIncomingErrorProduct (n j k : ℕ)
    {ias as : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es T : ClockTree (Spin n) as) (H : Ei.Assignment → Es.Assignment → ℝ)
    (e : Ei.Slot) (s t : T.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (E : T.Assignment→ℝ) (xi xs : RestCoordinate n → ℝ) : ℝ :=
  let Y:=nativeStarCenteredProjection n as qs center xs
  T.expect (restWeight n) (restFeature n) qs (fun σ=>
    (Y (T.atSlot σ t)-Y (T.atSlot σ s))*
    inner ℝ (WithLp.toLp 2 (normalizedSpin n (T.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s)))
      (nativeTwoLevelWeightedAnchor n Ei Es H e qi qs xi xs)*E σ*
    (Y (T.atSlot σ s)^j*Y (T.atSlot σ t)^k)) xs

theorem native_two_level_incoming_error_product_abs_le_moments (n j k : ℕ)
    {ias as : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es T : ClockTree (Spin n) as) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast as)
    (H : Ei.Assignment → Es.Assignment → ℝ) (e : Ei.Slot) (s t : T.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ) (E : T.Assignment→ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P → RestCoordinate n → ℝ) (hxi : Measurable xi) (hxs : Measurable xs) :
    |∫z,nativeTwoLevelIncomingErrorProduct n j k Ei Es T H e s t qi qs center E (xi z) (xs z) ∂μ| ≤
      Real.sqrt (Real.sqrt (
        (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single as) (fun _=>1)
          (ClockTree.singleSlot as) qs qs (xs z) (xs z) ∂μ)*
        (∫z,nativeTwoLevelProjectionFourth n Ei Es T H e s t qi qs qs (xi z) (xs z) (xs z) ∂μ))*
        Real.sqrt (nativeRootTestExpect n T qs μ xs (fun _ σ=>E σ^4)*
          nativeRootTestExpect n T qs μ xs (fun z σ=>
            (nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ s)^j*
              nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ t)^k)^4))) := by
  let Y:=fun z σ=>nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ s)^j*
    nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ t)^k
  let A:=fun z σ=>nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ t)-
    nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ s)
  let V : P → EuclideanSpace ℝ (Fin n):=fun z=>nativeTwoLevelWeightedAnchor n Ei Es H e qi qs (xi z) (xs z)
  let F:=fun σ : T.Assignment=>WithLp.toLp 2 (normalizedSpin n (T.atSlot σ t))-
    WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))
  let B:=fun z σ=>inner ℝ (F σ) (V z)
  have hS (σ) : Measurable (fun z=>nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ s)):=
    (native_star_centered_projection_smooth n hos qs center _ 0).continuous.measurable.comp hxs
  have hT (σ) : Measurable (fun z=>nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ t)):=
    (native_star_centered_projection_smooth n hos qs center _ 0).continuous.measurable.comp hxs
  have hV : Measurable V := by
    have hcont:=nativeTwoLevelWeightedAnchor_continuous n Ei Es hoi hos H e qi qs
    have hmeas:=hcont.measurable.comp (hxi.prodMk hxs)
    exact hmeas
  obtain ⟨R,hR,hRb⟩:=nativeTwoLevelWeightedAnchor_exists_bound n Ei Es hoi hos H e qi qs
  let Cspin:=∑σ : T.Assignment,‖F σ‖
  have hCspin : 0 ≤ Cspin:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have hF (σ) : ‖F σ‖ ≤ Cspin:=Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ σ)
  have hAb (z) (σ) : |A z σ| ≤ 2*(1+|center|) := by
    apply (abs_sub _ _).trans
    have h1:=native_star_centered_projection_bound n hos qs center (xs z) (T.atSlot σ t)
    have h2:=native_star_centered_projection_bound n hos qs center (xs z) (T.atSlot σ s)
    linarith
  have hBb (z) (σ) : |B z σ| ≤ Cspin*R :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hF σ) (hRb (xi z) (xs z))
      (norm_nonneg _) hCspin)
  have hYb (z) (σ) : |Y z σ| ≤ (1+|center|)^(j+k) := by
    rw [abs_mul,abs_pow,abs_pow,pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) (native_star_centered_projection_bound n hos qs center (xs z) (T.atSlot σ s)) j)
      (pow_le_pow_left₀ (abs_nonneg _) (native_star_centered_projection_bound n hos qs center (xs z) (T.atSlot σ t)) k)
      (by positivity) (by positivity)
  let CE:=∑σ : T.Assignment,|E σ|
  have hCE:0 ≤ CE:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hEb (z : P) (σ : T.Assignment) : |E σ| ≤ CE:=
    Finset.single_le_sum (f:=fun τ=>|E τ|) (fun _ _=>abs_nonneg _) (Finset.mem_univ σ)
  have HG:=native_root_test_four_saved_bound n T hos qs μ xs hxs A B (fun _ σ=>E σ) Y
    (fun σ=>(hT σ).sub (hS σ)) (fun σ=>measurable_const.inner hV)
    (fun _=>measurable_const)
    (fun σ=>((hS σ).pow_const j).mul ((hT σ).pow_const k))
    (2*(1+|center|)) (Cspin*R) CE ((1+|center|)^(j+k))
    (by positivity) (mul_nonneg hCspin hR.le) hCE (by positivity) hAb hBb hEb hYb
  have heA : nativeRootTestExpect n T qs μ xs (fun z σ=>A z σ^4)=
      ∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single as) (fun _=>1)
        (ClockTree.singleSlot as) qs qs (xs z) (xs z) ∂μ := by
    unfold nativeRootTestExpect nativeSubtreeExteriorProjectionFourth
    simp only [A,native_star_centered_projection_difference]
  rw [heA] at HG
  exact HG

end OAI.SKFluctuations.Cavity
