module

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

def nativeTwoLevelIncomingProduct (n j k : ℕ)
    {ias as : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es T : ClockTree (Spin n) as) (H : Ei.Assignment → Es.Assignment → ℝ)
    (e : Ei.Slot) (s t : T.Slot) (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (center : ℝ) (xi xs : RestCoordinate n → ℝ) : ℝ :=
  let Y:=nativeStarCenteredProjection n as qs center xs
  T.expect (restWeight n) (restFeature n) qs (fun σ=>
    (Y (T.atSlot σ t)-Y (T.atSlot σ s))*
    inner ℝ (WithLp.toLp 2 (normalizedSpin n (T.atSlot σ t))-
      WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s)))
      (nativeTwoLevelWeightedAnchor n Ei Es H e qi qs xi xs)*
    (Y (T.atSlot σ s)^j*Y (T.atSlot σ t)^k)) xs

theorem native_two_level_incoming_product_abs_le_moments (n j k : ℕ)
    {ias as : List PositiveMass} (Ei : ClockTree (Spin n) ias)
    (Es T : ClockTree (Spin n) as) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast as)
    (H : Ei.Assignment → Es.Assignment → ℝ) (e : Ei.Slot) (s t : T.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0) (center : ℝ)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P → RestCoordinate n → ℝ) (hxi : Measurable xi) (hxs : Measurable xs) :
    |∫z,nativeTwoLevelIncomingProduct n j k Ei Es T H e s t qi qs center (xi z) (xs z) ∂μ| ≤
      Real.sqrt (Real.sqrt (
        (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single as) (fun _=>1)
          (ClockTree.singleSlot as) qs qs (xs z) (xs z) ∂μ)*
        (∫z,nativeTwoLevelProjectionFourth n Ei Es T H e s t qi qs qs (xi z) (xs z) (xs z) ∂μ))*
        nativeRootTestExpect n T qs μ xs (fun z σ=>
          (nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ s)^j*
            nativeStarCenteredProjection n as qs center (xs z) (T.atSlot σ t)^k)^2)) := by
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
  have HG:=native_root_test_three_saved_bound n T hos qs μ xs hxs A B Y
    (fun σ=>(hT σ).sub (hS σ)) (fun σ=>measurable_const.inner hV)
    (fun σ=>((hS σ).pow_const j).mul ((hT σ).pow_const k))
    (2*(1+|center|)) (Cspin*R) ((1+|center|)^(j+k))
    (by positivity) (mul_nonneg hCspin hR.le) (by positivity) hAb hBb hYb
  have heA : nativeRootTestExpect n T qs μ xs (fun z σ=>A z σ^4)=
      ∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single as) (fun _=>1)
        (ClockTree.singleSlot as) qs qs (xs z) (xs z) ∂μ := by
    unfold nativeRootTestExpect nativeSubtreeExteriorProjectionFourth
    simp only [A,native_star_centered_projection_difference]
  rw [heA] at HG
  exact HG

theorem two_level_incoming_moment_scales {a b c A B C : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hpa : a ≤ A^4) (hpb : b ≤ B^4) (hpc : c ≤ C^2) :
    Real.sqrt (Real.sqrt (a*b)*c) ≤ A*B*C := by
  have H1:=Real.sqrt_le_sqrt (mul_le_mul hpa hpb hb (by positivity))
  have he1 : Real.sqrt (A^4*B^4)=(A*B)^2 := by
    rw [←mul_pow,show (A*B)^4=((A*B)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [he1] at H1
  have H2:=Real.sqrt_le_sqrt (mul_le_mul H1 hpc hc (sq_nonneg _))
  have he2 : Real.sqrt ((A*B)^2*C^2)=A*B*C := by
    rw [←mul_pow,Real.sqrt_sq (by positivity)]
  rw [he2] at H2
  exact H2

end OAI.SKFluctuations.Cavity
