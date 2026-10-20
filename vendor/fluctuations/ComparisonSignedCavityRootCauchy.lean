module

public import ComparisonSignedCavityIntegratedPairLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeRootTestExpect (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n) as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P→RestCoordinate n→ℝ) (J : P→T.Assignment→ℝ) : ℝ :=
  ∫ z, T.expect (restWeight n) (restFeature n) q (J z) (x z) ∂μ

theorem native_root_test_expect_nonneg (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P→RestCoordinate n→ℝ) (J : P→T.Assignment→ℝ)
    (hJ : ∀ z σ, 0 ≤ J z σ) : 0 ≤ nativeRootTestExpect n T q μ x J := by
  apply integral_nonneg
  intro z
  unfold ClockTree.expect
  exact Finset.sum_nonneg fun σ _=>mul_nonneg
    ((T.weight_probability (restWeight_pos n) (restFeature n) ho q (x z)).1 σ) (hJ z σ)

private theorem native_weight_measurable (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (q : ℕ→RestCoordinate n→ℝ≥0) (σ : T.Assignment)
    {P : Type} [MeasurableSpace P] (x : P→RestCoordinate n→ℝ) (hx : Measurable x) :
    Measurable (fun z=>T.weight (restWeight n) (restFeature n) q σ (x z)) := by
  simpa only [ClockTree.weight_featureLaw,Function.comp_def] using
    (clockFeatureWeight_measurable (restWeight n) (restFeature n) T q σ).comp
      ((featureVector (restFeature n)).measurable.comp hx)

theorem native_root_test_integrable (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P→RestCoordinate n→ℝ) (hx : Measurable x) (J : P→T.Assignment→ℝ)
    (hJ : ∀ σ, Measurable (fun z=>J z σ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z σ, |J z σ| ≤ C) :
    Integrable (fun z=>T.expect (restWeight n) (restFeature n) q (J z) (x z)) μ := by
  have hm : Measurable (fun z=>T.expect (restWeight n) (restFeature n) q (J z) (x z)) := by
    unfold ClockTree.expect
    exact Finset.measurable_sum _ fun σ _=>(native_weight_measurable n T q σ x hx).mul (hJ σ)
  apply Integrable.of_bound hm.aestronglyMeasurable C
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  unfold ClockTree.expect
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ σ, T.weight (restWeight n) (restFeature n) q σ (x z)*C := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_of_nonneg
        ((T.weight_probability (restWeight_pos n) (restFeature n) ho q (x z)).1 σ)]
      exact mul_le_mul_of_nonneg_left (hbound z σ)
        ((T.weight_probability (restWeight_pos n) (restFeature n) ho q (x z)).1 σ)
    _=C := by
      rw [←Finset.sum_mul,(T.weight_probability (restWeight_pos n) (restFeature n) ho q (x z)).2]
      ring

theorem native_root_test_mul_sq_le (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (J L : P→T.Assignment→ℝ)
    (hJ : ∀ σ, Measurable (fun z=>J z σ)) (hL : ∀ σ, Measurable (fun z=>L z σ))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJb : ∀ z σ, |J z σ| ≤ C) (hLb : ∀ z σ, |L z σ| ≤ D) :
    nativeRootTestExpect n T q μ x (fun z σ=>J z σ*L z σ)^2 ≤ 
      nativeRootTestExpect n T q μ x (fun z σ=>J z σ^2)*
        nativeRootTestExpect n T q μ x (fun z σ=>L z σ^2) := by
  have hIjj := native_root_test_integrable n T ho q μ x hx (fun z σ=>J z σ^2)
    (fun σ=>(hJ σ).pow_const 2) (C^2) (sq_nonneg _)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hJb z σ) 2)
  have hIll := native_root_test_integrable n T ho q μ x hx (fun z σ=>L z σ^2)
    (fun σ=>(hL σ).pow_const 2) (D^2) (sq_nonneg _)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hLb z σ) 2)
  have hIjl := native_root_test_integrable n T ho q μ x hx (fun z σ=>J z σ*L z σ)
    (fun σ=>(hJ σ).mul (hL σ)) (C*D) (mul_nonneg hC hD)
    (fun z σ=>by rw [abs_mul]; exact mul_le_mul (hJb z σ) (hLb z σ) (abs_nonneg _) hC)
  have hpos (t : ℝ) : 0 ≤ 
      nativeRootTestExpect n T q μ x (fun z σ=>J z σ^2)*(t*t)+
      (2*nativeRootTestExpect n T q μ x (fun z σ=>J z σ*L z σ))*t+
      nativeRootTestExpect n T q μ x (fun z σ=>L z σ^2) := by
    have hp := native_root_test_expect_nonneg n T ho q μ x
      (fun z σ=>(t*J z σ+L z σ)^2) (fun z σ=>sq_nonneg _)
    have he (z) : T.expect (restWeight n) (restFeature n) q
        (fun σ=>(t*J z σ+L z σ)^2) (x z)=
        t^2*T.expect (restWeight n) (restFeature n) q (fun σ=>J z σ^2) (x z)+
          (2*t)*T.expect (restWeight n) (restFeature n) q (fun σ=>J z σ*L z σ) (x z)+
          T.expect (restWeight n) (restFeature n) q (fun σ=>L z σ^2) (x z) := by
      unfold ClockTree.expect
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    unfold nativeRootTestExpect at hp ⊢
    simp_rw [he] at hp
    have e1 := integral_add ((hIjj.const_mul (t^2)).add (hIjl.const_mul (2*t))) hIll
    have e2 := integral_add (hIjj.const_mul (t^2)) (hIjl.const_mul (2*t))
    simp only [Pi.add_apply] at e1 e2
    rw [e1,e2,integral_const_mul,integral_const_mul] at hp
    nlinarith
  have hd := discrim_le_zero hpos
  dsimp only [discrim] at hd
  nlinarith

theorem native_root_test_mul_abs_le_sqrt (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (J L : P→T.Assignment→ℝ)
    (hJ : ∀ σ, Measurable (fun z=>J z σ)) (hL : ∀ σ, Measurable (fun z=>L z σ))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJb : ∀ z σ, |J z σ| ≤ C) (hLb : ∀ z σ, |L z σ| ≤ D) :
    |nativeRootTestExpect n T q μ x (fun z σ=>J z σ*L z σ)| ≤ 
      Real.sqrt (nativeRootTestExpect n T q μ x (fun z σ=>J z σ^2)*
        nativeRootTestExpect n T q μ x (fun z σ=>L z σ^2)) := by
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg
    (native_root_test_expect_nonneg n T ho q μ x _ (fun z σ=>sq_nonneg _))
    (native_root_test_expect_nonneg n T ho q μ x _ (fun z σ=>sq_nonneg _)))).mpr
  rw [sq_abs]
  exact native_root_test_mul_sq_le n T ho q μ x hx J L hJ hL C D hC hD hJb hLb

theorem native_root_test_three_saved_bound (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (A D Y : P→T.Assignment→ℝ)
    (hA : ∀ σ, Measurable (fun z=>A z σ)) (hD : ∀ σ, Measurable (fun z=>D z σ))
    (hY : ∀ σ, Measurable (fun z=>Y z σ))
    (CA CD CY : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hCY : 0 ≤ CY)
    (hAb : ∀ z σ, |A z σ| ≤ CA) (hDb : ∀ z σ, |D z σ| ≤ CD)
    (hYb : ∀ z σ, |Y z σ| ≤ CY) :
    |nativeRootTestExpect n T q μ x (fun z σ=>A z σ*D z σ*Y z σ)| ≤ 
      Real.sqrt (Real.sqrt (
        nativeRootTestExpect n T q μ x (fun z σ=>A z σ^4)*
        nativeRootTestExpect n T q μ x (fun z σ=>D z σ^4))*
        nativeRootTestExpect n T q μ x (fun z σ=>Y z σ^2)) := by
  have hfirst := native_root_test_mul_abs_le_sqrt n T ho q μ x hx
    (fun z σ=>A z σ*D z σ) Y (fun σ=>(hA σ).mul (hD σ)) hY
    (CA*CD) CY (mul_nonneg hCA hCD) hCY
    (fun z σ=>by rw [abs_mul]; exact mul_le_mul (hAb z σ) (hDb z σ) (abs_nonneg _) hCA) hYb
  have hsecond := native_root_test_mul_abs_le_sqrt n T ho q μ x hx
    (fun z σ=>A z σ^2) (fun z σ=>D z σ^2)
    (fun σ=>(hA σ).pow_const 2) (fun σ=>(hD σ).pow_const 2)
    (CA^2) (CD^2) (sq_nonneg _) (sq_nonneg _)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hAb z σ) 2)
    (fun z σ=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hDb z σ) 2)
  have heA : (fun z σ=>(A z σ^2)^2)=(fun z σ=>A z σ^4) := by funext z σ; ring
  have heD : (fun z σ=>(D z σ^2)^2)=(fun z σ=>D z σ^4) := by funext z σ; ring
  have heAD : (fun z σ=>(A z σ*D z σ)^2)=(fun z σ=>A z σ^2*D z σ^2) := by funext z σ; ring
  rw [heA,heD,abs_of_nonneg (native_root_test_expect_nonneg n T ho q μ x _
    (fun z σ=>mul_nonneg (sq_nonneg _) (sq_nonneg _)))] at hsecond
  rw [heAD] at hfirst
  apply hfirst.trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right hsecond
    (native_root_test_expect_nonneg n T ho q μ x _ (fun z σ=>sq_nonneg _))

theorem native_incoming_anchor_placement_integral_saved_differences (n k : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (H : E.Assignment→ℝ) (s : E.Slot)
    (q : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
    (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (hA : ∀ σ, Measurable (fun z=>nativeIncomingProjectionDifference n q (x z) center p σ))
    (hD : ∀ σ, Measurable (fun z=>nativeIncomingAnchorDifference n E H s q (x z) p σ))
    (hY : ∀ σ, Measurable (fun z=>
      nativeCenteredProjectedDeletedOverlap n as q (x z) center (p.restSpin σ)^k))
    (CA CD CY : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hCY : 0 ≤ CY)
    (hAb : ∀ z σ, |nativeIncomingProjectionDifference n q (x z) center p σ| ≤ CA)
    (hDb : ∀ z σ, |nativeIncomingAnchorDifference n E H s q (x z) p σ| ≤ CD)
    (hYb : ∀ z σ,
      |nativeCenteredProjectedDeletedOverlap n as q (x z) center (p.restSpin σ)^k| ≤ CY)
    (hM : Integrable (fun z=>nativeIncomingRawTargetMoment n k as q (x z) center) μ) :
    |∫ z, nativeIncomingAnchorPlacement n k E H s q (x z) center p ∂μ| ≤ 
      Real.sqrt (Real.sqrt (
        (∫ z, nativeIncomingProjectionFourth n q (x z) center p ∂μ)*
        (∫ z, nativeIncomingAnchorFourth n E H s q (x z) p ∂μ))*
        (∫ z, nativeIncomingRawTargetMoment n k as q (x z) center ∂μ)) := by
  let T := p.tree.cavityLeft
  let A := fun z σ=>nativeIncomingProjectionDifference n q (x z) center p σ
  let D := fun z σ=>nativeIncomingAnchorDifference n E H s q (x z) p σ
  let Y := fun z σ=>nativeCenteredProjectedDeletedOverlap n as q (x z) center (p.restSpin σ)^k
  have hthree := native_root_test_three_saved_bound n T ho q μ x hx A D Y hA hD hY
    CA CD CY hCA hCD hCY hAb hDb hYb
  have hcontract (z) : T.expect (restWeight n) (restFeature n) q
      (fun σ=>Y z σ^2) (x z) ≤ nativeIncomingRawTargetMoment n k as q (x z) center := by
    have hp := native_projected_target_power_moment_le n (2*k) T ho
      (nativeIncomingNewSlot p) q (x z) center
    simpa only [nativeIncomingRawTargetMoment,Y,T,ClockTree.MarkedPlacement.restSpin,
      nativeIncomingNewSlot,←pow_mul,show k*2=2*k by omega,
      (even_two_mul k).pow_abs] using hp
  have hIY := native_root_test_integrable n T ho q μ x hx (fun z σ=>Y z σ^2)
    (fun σ=>(hY σ).pow_const 2) (CY^2) (sq_nonneg _)
    (fun z σ=>by simpa only [Y,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hYb z σ) 2)
  have hc := integral_mono hIY hM hcontract
  have hA4 := native_root_test_expect_nonneg n T ho q μ x (fun z σ=>A z σ^4)
    (fun z σ=>by positivity)
  have hD4 := native_root_test_expect_nonneg n T ho q μ x (fun z σ=>D z σ^4)
    (fun z σ=>by positivity)
  have heJ : (fun z σ=>A z σ*D z σ*Y z σ)=
      (fun z σ=>A z σ*Y z σ*D z σ) := by funext z σ; ring
  rw [heJ] at hthree
  apply hthree.trans
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)

end OAI.SKFluctuations.Cavity
