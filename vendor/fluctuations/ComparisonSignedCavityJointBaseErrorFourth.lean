module

public import ComparisonSignedCavityTwoLevelPowerProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem jointFiniteExpect_mul_fourth_bound
    {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) [IsFiniteMeasure μ] (w : P→S→ℝ)
    (hw : ∀z s,0 ≤ w z s) (hsum : ∀z,∑s,w z s=1)
    (hwm : ∀s,Measurable (fun z=>w z s))
    (Z E : S→ℝ) {H R : ℝ}
    (hZ8 : jointFiniteExpect μ w (fun _ s=>Z s^8) ≤ H^8)
    (hE8 : jointFiniteExpect μ w (fun _ s=>E s^8) ≤ R^8) :
    jointFiniteExpect μ w (fun _ s=>(Z s*E s)^4) ≤ (H*R)^4 := by
  let CZ:=∑s,|Z s|
  let CE:=∑s,|E s|
  have hZb (s) : |Z s| ≤ CZ:=Finset.single_le_sum (f:=fun s=>|Z s|)
    (fun _ _=>abs_nonneg _) (Finset.mem_univ s)
  have hEb (s) : |E s| ≤ CE:=Finset.single_le_sum (f:=fun s=>|E s|)
    (fun _ _=>abs_nonneg _) (Finset.mem_univ s)
  have HX:=jointFiniteExpect_mul_sq_le μ w hw hsum hwm
    (fun _ s=>Z s^4) (fun _ s=>E s^4) (fun _=>measurable_const) (fun _=>measurable_const)
    (CZ^4) (CE^4) (by positivity)
    (fun _ s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hZb s) 4)
    (fun _ s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hEb s) 4)
  have heZ:(fun (_:P) s=>(Z s^4)^2)=(fun _ s=>Z s^8):=by funext z s;ring
  have heE:(fun (_:P) s=>(E s^4)^2)=(fun _ s=>E s^8):=by funext z s;ring
  rw [heZ,heE] at HX
  have HE0:=jointFiniteExpect_nonneg μ w hw (fun _ s=>E s^8) (fun _ _=>by positivity)
  have Hbound:=HX.trans (mul_le_mul hZ8 hE8 HE0 (by positivity))
  have Hzero:=jointFiniteExpect_nonneg μ w hw (fun _ s=>Z s^4*E s^4) (fun _ _=>by positivity)
  simp only [mul_pow]
  apply (sq_le_sq₀ Hzero (by positivity : 0 ≤ H^4*R^4)).mp
  convert Hbound using 1
  ring

theorem native_three_root_base_error_fourth
    (n : ℕ) {ias tas : List PositiveMass}
    (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (xi xs : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxs : Measurable xs)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (E : D.Assignment→ℝ)
    {H R : ℝ}
    (hZ8 : (∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
      (fun η ζ δ=>Z η ζ δ^8) (xi z) (xs z) ∂μ) ≤ H^8)
    (hE8 : nativeRootTestExpect n D qs μ xs (fun _ δ=>E δ^8) ≤ R^8) :
    (∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n) qi qs
      (fun η ζ δ=>(Z η ζ δ*E δ)^4) (xi z) (xs z) ∂μ) ≤ (H*R)^4 := by
  let w:=nativeThreeRootWeight n Ei Es D qi qs xi xs xs
  have HZ:jointFiniteExpect μ w (fun _ s=>Z s.1 s.2.1 s.2.2^8) ≤ H^8:=by
    dsimp only [w]
    rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun _ η ζ δ=>Z η ζ δ^8)]
    simpa only [nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork] using hZ8
  have HE:jointFiniteExpect μ w (fun _ s=>E s.2.2^8) ≤ R^8:=by
    dsimp only [w]
    rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun _ _ _ δ=>E δ^8)]
    simp_rw [Es.expect_const (restWeight_pos n) (restFeature n) hot qs,
      Ei.expect_const (restWeight_pos n) (restFeature n) hoi qi]
    exact hE8
  have HX:=jointFiniteExpect_mul_fourth_bound μ w
    (nativeThreeRootWeight_nonneg n Ei Es D hoi hot qi qs xi xs xs)
    (nativeThreeRootWeight_sum n Ei Es D hoi hot qi qs xi xs xs)
    (nativeThreeRootWeight_measurable n Ei Es D hoi hot qi qs xi xs xs hxi hxs hxs)
    (fun s=>Z s.1 s.2.1 s.2.2) (fun s=>E s.2.2) HZ HE
  dsimp only [w] at HX
  rw [nativeThreeRootWeight_expect n Ei Es D qi qs μ xi xs xs (fun _ η ζ δ=>(Z η ζ δ*E δ)^4)] at HX
  simpa only [nativeExteriorForestConditionalTest_eq_joint,ClockTree.expect_fork] using HX

end OAI.SKFluctuations.Cavity
