module

public import ComparisonSignedCavityJointFiniteHolder

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeThreeRootWeight (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type}
    (xi xb xd : P→RestCoordinate n→ℝ)
    (z : P) (s : A.Assignment×(B.Assignment×D.Assignment)) : ℝ :=
  A.weight (restWeight n) (restFeature n) qi s.1 (xi z)*
    (B.weight (restWeight n) (restFeature n) qs s.2.1 (xb z)*
      D.weight (restWeight n) (restFeature n) qs s.2.2 (xd z))

theorem nativeThreeRootWeight_nonneg (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type}
    (xi xb xd : P→RestCoordinate n→ℝ) (z : P) (s : A.Assignment×(B.Assignment×D.Assignment)) :
    0 ≤ nativeThreeRootWeight n A B D qi qs xi xb xd z s := by
  exact mul_nonneg ((A.weight_probability (restWeight_pos n) (restFeature n) hoi qi (xi z)).1 _)
    (mul_nonneg ((B.weight_probability (restWeight_pos n) (restFeature n) hot qs (xb z)).1 _)
      ((D.weight_probability (restWeight_pos n) (restFeature n) hot qs (xd z)).1 _))

theorem nativeThreeRootWeight_sum (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type}
    (xi xb xd : P→RestCoordinate n→ℝ) (z : P) :
    (∑s,nativeThreeRootWeight n A B D qi qs xi xb xd z s)=1 := by
  simp only [nativeThreeRootWeight,Fintype.sum_prod_type,←Finset.mul_sum]
  rw [(D.weight_probability (restWeight_pos n) (restFeature n) hot qs (xd z)).2]
  simp only [mul_one]
  rw [(B.weight_probability (restWeight_pos n) (restFeature n) hot qs (xb z)).2]
  simp only [mul_one]
  exact (A.weight_probability (restWeight_pos n) (restFeature n) hoi qi (xi z)).2

theorem nativeThreeRootWeight_measurable (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (xi xb xd : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxb : Measurable xb)
    (hxd : Measurable xd) (s : A.Assignment×(B.Assignment×D.Assignment)) :
    Measurable (fun z=>nativeThreeRootWeight n A B D qi qs xi xb xd z s) := by
  exact ((A.weight_smooth (restWeight_pos n) (restFeature n) hoi qi s.1 0).continuous.measurable.comp hxi).mul
    (((B.weight_smooth (restWeight_pos n) (restFeature n) hot qs s.2.1 0).continuous.measurable.comp hxb).mul
      ((D.weight_smooth (restWeight_pos n) (restFeature n) hot qs s.2.2 0).continuous.measurable.comp hxd))

theorem nativeThreeRootWeight_expect (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (xi xb xd : P→RestCoordinate n→ℝ)
    (J : P→A.Assignment→B.Assignment→D.Assignment→ℝ) :
    jointFiniteExpect μ (nativeThreeRootWeight n A B D qi qs xi xb xd)
      (fun z s=>J z s.1 s.2.1 s.2.2)=
      ∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
        B.expect (restWeight n) (restFeature n) qs (fun β=>
          D.expect (restWeight n) (restFeature n) qs (J z η β) (xd z)) (xb z)) (xi z) ∂μ := by
  unfold jointFiniteExpect nativeThreeRootWeight ClockTree.expect
  simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem native_three_root_old_second_projection_fourth
    (n : ℕ) {ias tas : List PositiveMass}
    (A : ClockTree (Spin n) ias) (B D : ClockTree (Spin n) tas)
    {ai ast : ℝ} (hoi : MassOrdered ai ias) (hot : MassOrdered ast tas)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ]
    (xi xb xd : P→RestCoordinate n→ℝ) (hxi : Measurable xi) (hxb : Measurable xb)
    (hxd : Measurable xd)
    (Z : A.Assignment→B.Assignment→D.Assignment→ℝ) (J : P→D.Assignment→ℝ)
    (hJ : ∀δ,Measurable (fun z=>J z δ)) (CJ : ℝ) (hJb : ∀z δ,|J z δ| ≤ CJ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hZ2 : (∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
      B.expect (restWeight n) (restFeature n) qs (fun β=>D.expect (restWeight n) (restFeature n)
        qs (fun δ=>Z η β δ^2) (xd z)) (xb z)) (xi z) ∂μ) ≤ p^2)
    (hJ4 : (∫z,D.expect (restWeight n) (restFeature n) qs (fun δ=>J z δ^4) (xd z) ∂μ) ≤ r^4) :
    |∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
      B.expect (restWeight n) (restFeature n) qs (fun β=>D.expect (restWeight n) (restFeature n)
        qs (fun δ=>Z η β δ*J z δ) (xd z)) (xb z)) (xi z) ∂μ| ≤ p*r := by
  let w:=nativeThreeRootWeight n A B D qi qs xi xb xd
  let Z':=fun (_ : P) (s : A.Assignment×(B.Assignment×D.Assignment))=>Z s.1 s.2.1 s.2.2
  let J':=fun (z : P) (s : A.Assignment×(B.Assignment×D.Assignment))=>J z s.2.2
  let CZ:=∑s : A.Assignment×(B.Assignment×D.Assignment),|Z s.1 s.2.1 s.2.2|
  have hCZ : 0 ≤ CZ:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hZb : ∀z s,|Z' z s| ≤ CZ := by
    intro z s
    dsimp only [Z',CZ]
    exact Finset.single_le_sum (f:=fun a : A.Assignment×(B.Assignment×D.Assignment)=>|Z a.1 a.2.1 a.2.2|)
      (fun _ _=>abs_nonneg _) (Finset.mem_univ s)
  have HZ : jointFiniteExpect μ w (fun z s=>Z' z s^2) ≤ p^2 := by
    dsimp only [w,Z']
    rw [nativeThreeRootWeight_expect n A B D qi qs μ xi xb xd (fun _ η β δ=>Z η β δ^2)]
    exact hZ2
  have HJ : jointFiniteExpect μ w (fun z s=>J' z s^4) ≤ r^4 := by
    dsimp only [w,J']
    rw [nativeThreeRootWeight_expect n A B D qi qs μ xi xb xd (fun z _ _ δ=>J z δ^4)]
    simp_rw [ClockTree.expect_const (restWeight_pos n) (restFeature n) B hot qs,
      ClockTree.expect_const (restWeight_pos n) (restFeature n) A hoi qi]
    exact hJ4
  have H:=jointFiniteExpect_old_second_projection_fourth μ w
    (nativeThreeRootWeight_nonneg n A B D hoi hot qi qs xi xb xd)
    (nativeThreeRootWeight_sum n A B D hoi hot qi qs xi xb xd)
    (nativeThreeRootWeight_measurable n A B D hoi hot qi qs xi xb xd hxi hxb hxd)
    Z' J' (fun _=>measurable_const) (fun s=>hJ s.2.2) CZ CJ hCZ hZb (fun z s=>hJb z s.2.2)
    hp hr HZ HJ
  dsimp only [w,Z',J'] at H
  rw [nativeThreeRootWeight_expect n A B D qi qs μ xi xb xd (fun z η β δ=>Z η β δ*J z δ)] at H
  exact H

end OAI.SKFluctuations.Cavity
