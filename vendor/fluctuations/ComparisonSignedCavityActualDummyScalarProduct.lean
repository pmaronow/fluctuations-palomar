module

public import ComparisonSignedCavityActualDummyScalarTree

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 8000000

theorem native_dummy_baseline_product_on_tree (n : ℕ) {as : List PositiveMass}
    (R : ClockTree ((Spin n×Bool)×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) (P : R.cavityLeft.Assignment→ℝ) (Q : R.cavityRight.Assignment→ℝ) :
    R.disorderExpect (nativeDummyWeight n) (nativeDummyFeature n) (nativeDummyRoot v)
      (nativeDummyClock q U K)
      (fun σ=>P (R.cavityAssignment σ).1*Q (R.cavityAssignment σ).2) (nativeDummyField x)=
    R.cavityLeft.disorderExpect (fullWeight n) (fullFeature n) v q P x*
      R.cavityRight.disorderExpect (fun _ : Bool=>(1/2:ℝ)) scalarFeature 0
        (fun j _=>relocatedClock U 0 K j) Q 0 := by
  unfold nativeDummyRoot nativeDummyClock nativeDummyField
  rw [R.disorderExpect_zeroRow]
  simp only [nativeDummyFeature_restrict]
  exact R.disorderExpect_cavity_product (v:=fun _ : Bool=>(1/2:ℝ))
    (fullWeight_pos n) (by intro s;norm_num)
    (fullFeature n) scalarFeature ho (Sum.elim v (fun _=>0))
      (fun j=>Sum.elim (q j) (fun _=>relocatedClock U 0 K j)) P Q (Sum.elim x (fun _=>0))

theorem native_dummy_baseline_product (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) (P : T.Assignment→ℝ) (Q : T.cavityRight.Assignment→ℝ) :
    T.withDummy.disorderExpect (nativeDummyWeight n) (nativeDummyFeature n) (nativeDummyRoot v)
      (nativeDummyClock q U K)
      (fun σ=>P (T.withDummyPhysical σ)*Q (T.withDummyScalar σ)) (nativeDummyField x)=
    T.disorderExpect (fullWeight n) (fullFeature n) v q P x*
      T.cavityRight.disorderExpect (fun _ : Bool=>(1/2:ℝ)) scalarFeature 0
        (fun j _=>relocatedClock U 0 K j) Q 0 := by
  have H:=native_dummy_baseline_product_on_tree n T.withDummy ho v q x U K
    (fun σ=>P (cast (congrArg ClockTree.Assignment T.withDummy_cavityLeft) σ))
    (fun σ=>Q (cast (congrArg ClockTree.Assignment T.withDummy_cavityRight) σ))
  rw [ClockTree.disorderExpect_cast_tree T.withDummy_cavityLeft,
    ClockTree.disorderExpect_cast_tree T.withDummy_cavityRight] at H
  exact H

def nativeDummyMonomial {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (σ : T.withDummy.Assignment) (es : List T.Slot) : ℝ :=
  T.withDummy.slotProduct (fun s=>spinValue s.2) σ (es.map T.withDummySlot)

theorem nativeDummyMonomial_eq_scalar {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (σ : T.withDummy.Assignment) (es : List T.Slot) :
    nativeDummyMonomial T σ es=
      T.cavityRight.slotProduct spinValue (T.withDummyScalar σ) (es.map T.cavityRightSlot) := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simpa only [nativeDummyMonomial,List.map_cons,ClockTree.slotProduct,
      T.withDummyScalar_atSlot] using (congrArg
        (fun z=>spinValue (T.withDummy.atSlot σ (T.withDummySlot e)).2*z) ih)

theorem native_dummy_baseline_monomial (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) (P : T.Assignment→ℝ) (es : List T.Slot) :
    T.withDummy.disorderExpect (nativeDummyWeight n) (nativeDummyFeature n) (nativeDummyRoot v)
      (nativeDummyClock q U K)
      (fun σ=>P (T.withDummyPhysical σ)*nativeDummyMonomial T σ es) (nativeDummyField x)=
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x*fullScalarCutMoment T U K es := by
  simp only [nativeDummyMonomial_eq_scalar]
  exact native_dummy_baseline_product n T ho v q x U K P
    (fun σ=>T.cavityRight.slotProduct spinValue σ (es.map T.cavityRightSlot))

theorem native_dummy_baseline_physical (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) (P : T.Assignment→ℝ) :
    T.withDummy.disorderExpect (nativeDummyWeight n) (nativeDummyFeature n) (nativeDummyRoot v)
      (nativeDummyClock q U K) (fun σ=>P (T.withDummyPhysical σ)) (nativeDummyField x)=
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x := by
  have H:=native_dummy_baseline_product n T ho v q x U K P (fun _=>1)
  rw [T.cavityRight.disorderExpect_one (by intro s;norm_num) scalarFeature ho] at H
  simpa only [mul_one] using H

end OAI.SKFluctuations.Cavity
