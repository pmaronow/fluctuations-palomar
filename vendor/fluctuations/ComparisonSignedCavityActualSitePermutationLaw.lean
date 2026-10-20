module

public import ComparisonSignedCavityActualSitePermutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Fintype ι]

theorem native_expect_gauge
    (L : (ι→ℝ)≃L[ℝ](ι→ℝ)) (π : S≃S)
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ}
    (hw : ∀s,w (π s)=w s) (hφ : ∀s x,φ (π s) (L x)=φ s x)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (hL : ∀j,MeasurePreserving L (Measure.pi fun i=>gaussianReal 0 (q j i))
      (Measure.pi fun i=>gaussianReal 0 (q j i)))
    (P : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q P (L x)=T.expect w φ q (fun σ=>P (T.assignmentGauge π σ)) x := by
  unfold expect
  rw [←(T.assignmentGauge π).sum_comp]
  simp_rw [T.weight_gauge L π hw hφ q hL]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_actual_site_permutation_law
    {n : ℕ} (π : Fin n≃Fin n) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (P : T.Assignment→ℝ) :
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h) P 0=
      T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
        (fun σ=>P (T.assignmentGauge (nativeSiteSpinPerm π) σ)) 0 := by
  let L:=coordinateEquiv (nativeSiteFeaturePerm π)
  let q:=physicalCompletedClock n b h
  let qi:=cumulativeIncrements (q 0) (fun j=>q (j+1))
  let ν:=Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))
  have hq (j : ℕ) (i : FeatureIndex n) : q j (nativeSiteFeaturePerm π i)=q j i :=
    nativeSiteFeaturePerm_physicalClock π b h j i
  have hqi (j : ℕ) (i : FeatureIndex n) : qi j (nativeSiteFeaturePerm π i)=qi j i := by
    cases j <;> simp only [qi,cumulativeIncrements,hq]
  have HL : MeasurePreserving L ν ν := nativeSiteFeaturePerm_gaussian π _ (by intro i;rw [hq])
  have HLi (j : ℕ) : MeasurePreserving L (Measure.pi fun i=>gaussianReal 0 (qi j i))
      (Measure.pi fun i=>gaussianReal 0 (qi j i)) := nativeSiteFeaturePerm_gaussian π _ (hqi j)
  have HE (x : FeatureIndex n→ℝ) :
      T.expect (uniformWeight n) (finiteFeature n) qi P (L x)=
      T.expect (uniformWeight n) (finiteFeature n) qi
        (fun σ=>P (T.assignmentGauge (nativeSiteSpinPerm π) σ)) x :=
    T.native_expect_gauge L (nativeSiteSpinPerm π) (fun _=>rfl)
      (finiteFeature_nativeSitePerm π) qi HLi P x
  rw [T.disorderExpect_integral (uniformWeight_pos n) (finiteFeature n) ho,
    T.disorderExpect_integral (uniformWeight_pos n) (finiteFeature n) ho]
  simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
  change (∫x,T.expect (uniformWeight n) (finiteFeature n) qi P x ∂ν)=
    ∫x,T.expect (uniformWeight n) (finiteFeature n) qi
      (fun σ=>P (T.assignmentGauge (nativeSiteSpinPerm π) σ)) x ∂ν
  rw [←HL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  simp_rw [HE]

theorem native_actual_null_completed_site_permutation_law
    {n : ℕ} (π : Fin n≃Fin n) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (P : T.Assignment→ℝ) :
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (nullCompletedClock n b h) P 0=
      T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (nullCompletedClock n b h)
        (fun σ=>P (T.assignmentGauge (nativeSiteSpinPerm π) σ)) 0 := by
  rw [completed_scalar_expect_eq n T ho b h P,
    completed_scalar_expect_eq n T ho b h (fun σ=>P (T.assignmentGauge (nativeSiteSpinPerm π) σ))]
  exact native_actual_site_permutation_law π T ho b h P

end OAI.SKFluctuations.Cavity
