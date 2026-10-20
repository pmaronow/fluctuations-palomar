module

public import CavityRetainedConnectedInsertion
public import CavityActualFrozenInsertion

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal

def restLowKernel (n U : ℕ) (b h : ℕ→ℝ) (j : ℕ) (σ τ : Spin n) : ℝ :=
  if j<U then h j+b j*((∑ i, spinValue (σ i)*spinValue (τ i))/(n+1:ℕ)) else 0

theorem siteRestKernel_eq_cut_low (n U : ℕ) (b h K : ℕ→ℝ) :
    siteRestKernel n (restLowKernel n U b h)=
      ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) := by
  funext j σ τ
  rw [coordinateProfile_eq_rowCovarianceKernel]
  by_cases hj : j<U
  · have he : fullVariance n 0 1 (b j) (h j) (K j)=
        rowInterpolationSlope n (b j) (h j) 0 := by
      funext i
      rcases i with (i|i)|(i|i) <;>
        simp [fullVariance,rowInterpolationSlope]
    simp only [cutLSlope,hj,ite_true,he]
    rw [rowInterpolationSlope_covariance]
    simp only [siteRestKernel,restLowKernel,hj,ite_true,sub_zero]
    congr 2
    simp [deletedOverlap,joinSpin]
  · simp only [cutLSlope,hj,ite_false,siteRestKernel,restLowKernel,
      mul_zero,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

def retainedSignedJets (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) :
    (As : List (ℕ→Spin n→Spin n→ℝ)) → {as : List PositiveMass} →
      (T : ClockTree (Spin n×Bool) as) → (T.cavityLeft.Assignment→ℝ) →
      List T.Slot → ℝ
  | [], _, T, P, es =>
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
      fullScalarCutMoment T U K es
  | A::As, _, T, P, es =>
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        retainedSignedJets n q U b h K As r.tree (insertedRestTest P A p r)
          (insertedSiteSlots es p r))).sum)).sum/2

theorem actual_site_rest_jets_eq_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (As : List (ℕ→Spin n→Spin n→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 (As.map (siteRestKernel n)) T
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es)=
        retainedSignedJets n q U b h K As T P es := by
  induction As generalizing T with
  | nil =>
    exact cut_full_monomial_eq_retained n q U b h K T ho P es
  | cons A As ih =>
    simp only [List.map_cons,ClockTree.disorderProfileJets,retainedSignedJets]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    congr 1
    have he : ClockTree.profilePairTest
        (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) (siteRestKernel n A) p r =
        (fun σ=>insertedRestTest P A p r (r.tree.cavityAssignment σ).1*
          siteMonomial r.tree σ (insertedSiteSlots es p r)) := by
      funext σ
      exact profilePairTest_eq_rest_scalar P A es p r σ
    rw [he]
    exact ih r.tree (insertedRestTest P A p r) (insertedSiteSlots es p r)

theorem actual_frozen_coefficient_eq_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot)
    (hq0 : ∀ j i, 0≤q j i) (hq : ∀ i, Monotone (fun j=>q j i))
    (hb : ∀ j, 0≤b j) (hh : ∀ j, 0≤h j) (hK : ∀ j, 0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (k r : ℕ) :
    cutFrozenLowHighJet n q U b h K T
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) 0 k r 0 =
      retainedSignedJets n q U b h K
        (List.replicate k (restLowKernel n U b h)++
          List.replicate r (restHighKernel n U b h K)) T P es := by
  rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho _ 0 hq0 hq hb hh hK
    hbm hhm hKm k r (by norm_num : (0:ℝ) ∈ Icc 0 1)]
  rw [←siteRestKernel_eq_cut_low,←siteRestKernel_eq_cut_high]
  have hm : (List.replicate k (restLowKernel n U b h)++
      List.replicate r (restHighKernel n U b h K)).map (siteRestKernel n)=
      List.replicate k (siteRestKernel n (restLowKernel n U b h))++
        List.replicate r (siteRestKernel n (restHighKernel n U b h K)) := by
    simp only [List.map_append,List.map_replicate]
  rw [←hm]
  exact actual_site_rest_jets_eq_retained n q U b h K _ T ho P es

end OAI.SKFluctuations.Cavity
