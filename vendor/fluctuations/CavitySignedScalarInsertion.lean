module

public import CavityAttachmentCoordinateProjection
public import CavityCutErrorMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal

def siteRestKernel (n : ℕ) (A : ℕ→Spin n→Spin n→ℝ)
    (j : ℕ) (σ τ : Spin n×Bool) : ℝ :=
  spinValue σ.2*spinValue τ.2*A j σ.1 τ.1

def restHighKernel (n U : ℕ) (b h K : ℕ→ℝ) (j : ℕ) (σ τ : Spin n) : ℝ :=
  if j<U then 0 else h j+b j*((∑ i, spinValue (σ i)*spinValue (τ i))/(n+1:ℕ))-K j

theorem siteRestKernel_eq_cut_high (n U : ℕ) (b h K : ℕ→ℝ) :
    siteRestKernel n (restHighKernel n U b h K)=
      ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) := by
  funext j σ τ
  rw [cutTSlope_zero_covariance]
  by_cases hj : j<U
  · simp [siteRestKernel,restHighKernel,hj]
  · simp only [siteRestKernel,restHighKernel,hj,ite_false]
    congr 2
    simp [deletedOverlap,joinSpin]

def insertedRestTest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : T.cavityLeft.Assignment→ℝ)
    (A : ℕ→Spin n→Spin n→ℝ) (p : ClockTree.MarkedPlacement T)
    (r : ClockTree.MarkedPlacement p.tree) (τ : r.tree.cavityLeft.Assignment) : ℝ :=
  P (p.restRestrict (r.restRestrict τ))*
    A (r.tree.splitIndex (r.embed p.mark) r.mark)
      (p.restSpin (r.restRestrict τ)) (r.restSpin τ)

def insertedSiteSlots {S : Type*} {as : List PositiveMass} {T : ClockTree S as}
    (es : List T.Slot) (p : ClockTree.MarkedPlacement T)
    (r : ClockTree.MarkedPlacement p.tree) : List r.tree.Slot :=
  es.map (fun s=>r.embed (p.embed s))++[r.embed p.mark,r.mark]

theorem siteMonomial_marked_restrict {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (p : ClockTree.MarkedPlacement T)
    (es : List T.Slot) (σ : p.tree.Assignment) :
    siteMonomial T (p.restrict σ) es=siteMonomial p.tree σ (es.map p.embed) := by
  induction es with
  | nil => rfl
  | cons s es ih => simp only [siteMonomial,List.map_cons,p.restrict_at,ih]

theorem siteMonomial_append {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (σ : T.Assignment) (es fs : List T.Slot) :
    siteMonomial T σ (es++fs)=siteMonomial T σ es*siteMonomial T σ fs := by
  induction es with
  | nil => simp [siteMonomial]
  | cons s es ih => simp only [List.cons_append,siteMonomial,ih]; ring

theorem profilePairTest_eq_rest_scalar {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : T.cavityLeft.Assignment→ℝ)
    (A : ℕ→Spin n→Spin n→ℝ) (es : List T.Slot)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (σ : r.tree.Assignment) :
    ClockTree.profilePairTest (fun τ=>P (T.cavityAssignment τ).1*siteMonomial T τ es)
      (siteRestKernel n A) p r σ =
      insertedRestTest P A p r (r.tree.cavityAssignment σ).1*
        siteMonomial r.tree σ (insertedSiteSlots es p r) := by
  have hp:=p.restSpin_actual (r.restrict σ)
  have hr:=r.restSpin_actual σ
  rw [r.restRestrict_actual] at hp
  simp only [p.spin_at,r.restrict_at] at hp
  simp only [r.spin_at] at hr
  simp only [ClockTree.profilePairTest,siteRestKernel,insertedRestTest,
    insertedSiteSlots,siteMonomial_append,siteMonomial_marked_restrict,List.map_map,
    Function.comp_def,siteMonomial,p.spin_at,r.spin_at,r.restrict_at,
    ClockTree.MarkedPlacement.restRestrict_actual,
    ClockTree.MarkedPlacement.restSpin_actual]
  rw [hp,hr]
  ring

theorem inserted_full_expect_eq_scalar_coefficient (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℕ→Spin n→Spin n→ℝ) (es : List T.Slot)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) :
    r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (ClockTree.profilePairTest (fun τ=>P (T.cavityAssignment τ).1*siteMonomial T τ es)
        (siteRestKernel n A) p r) 0 =
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P A p r) 0*
      fullScalarCutMoment r.tree U K (insertedSiteSlots es p r) := by
  have he : ClockTree.profilePairTest
      (fun τ=>P (T.cavityAssignment τ).1*siteMonomial T τ es) (siteRestKernel n A) p r =
      (fun σ=>insertedRestTest P A p r (r.tree.cavityAssignment σ).1*
        siteMonomial r.tree σ (insertedSiteSlots es p r)) := by
    funext σ
    exact profilePairTest_eq_rest_scalar P A es p r σ
  rw [he]
  exact cut_full_monomial_eq_retained n q U b h K r.tree ho _ _

theorem actual_site_rest_jet_eq_signed_scalar_sum (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (A : ℕ→Spin n→Spin n→ℝ) (es : List T.Slot) :
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 [siteRestKernel n A] T
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) =
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P A p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum)).sum/2 := by
  simp only [ClockTree.disorderProfileJets,
    inserted_full_expect_eq_scalar_coefficient n q U b h K T ho]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  ring

theorem actual_high_jet_eq_signed_scalar_sum (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0
      [ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K)] T
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) =
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots es p r))).sum)).sum/2 := by
  rw [←siteRestKernel_eq_cut_high]
  simp only [ClockTree.disorderProfileJets,
    inserted_full_expect_eq_scalar_coefficient n q U b h K T ho]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  ring

end OAI.SKFluctuations.Cavity
