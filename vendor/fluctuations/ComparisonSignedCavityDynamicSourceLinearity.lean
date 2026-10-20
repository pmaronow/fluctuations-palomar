module

public import ComparisonSignedCavityDynamicProjectionAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {n a : ℕ} {pre mid tail : List PositiveMass}
  {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {s : T.cavityLeft.Slot}
  {G : ActualNaturalBoundaryShape n a T} {v : RestCoordinate n→ℝ}
  {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

def NativeDynamicCanonicalExteriorSource.rootTest
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    (J : (RestCoordinate n→ℝ)→T.cavityLeft.Assignment→ℝ)
    (z : ((RestCoordinate n→ℝ)×(RestCoordinate n→ℝ))×(RestCoordinate n→ℝ)) : ℝ :=
  nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight n) (restFeature n)
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
    (fun η ζ δ=>J (exteriorForestStarRoot z) (E.read η ζ δ))
    (exteriorForestIRoot z) (exteriorForestStarRoot z)

theorem NativeDynamicCanonicalExteriorSource.rootTest_integrable
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (J : (RestCoordinate n→ℝ)→T.cavityLeft.Assignment→ℝ)
    (hJ : ∀σ,BddSmooth 0 (fun y=>J y σ)) :
    Integrable (E.rootTest J)
      (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) := by
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho v q x
  have H:=native_dynamic_exterior_test_smooth 0 E.Ei E.Es E.D
    ho.suffix_end ho.suffix_end.suffix_end (restWeight_pos n) (restFeature n)
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
    (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
    (fun z η ζ δ=>J z.2 (E.read η ζ δ))
    (fun η ζ δ=>(hJ (E.read η ζ δ)).compCLM
      (ContinuousLinearMap.snd ℝ (RestCoordinate n→ℝ) (RestCoordinate n→ℝ)))
  exact H.integrable_comp_measurable
    (departedAnchorTargetRoot_measurable.prodMk departedAnchorExteriorRoot_measurable)

theorem NativeDynamicCanonicalExteriorSource.mean_zero
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x) :
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q (fun _ _=>0) x=0 := by
  rw [E.star_field_law _ (fun _=>BddSmooth.const 0 0)]
  simp only [nativeExteriorForestConditionalTest,nativeExteriorForestMean,ClockTree.expect,
    mul_zero,Finset.sum_const_zero,integral_zero]

theorem NativeDynamicCanonicalExteriorSource.mean_add
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (J K : (RestCoordinate n→ℝ)→T.cavityLeft.Assignment→ℝ)
    (hJ : ∀σ,BddSmooth 0 (fun y=>J y σ)) (hK : ∀σ,BddSmooth 0 (fun y=>K y σ)) :
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q (fun y σ=>J y σ+K y σ) x=
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q J x+
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q K x := by
  rw [E.star_field_law _ (fun σ=>(hJ σ).add (hK σ)),E.star_field_law J hJ,E.star_field_law K hK]
  change (∫z,E.rootTest (fun y σ=>J y σ+K y σ) z ∂_)=
    (∫z,E.rootTest J z ∂_)+(∫z,E.rootTest K z ∂_)
  rw [←integral_add (E.rootTest_integrable ho J hJ) (E.rootTest_integrable ho K hK)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp only [rootTest,nativeExteriorForestConditionalTest,nativeExteriorForestMean,ClockTree.expect,
    mul_add,Finset.sum_add_distrib]

theorem NativeDynamicCanonicalExteriorSource.mean_sum
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {κ : Type} (I : Finset κ) (J : κ→(RestCoordinate n→ℝ)→T.cavityLeft.Assignment→ℝ)
    (hJ : ∀i∈I,∀σ,BddSmooth 0 (fun y=>J i y σ)) :
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q (fun y σ=>∑i∈I,J i y σ) x=
      ∑i∈I,nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q (J i) x := by
  rw [E.star_field_law _ (fun σ=>BddSmooth.sum I (fun i hi=>hJ i hi σ))]
  symm
  calc
    _=∑i∈I,∫z,E.rootTest (J i) z
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact E.star_field_law (J i) (hJ i hi)
    _=_:=by
      rw [←integral_finsetSum I (fun i hi=>E.rootTest_integrable ho (J i) (hJ i hi))]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      change (∑i∈I,E.rootTest (J i) z)=E.rootTest (fun y σ=>∑i∈I,J i y σ) z
      unfold rootTest nativeExteriorForestConditionalTest nativeExteriorForestMean ClockTree.expect
      simp only [Finset.mul_sum]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _=>
        Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _=>Finset.sum_comm))))

end OAI.SKFluctuations.Cavity
