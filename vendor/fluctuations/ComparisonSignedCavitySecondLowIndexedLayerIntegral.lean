module

public import ComparisonSignedCavitySecondLowIndexedLayerCloneGram

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_scalar_indexed_incoming_layer_clone_gram_sq_le {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (cut : ℕ) {a v z : ℝ} (ho : MassOrdered a as) (hav : a ≤ v) (hcut : cut ≤ as.length)
    (q : ℕ→ι→ℝ≥0) (hp : ∀st∈(clockSteps as q).take cut,st.1 ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment→ℝ) (F : S→ℝ) (μ : Measure (ι→ℝ)) [IsProbabilityMeasure μ] :
    (∫x,nativeScalarIndexedCutLayerFold w φ T cut a v z q P F x ∂μ)^2 ≤
      (3*(T.leaves:ℝ)*v)^2*(∫x,nativeRetainedOldCloneSquareSum T w φ cut q P x ∂μ)*
        (∫x,nativeRetainedNewCloneSquareSum T w φ cut q F x ∂μ) := by
  have hIP : Integrable (nativeRetainedOldCloneSquareSum T w φ cut q P) μ := by
    simpa only [zero_add] using
      (nativeRetainedOldCloneSquareSum_smooth0 T hw φ ho cut q P).integrable_zero_shift (ν:=μ) 0
  have hIF : Integrable (nativeRetainedNewCloneSquareSum T w φ cut q F) μ := by
    simpa only [zero_add] using
      (nativeRetainedNewCloneSquareSum_smooth0 T hw φ ho cut q F).integrable_zero_shift (ν:=μ) 0
  have hIL : Integrable (nativeScalarIndexedCutLayerFold w φ T cut a v z q P F) μ := by
    simpa only [zero_add] using
      (nativeScalarIndexedCutLayerFold_smooth0 T hw φ cut ho hcut q hp hvz P F).integrable_zero_shift (ν:=μ) 0
  apply actual_original_root_gram_sq_le μ hIP hIF hIL
  · exact nativeRetainedOldCloneSquareSum_nonneg T hw φ ho cut q P
  · exact nativeRetainedNewCloneSquareSum_nonneg T hw φ ho cut q F
  · exact native_scalar_indexed_cut_layer_clone_gram_sq_le T hw φ cut ho hav hcut q hp hvz hz P F

def nativeExteriorIndexedCutLayer {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (a v z : ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (F : Ei.Assignment→Es.Assignment→S→ℝ) (y : (ι→ℝ)×(ι→ℝ)) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>
    nativeScalarIndexedCutLayerFold w φ D cut a v z qs (P η ζ) (F η ζ) y.2) y.2) y.1

def nativeExteriorIndexedOldCloneSquareSum {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (y : (ι→ℝ)×(ι→ℝ)) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>
    nativeRetainedOldCloneSquareSum D w φ cut qs (P η ζ) y.2) y.2) y.1

def nativeExteriorIndexedNewCloneSquareSum {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) (qi qs : ℕ→ι→ℝ≥0)
    (F : Ei.Assignment→Es.Assignment→S→ℝ) (y : (ι→ℝ)×(ι→ℝ)) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>
    nativeRetainedNewCloneSquareSum D w φ cut qs (F η ζ) y.2) y.2) y.1

private theorem indexed_exterior_expect_gram {as : List PositiveMass} (E : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (A B C : E.Assignment→ℝ) (k : ℝ) (hA : ∀e,0 ≤ A e) (hB : ∀e,0 ≤ B e)
    (hC : ∀e,(C e)^2 ≤ k^2*A e*B e) (x : ι→ℝ) :
    (E.expect w φ q C x)^2 ≤ k^2*E.expect w φ q A x*E.expect w φ q B x := by
  classical
  simp_rw [E.expect_realize w φ q]
  exact actualExterior_expect_gram_sq_le hw φ (E.realize q) (clockSteps_ordered ho q)
    (fun e=>A ((E.assignmentEquiv q).symm e)) (fun e=>B ((E.assignmentEquiv q).symm e))
    (fun e=>C ((E.assignmentEquiv q).symm e)) k
    (fun e=>hA _) (fun e=>hB _) (fun e=>hC _) x

private theorem indexed_exterior_expect_nonneg {as : List PositiveMass} (E : ClockTree S as)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (P : E.Assignment→ℝ) (hP : ∀e,0 ≤ P e) (x : ι→ℝ) :
    0 ≤ E.expect w φ q P x := by
  rw [E.expect_realize]
  exact (E.realize q).expect_nonneg hw φ (clockSteps_ordered ho q) (fun _=>hP _) x

private theorem indexed_exterior_smooth_joint {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es : ClockTree S sas) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {ai ast : ℝ} (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (qi qs : ℕ→ι→ℝ≥0) (G : Ei.Assignment→Es.Assignment→(ι→ℝ)→ℝ)
    (hG : ∀η ζ,BddSmooth 0 (G η ζ)) :
    BddSmooth 0 (fun y : (ι→ℝ)×(ι→ℝ)=>
      Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>G η ζ y.2) y.2) y.1) := by
  unfold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  apply ((Ei.weight_smooth hw φ hoi qi η 0).compCLM
    (ContinuousLinearMap.fst ℝ (ι→ℝ) (ι→ℝ))).mul
  apply BddSmooth.sum Finset.univ
  intro ζ _
  exact ((Es.weight_smooth hw φ hos qs ζ 0).compCLM
    (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ))).mul
      ((hG η ζ).compCLM (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ)))

theorem native_exterior_indexed_incoming_layer_clone_gram_sq_le {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) {ai a v z : ℝ}
    (hoi : MassOrdered ai ias) (ho : MassOrdered a sas) (hav : a ≤ v) (hcut : cut ≤ sas.length)
    (qi qs : ℕ→ι→ℝ≥0) (hp : ∀st∈(clockSteps sas qs).take cut,st.1 ≤ v)
    (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (F : Ei.Assignment→Es.Assignment→S→ℝ)
    (μ : Measure ((ι→ℝ)×(ι→ℝ))) [IsProbabilityMeasure μ] :
    (∫y,nativeExteriorIndexedCutLayer Ei Es D w φ cut a v z qi qs P F y ∂μ)^2 ≤
      (3*(D.leaves:ℝ)*v)^2*
        (∫y,nativeExteriorIndexedOldCloneSquareSum Ei Es D w φ cut qi qs P y ∂μ)*
        (∫y,nativeExteriorIndexedNewCloneSquareSum Ei Es D w φ cut qi qs F y ∂μ) := by
  let A := nativeExteriorIndexedOldCloneSquareSum Ei Es D w φ cut qi qs P
  let B := nativeExteriorIndexedNewCloneSquareSum Ei Es D w φ cut qi qs F
  let C := nativeExteriorIndexedCutLayer Ei Es D w φ cut a v z qi qs P F
  have hAs : BddSmooth 0 A := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs _
    (fun η ζ=>nativeRetainedOldCloneSquareSum_smooth0 D hw φ ho cut qs (P η ζ))
  have hBs : BddSmooth 0 B := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs _
    (fun η ζ=>nativeRetainedNewCloneSquareSum_smooth0 D hw φ ho cut qs (F η ζ))
  have hCs : BddSmooth 0 C := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs _
    (fun η ζ=>nativeScalarIndexedCutLayerFold_smooth0 D hw φ cut ho hcut qs hp hvz (P η ζ) (F η ζ))
  have hIP : Integrable A μ := by simpa only [zero_add] using hAs.integrable_zero_shift (ν:=μ) 0
  have hIF : Integrable B μ := by simpa only [zero_add] using hBs.integrable_zero_shift (ν:=μ) 0
  have hIL : Integrable C μ := by simpa only [zero_add] using hCs.integrable_zero_shift (ν:=μ) 0
  have hA : ∀y,0 ≤ A y := fun y=>indexed_exterior_expect_nonneg Ei hw φ hoi qi _
    (fun η=>indexed_exterior_expect_nonneg Es hw φ ho qs _
      (fun ζ=>nativeRetainedOldCloneSquareSum_nonneg D hw φ ho cut qs (P η ζ) y.2) y.2) y.1
  have hB : ∀y,0 ≤ B y := fun y=>indexed_exterior_expect_nonneg Ei hw φ hoi qi _
    (fun η=>indexed_exterior_expect_nonneg Es hw φ ho qs _
      (fun ζ=>nativeRetainedNewCloneSquareSum_nonneg D hw φ ho cut qs (F η ζ) y.2) y.2) y.1
  apply actual_original_root_gram_sq_le μ hIP hIF hIL hA hB
  intro y
  apply indexed_exterior_expect_gram Ei hw φ hoi qi _ _ _ _
  · intro η
    exact indexed_exterior_expect_nonneg Es hw φ ho qs _
      (fun ζ=>nativeRetainedOldCloneSquareSum_nonneg D hw φ ho cut qs (P η ζ) y.2) y.2
  · intro η
    exact indexed_exterior_expect_nonneg Es hw φ ho qs _
      (fun ζ=>nativeRetainedNewCloneSquareSum_nonneg D hw φ ho cut qs (F η ζ) y.2) y.2
  · intro η
    exact indexed_exterior_expect_gram Es hw φ ho qs _ _ _ _
      (fun ζ=>nativeRetainedOldCloneSquareSum_nonneg D hw φ ho cut qs (P η ζ) y.2)
      (fun ζ=>nativeRetainedNewCloneSquareSum_nonneg D hw φ ho cut qs (F η ζ) y.2)
      (fun ζ=>native_scalar_indexed_cut_layer_clone_gram_sq_le D hw φ cut ho hav hcut qs hp hvz hz (P η ζ) (F η ζ) y.2) y.2

theorem native_exterior_indexed_incoming_layer_clone_gram_sq_le_map
    {κ : Type} [MeasurableSpace κ] {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) {ai a v z : ℝ}
    (hoi : MassOrdered ai ias) (ho : MassOrdered a sas) (hav : a ≤ v) (hcut : cut ≤ sas.length)
    (qi qs : ℕ→ι→ℝ≥0) (hp : ∀st∈(clockSteps sas qs).take cut,st.1 ≤ v)
    (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (F : Ei.Assignment→Es.Assignment→S→ℝ)
    (μ : Measure κ) [IsProbabilityMeasure μ]
    (ρ : κ→((ι→ℝ)×(ι→ℝ))) (hρ : Measurable ρ) :
    (∫r,nativeExteriorIndexedCutLayer Ei Es D w φ cut a v z qi qs P F (ρ r) ∂μ)^2 ≤
      (3*(D.leaves:ℝ)*v)^2*
        (∫r,nativeExteriorIndexedOldCloneSquareSum Ei Es D w φ cut qi qs P (ρ r) ∂μ)*
        (∫r,nativeExteriorIndexedNewCloneSquareSum Ei Es D w φ cut qi qs F (ρ r) ∂μ) := by
  have : IsProbabilityMeasure (μ.map ρ) :=
    (Measure.isProbabilityMeasure_map_iff hρ.aemeasurable).2 inferInstance
  have H := native_exterior_indexed_incoming_layer_clone_gram_sq_le Ei Es D hw φ cut
    hoi ho hav hcut qi qs hp hvz hz P F (μ.map ρ)
  have hAs := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs
    (fun η ζ=>nativeRetainedOldCloneSquareSum D w φ cut qs (P η ζ))
    (fun η ζ=>nativeRetainedOldCloneSquareSum_smooth0 D hw φ ho cut qs (P η ζ))
  have hBs := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs
    (fun η ζ=>nativeRetainedNewCloneSquareSum D w φ cut qs (F η ζ))
    (fun η ζ=>nativeRetainedNewCloneSquareSum_smooth0 D hw φ ho cut qs (F η ζ))
  have hCs := indexed_exterior_smooth_joint Ei Es hw φ hoi ho qi qs
    (fun η ζ=>nativeScalarIndexedCutLayerFold w φ D cut a v z qs (P η ζ) (F η ζ))
    (fun η ζ=>nativeScalarIndexedCutLayerFold_smooth0 D hw φ cut ho hcut qs hp hvz (P η ζ) (F η ζ))
  dsimp only [nativeExteriorIndexedCutLayer, nativeExteriorIndexedOldCloneSquareSum,
    nativeExteriorIndexedNewCloneSquareSum] at H ⊢
  rw [integral_map hρ.aemeasurable hCs.continuous.aestronglyMeasurable,
    integral_map hρ.aemeasurable hAs.continuous.aestronglyMeasurable,
    integral_map hρ.aemeasurable hBs.continuous.aestronglyMeasurable] at H
  exact H

end OAI.SKFluctuations.Cavity
