module

public import ComparisonSignedCavitySecondLowIndexedPrefixTelescope

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeExteriorCompleteCFold {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (c : D.Slot) (U : ℕ) (a : ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) (y : (ι→ℝ)×(ι→ℝ)) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>
    nativeSecondLowCCouplingFold w φ D c U a qs (P η ζ) (.fixed (f η ζ)) (.fixed (z η ζ)) Q y.2) y.2) y.1

def nativeExteriorRetainedCProductCovariance {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (c : D.Slot) (U : ℕ) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ) (y : (ι→ℝ)×(ι→ℝ)) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (fun ζ=>nativeRetainedCloneCutMean w φ D c U qs
    (fun δ δ'=>(P η ζ δ-P η ζ δ')*
      (Q (f η ζ) (D.atSlot δ c) (z η ζ)-Q (f η ζ) (D.atSlot δ' c) (z η ζ))) y.2) y.2) y.1

omit [Nonempty S] in
private theorem telescope_expect_sub {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P Q : T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>P σ-Q σ) x=T.expect w φ q P x-T.expect w φ q Q x := by
  simp only [ClockTree.expect,mul_sub,Finset.sum_sub_distrib]

omit [Nonempty S] in
private theorem telescope_expect_scale {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (c : ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>c*P σ) x=c*T.expect w φ q P x := by
  simp only [ClockTree.expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [Nonempty S] in
private theorem telescope_expect_sum {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    {J : Type} (js : Finset J) (P : J→T.Assignment→ℝ) (x : ι→ℝ) :
    T.expect w φ q (fun σ=>∑j∈js,P j σ) x=∑j∈js,T.expect w φ q (P j) x := by
  simp only [ClockTree.expect,Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem telescope_exterior_smooth_joint {ias sas : List PositiveMass}
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

theorem nativeExteriorIndexedCutLayer_integrable_map
    {κ : Type} [MeasurableSpace κ] {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (cut : ℕ) {ai a : ℝ}
    (hoi : MassOrdered ai ias) (ho : MassOrdered a sas) (v z : ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (F : Ei.Assignment→Es.Assignment→S→ℝ)
    (μ : Measure κ) [IsFiniteMeasure μ] (ρ : κ→((ι→ℝ)×(ι→ℝ))) (hρ : Measurable ρ) :
    Integrable (fun r=>nativeExteriorIndexedCutLayer Ei Es D w φ cut a v z qi qs P F (ρ r)) μ := by
  have H := telescope_exterior_smooth_joint Ei Es hw φ hoi ho qi qs _
    (fun η ζ=>nativeScalarIndexedCutLayerFold_virtual_smooth0 D hw φ cut ho v z qs (P η ζ) (F η ζ))
  obtain ⟨K,_,Hbound⟩:=H.bound
  apply Integrable.of_bound (H.continuous.measurable.comp hρ).aestronglyMeasurable K
  exact Eventually.of_forall fun r=>Hbound _

theorem nativeExteriorRetainedCProductCovariance_integrable_map
    {κ : Type} [MeasurableSpace κ] {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (c : D.Slot) (U : ℕ) {ai a : ℝ}
    (hoi : MassOrdered ai ias) (ho : MassOrdered a sas) (qi qs : ℕ→ι→ℝ≥0)
    (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ)
    (μ : Measure κ) [IsFiniteMeasure μ] (ρ : κ→((ι→ℝ)×(ι→ℝ))) (hρ : Measurable ρ) :
    Integrable (fun r=>nativeExteriorRetainedCProductCovariance Ei Es D w φ c U qi qs P f z Q (ρ r)) μ := by
  have H := telescope_exterior_smooth_joint Ei Es hw φ hoi ho qi qs _
    (fun η ζ=>nativeRetainedCloneCutMean_smooth0 D hw φ ho c U qs
      (fun δ δ'=>(P η ζ δ-P η ζ δ')*
        (Q (f η ζ) (D.atSlot δ c) (z η ζ)-Q (f η ζ) (D.atSlot δ' c) (z η ζ))))
  obtain ⟨K,_,Hbound⟩:=H.bound
  apply Integrable.of_bound (H.continuous.measurable.comp hρ).aestronglyMeasurable K
  exact Eventually.of_forall fun r=>Hbound _

theorem native_exterior_complete_c_fold_eq_grouped_indexed_layers_sub_covariance
    {ias sas : List PositiveMass} (Ei : ClockTree S ias) (Es D : ClockTree S sas) (c : D.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (U : ℕ) {a : ℝ}
    (ho : MassOrdered a sas) (hblock : ∀d:D.Slot,U ≤ D.splitIndex c d)
    (qi qs : ℕ→ι→ℝ≥0) (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ)
    (cuts : ℕ→ℝ) (count : ℕ) (index : ℕ→ℕ)
    (hfirst : cuts 0=partitionPoint a sas U/2) (hlast : cuts count=1) (hindex0 : index 0=U)
    (hindex : ∀j < count,index j ≤ sas.length)
    (hprefix : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps sas qs).take (index j),st.1 ≤ cuts j)
    (hsource : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps sas qs).take U,st.1 ≤ cuts j)
    (hmono : ∀j < count,cuts j ≤ cuts (j+1)) (y : (ι→ℝ)×(ι→ℝ)) :
    nativeExteriorCompleteCFold Ei Es D w φ c U a qi qs P f z Q y=
      (∑j∈Finset.range count,nativeExteriorIndexedCutLayer Ei Es D w φ (index j) 0 (cuts j) (cuts (j+1))
        qi qs P (fun η ζ s=>Q (f η ζ) s (z η ζ)) y)-
        (partitionPoint a sas U/2)*nativeExteriorRetainedCProductCovariance Ei Es D w φ c U qi qs P f z Q y := by
  let v:=partitionPoint a sas U/2
  let L:=fun j η ζ=>nativeScalarIndexedCutLayerFold w φ D (index j) 0 (cuts j) (cuts (j+1))
    qs (P η ζ) (fun s=>Q (f η ζ) s (z η ζ)) y.2
  let C:=fun η ζ=>nativeRetainedCloneCutMean w φ D c U qs
    (fun δ δ'=>(P η ζ δ-P η ζ δ')*
      (Q (f η ζ) (D.atSlot δ c) (z η ζ)-Q (f η ζ) (D.atSlot δ' c) (z η ζ))) y.2
  have H : (fun η=>Es.expect w φ qs (fun ζ=>nativeSecondLowCCouplingFold w φ D c U a qs (P η ζ)
      (.fixed (f η ζ)) (.fixed (z η ζ)) Q y.2) y.2)=
      fun η=>(∑j∈Finset.range count,Es.expect w φ qs (L j η) y.2)-v*Es.expect w φ qs (C η) y.2 := by
    funext η
    have HE : (fun ζ=>nativeSecondLowCCouplingFold w φ D c U a qs (P η ζ)
        (.fixed (f η ζ)) (.fixed (z η ζ)) Q y.2)=
        fun ζ=>(∑j∈Finset.range count,L j η ζ)-v*C η ζ := by
      funext ζ
      exact native_second_low_complete_c_fold_eq_grouped_indexed_layers_sub_retained_covariance
        D c hw φ U ho hblock qs (P η ζ) (f η ζ) (z η ζ) Q cuts count index hfirst hlast hindex0
        hindex hprefix hsource hmono y.2
    rw [HE,telescope_expect_sub,telescope_expect_scale,telescope_expect_sum]
  unfold nativeExteriorCompleteCFold
  rw [H,telescope_expect_sub,telescope_expect_scale,telescope_expect_sum]
  rfl

theorem native_exterior_incoming_complete_c_fold_eq_grouped_indexed_layers_sub_covariance
    {κ : Type} [MeasurableSpace κ] {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (c : D.Slot)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (U : ℕ) {ai a : ℝ}
    (hoi : MassOrdered ai ias) (ho : MassOrdered a sas) (hblock : ∀d:D.Slot,U ≤ D.splitIndex c d)
    (qi qs : ℕ→ι→ℝ≥0) (P : Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (f z : Ei.Assignment→Es.Assignment→S) (Q : S→S→S→ℝ)
    (cuts : ℕ→ℝ) (count : ℕ) (index : ℕ→ℕ)
    (hfirst : cuts 0=partitionPoint a sas U/2) (hlast : cuts count=1) (hindex0 : index 0=U)
    (hindex : ∀j < count,index j ≤ sas.length)
    (hprefix : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps sas qs).take (index j),st.1 ≤ cuts j)
    (hsource : ∀j,1 ≤ j → j < count → ∀st∈(clockSteps sas qs).take U,st.1 ≤ cuts j)
    (hmono : ∀j < count,cuts j ≤ cuts (j+1))
    (μ : Measure κ) [IsFiniteMeasure μ] (ρ : κ→((ι→ℝ)×(ι→ℝ))) (hρ : Measurable ρ) :
    (∫r,nativeExteriorCompleteCFold Ei Es D w φ c U a qi qs P f z Q (ρ r) ∂μ)=
      (∑j∈Finset.range count,∫r,nativeExteriorIndexedCutLayer Ei Es D w φ (index j) 0 (cuts j) (cuts (j+1))
        qi qs P (fun η ζ s=>Q (f η ζ) s (z η ζ)) (ρ r) ∂μ)-
        (partitionPoint a sas U/2)*(∫r,nativeExteriorRetainedCProductCovariance Ei Es D w φ c U qi qs P f z Q (ρ r) ∂μ) := by
  have H : (fun r=>nativeExteriorCompleteCFold Ei Es D w φ c U a qi qs P f z Q (ρ r))=
      fun r=>(∑j∈Finset.range count,nativeExteriorIndexedCutLayer Ei Es D w φ (index j) 0 (cuts j) (cuts (j+1))
        qi qs P (fun η ζ s=>Q (f η ζ) s (z η ζ)) (ρ r))-
        (partitionPoint a sas U/2)*nativeExteriorRetainedCProductCovariance Ei Es D w φ c U qi qs P f z Q (ρ r) :=
    funext fun r=>native_exterior_complete_c_fold_eq_grouped_indexed_layers_sub_covariance Ei Es D c hw φ U
      ho hblock qi qs P f z Q cuts count index hfirst hlast hindex0 hindex hprefix hsource hmono (ρ r)
  have hi : ∀j∈Finset.range count,Integrable (fun r=>nativeExteriorIndexedCutLayer Ei Es D w φ (index j) 0
      (cuts j) (cuts (j+1)) qi qs P (fun η ζ s=>Q (f η ζ) s (z η ζ)) (ρ r)) μ := by
    intro j _
    have ha0 : 0 ≤ a := (clockSteps_ordered ho qs).nonneg
    exact nativeExteriorIndexedCutLayer_integrable_map Ei Es D hw φ (index j) hoi
      (ho.lower (by norm_num) ha0) (cuts j) (cuts (j+1)) qi qs P _ μ ρ hρ
  have hC:=nativeExteriorRetainedCProductCovariance_integrable_map Ei Es D hw φ c U hoi ho qi qs P f z Q μ ρ hρ
  rw [H,integral_sub (integrable_finsetSum _ hi) (hC.const_mul _),integral_const_mul,
    integral_finsetSum _ hi]

end OAI.SKFluctuations.Cavity
