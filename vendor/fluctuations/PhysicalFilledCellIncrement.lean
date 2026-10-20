module

public import RadiusCellEnergyDensity
public import PhysicalLocalCapTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem physicalCapCellTrace_pre_append (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (pre extra tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a ((pre++extra)++tail))
    (ha' : OrderedSteps a (pre++(extra++tail))) (j : ℕ) (hj : j < pre.length)
    (x : FeatureIndex (n+1)→ℝ) :
    physicalCapCellTrace n d e (pre++extra) tail ha j x=
      physicalCapCellTrace n d e pre (extra++tail) ha' j x := by
  induction pre generalizing a j x with
  | nil=>simp at hj
  | cons st pre ih=>
    rcases st with ⟨m,q⟩
    cases j with
    | zero=>simp only [List.cons_append,physicalCapCellTrace,List.append_assoc]
    | succ j=>
      have hj' : j < pre.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj
      simp only [List.cons_append,physicalCapCellTrace]
      rw [funext (ih ha.2.2.2 ha'.2.2.2 j hj')]
      simp only [List.append_assoc]

theorem physicalRootedCapCellTrace_pre_append (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (pre extra tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a ((pre++extra)++tail))
    (ha' : OrderedSteps a (pre++(extra++tail))) (j : ℕ) (hj : j < pre.length) :
    physicalRootedCapCellTrace n d e q₀ (pre++extra) tail ha j=
      physicalRootedCapCellTrace n d e q₀ pre (extra++tail) ha' j := by
  unfold physicalRootedCapCellTrace
  rw [funext (physicalCapCellTrace_pre_append n d e pre extra tail ha ha' j hj)]

theorem physicalRootedCapCellTrace_mul_duration_le_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (common : List (GaussianStep (FeatureIndex (n+1)))) (st : GaussianStep (FeatureIndex (n+1)))
    (tail : List (GaussianStep (FeatureIndex (n+1))))
    (ha : OrderedSteps 0 ((common++[st])++tail))
    (w : ℝ≥0) {g : ℝ} (hg : 0 < g)
    (hfield : ∀j,st.2 (Sum.inl j)=st.2 (Sum.inl 0)) (hslope : g*(w:ℝ) ≤ st.2 (Sum.inl 0)) :
    (w:ℝ)*physicalRootedCapCellTrace n d e q₀ (common++[st]) tail ha common.length ≤
      (physicalPathSecondMoment (n+1) ((common++[st])++tail) q₀ (common++[st]).length-
        physicalPathSecondMoment (n+1) ((common++[st])++tail) q₀ common.length)/((n+1:ℝ)*g) := by
  have hcap := physicalFiniteCapIndexedTrace_band_rooted_le_path_increment n d e q₀ [w]
    common [st] tail ha hg (by
      intro s hs j
      have he : s=st := List.mem_singleton.mp hs
      simpa only [he] using hfield j)
    (List.Forall₂.cons hslope List.Forall₂.nil)
  have hlen : (List.replicate common.length 0++[w]).length ≤ (common++[st]).length := by simp
  rw [physicalRootedCapIndexedTrace_eq_weightedCellSum n d e q₀ _ (common++[st]) tail ha hlen,
    physicalWeightedCutSum_zero_prefix] at hcap
  simpa only [physicalWeightedCutSum,zero_add,add_zero] using hcap

theorem physicalRootedCapCellTrace_full_mul_duration_le_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (common : List (GaussianStep (FeatureIndex (n+1)))) (st : GaussianStep (FeatureIndex (n+1)))
    (extra tail : List (GaussianStep (FeatureIndex (n+1))))
    (ha : OrderedSteps 0 (((common++[st])++extra)++tail))
    (w : ℝ≥0) {g : ℝ} (hg : 0 < g)
    (hfield : ∀j,st.2 (Sum.inl j)=st.2 (Sum.inl 0)) (hslope : g*(w:ℝ) ≤ st.2 (Sum.inl 0)) :
    (w:ℝ)*physicalRootedCapCellTrace n d e q₀ ((common++[st])++extra) tail ha common.length ≤
      (physicalPathSecondMoment (n+1) (((common++[st])++extra)++tail) q₀ (common.length+1)-
        physicalPathSecondMoment (n+1) (((common++[st])++extra)++tail) q₀ common.length)/((n+1:ℝ)*g) := by
  have ha' : OrderedSteps 0 ((common++[st])++(extra++tail)) := by
    simpa only [List.append_assoc] using ha
  rw [physicalRootedCapCellTrace_pre_append n d e q₀ (common++[st]) extra tail ha ha'
    common.length (by simp)]
  have hh := physicalRootedCapCellTrace_mul_duration_le_increment n d e q₀ common st
    (extra++tail) ha' w hg hfield hslope
  simpa only [List.append_assoc,List.length_append,List.length_singleton] using hh

end OAI.SKFluctuations.LaplaceWindowFormalization
