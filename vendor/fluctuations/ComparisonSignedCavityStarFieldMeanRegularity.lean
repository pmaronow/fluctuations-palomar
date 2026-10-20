module

public import ComparisonSignedCavityStarFieldJointClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_field_test_mean_smooth
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→T.Assignment→ℝ) (r : ℕ)
    (hJ : ∀σ,BddSmooth r (fun y=>J y σ)) :
    BddSmooth r (fun y=>nativeStarFieldTestMean w φ T s star q J y) := by
  induction T generalizing a star q with
  | leaf=>exact native_star_field_expect_smooth leaf hw φ ho q J r hJ
  | step b T ih=>
    cases star with
    | zero=>exact native_star_field_expect_smooth (T.step b) hw φ ho q J r hJ
    | succ star=>
      exact (ih s star ho.2.2 (fun j=>q (j+1)) J hJ).shiftedMean
        (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho.2.2 _) r)
        (gaussianHierarchy_integrable hw φ _ (clockSteps_ordered ho.2.2 _) b.val (q 0))
  | fork T V ihT ihV=>
    cases star with
    | zero=>exact native_star_field_expect_smooth (T.fork V) hw φ ho q J r hJ
    | succ star=>
      cases s with
      | inl s=>
        apply BddSmooth.sum Finset.univ
        intro τ _
        exact (V.weight_smooth hw φ ho q τ r).mul
          (ihT s (star+1) ho q (fun y σ=>J y (σ,τ)) (fun σ=>hJ (σ,τ)))
      | inr s=>
        apply BddSmooth.sum Finset.univ
        intro σ _
        exact (T.weight_smooth hw φ ho q σ r).mul
          (ihV s (star+1) ho q (fun y τ=>J y (σ,τ)) (fun τ=>hJ (σ,τ)))

theorem native_star_pair_factor_smooth
    (as : List PositiveMass) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (F : S→S→ℝ) (u : S) (r : ℕ) :
    BddSmooth r (fun x=>nativeStarPairFactor w φ as star q F x u) := by
  have hd:MassOrdered a (as.take star++as.drop star):=by simpa only [List.take_append_drop] using ho
  exact (single (S:=S) (as.drop star)).nativeAnchor_expect_smooth hw φ hd.suffix_end
    (fun j=>q (star+j)) _ r

theorem native_star_field_test_mean_integrable
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→T.Assignment→ℝ) (hJ : ∀σ,BddSmooth 0 (fun y=>J y σ))
    (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ] (x : ι→ℝ) :
    Integrable (fun y=>nativeStarFieldTestMean w φ T s star q J (x+y)) μ :=
  (native_star_field_test_mean_smooth T s star hw φ ho q J 0 hJ).integrable_comp_measurable
    (measurable_const.add measurable_id)

theorem native_integral_list_sum {E α : Type} [MeasurableSpace E] (μ : Measure E)
    (L : List α) (F : α→E→ℝ) (hF : ∀a∈L,Integrable (F a) μ) :
    (∫x,(L.map (fun a=>F a x)).sum ∂μ)=(L.map (fun a=>∫x,F a x ∂μ)).sum := by
  suffices HH : Integrable (fun x=>(L.map (fun a=>F a x)).sum) μ ∧
      (∫x,(L.map (fun a=>F a x)).sum ∂μ)=(L.map (fun a=>∫x,F a x ∂μ)).sum from HH.2
  induction L with
  | nil=>simp
  | cons a L ih=>
    have ha:=hF a List.mem_cons_self
    have hL (b) (hb:b∈L):=hF b (List.mem_cons_of_mem a hb)
    obtain ⟨hi,he⟩:=ih hL
    simp only [List.map_cons,List.sum_cons]
    exact ⟨ha.add hi,by rw [integral_add ha hi,he]⟩

end OAI.SKFluctuations.Hierarchy.ClockTree
