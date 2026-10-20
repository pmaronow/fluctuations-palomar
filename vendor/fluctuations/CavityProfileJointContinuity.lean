module

public import CavityMarginalProfileJets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι Z : Type*} [Fintype S] [Fintype ι] [Nonempty S]
    [TopologicalSpace Z] [FirstCountableTopology Z]

theorem joint_continuous_listSum {A : Type*} (L : List A) (f : A → Z → ℝ)
    (hf : ∀ a ∈ L, Continuous (f a)) : Continuous (fun z => (L.map fun a => f a z).sum) := by
  induction L with
  | nil => exact continuous_const
  | cons a L ih =>
    exact (hf a List.mem_cons_self).add
      (ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)))

def parameterClockSteps : List PositiveMass → (ℕ → Z → ι → ℝ) →
    List (ℝ × (Z → ι → ℝ))
  | [], _ => []
  | a::as, q => ((a:ℝ),q 0)::parameterClockSteps as (fun j => q (j+1))

theorem parameterClockSteps_actual (as : List PositiveMass) (q : ℕ → Z → ι → ℝ) (z : Z) :
    covarianceSteps (parameterClockSteps as q) z =
      clockSteps as (fun j i => Real.toNNReal (q j z i)) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => simp only [parameterClockSteps,covarianceSteps_cons,clockSteps,ih]

private theorem parameterClockSteps_mass (as : List PositiveMass) (q : ℕ → Z → ι → ℝ) :
    ∀ s ∈ parameterClockSteps as q, 0 < s.1 := by
  induction as generalizing q with
  | nil => simp [parameterClockSteps]
  | cons a as ih =>
    intro s hs
    simp only [parameterClockSteps,List.mem_cons] at hs
    rcases hs with rfl|hs
    · exact a.property
    · exact ih _ _ hs

private theorem parameterClockSteps_continuous (as : List PositiveMass)
    (q : ℕ → Z → ι → ℝ) (hq : ∀ j, Continuous (q j)) :
    ∀ s ∈ parameterClockSteps as q, Continuous s.2 := by
  induction as generalizing q with
  | nil => simp [parameterClockSteps]
  | cons a as ih =>
    intro s hs
    simp only [parameterClockSteps,List.mem_cons] at hs
    rcases hs with rfl|hs
    · exact hq 0
    · exact ih _ (fun j => hq (j+1)) _ hs

theorem actual_clock_potential_joint_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    (q : ℕ → Z → ι → ℝ) (hq : ∀ j, Continuous (q j)) :
    Continuous (fun p : Z × (ι → ℝ) => gaussianHierarchy w φ
      (clockSteps as (fun j i => Real.toNNReal (q j p.1 i))) p.2) := by
  simpa only [parameterClockSteps_actual] using covarianceFamily_potential_continuous
    hw φ (parameterClockSteps as q) (parameterClockSteps_mass as q)
      (parameterClockSteps_continuous as q hq)

private theorem actual_clock_weight_abs_le_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (x : ι → ℝ) :
    |T.weight w φ q σ x| ≤ 1 := by
  obtain ⟨hn,hs⟩ := T.weight_probability hw φ ho q x
  rw [abs_of_nonneg (hn σ), ← hs]
  exact Finset.single_le_sum (fun τ _ => hn τ) (Finset.mem_univ σ)

theorem ClockTree.actual_weight_joint_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Z → ι → ℝ)
    (hq : ∀ j, Continuous (q j)) (σ : T.Assignment) :
    Continuous (fun p : Z × (ι → ℝ) =>
      T.weight w φ (fun j i => Real.toNNReal (q j p.1 i)) σ p.2) := by
  induction T generalizing a q with
  | leaf =>
    exact (bddSmooth_spinWeight hw φ 0 σ).continuous.comp continuous_snd
  | @step b bs T ih =>
    let qs := fun j => q (j+1)
    have hcF := actual_clock_potential_joint_continuous hw φ bs qs (fun j => hq (j+1))
    have hcA := ih ho.2.2 qs (fun j => hq (j+1)) σ
    obtain ⟨C,hF⟩ := (potentialRegularity_spinLogPartition hw φ 0).1
    have hLip (p : Z × (ι → ℝ)) : LipschitzWith C
        (gaussianHierarchy w φ (clockSteps bs (fun j i => Real.toNNReal (qs j p.1 i)))) := by
      rw [← parameterClockSteps_actual bs qs p.1]
      exact covarianceFamily_lipschitz φ hF _ (parameterClockSteps_mass bs qs) p.1
    have h := dynamic_varianceTest_continuous
      (F := fun p : Z × (ι → ℝ) => gaussianHierarchy w φ
        (clockSteps bs (fun j i => Real.toNNReal (qs j p.1 i))))
      (A := fun p : Z × (ι → ℝ) => T.weight w φ
        (fun j i => Real.toNNReal (qs j p.1 i)) σ) hLip
      (hcF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (hcA.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (fun p y => actual_clock_weight_abs_le_one hw φ T ho.2.2 _ σ y) b.val
      ((hq 0).comp continuous_fst) continuous_snd
    simpa only [ClockTree.weight_step,varianceTest,qs,Function.comp_def] using h
  | fork T U ihT ihU =>
    exact (ihT ho q hq σ.1).mul (ihU ho q hq σ.2)

theorem ClockTree.actual_disorderWeight_joint_continuous {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (v : ι → ℝ) (q : Z → ℕ → ι → ℝ) (hq : ∀ j, Continuous (fun z => q z j))
    (σ : T.Assignment) (x : Z → ι → ℝ) (hx : Continuous x) :
    Continuous (fun z => T.disorderWeight w φ v (q z) σ (x z)) := by
  let increments := fun j z i => q z (j+1) i-q z j i
  have hi : ∀ j, Continuous (increments j) := by
    intro j
    exact (hq (j+1)).sub (hq j)
  have hc := T.actual_weight_joint_continuous hw φ ho increments hi σ
  have h := dynamic_zeroContinuation_continuous
    (A := fun z => T.weight w φ (fun j i => Real.toNNReal (increments j z i)) σ) hc
    (fun z y => actual_clock_weight_abs_le_one hw φ T ho _ σ y)
    (q := fun z i => q z 0 i-v i) (x := x) ((hq 0).sub continuous_const) hx
  have he (z : Z) : cumulativeIncrements (q z 0) (fun j => q z (j+1)) =
      fun j i => Real.toNNReal (increments j z i) := by
    funext j i
    cases j <;> rfl
  simpa only [ClockTree.disorderWeight,zeroContinuation,he] using h

theorem ClockTree.actual_disorderProfileJets_joint_continuous {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ)
    (q : Z → ℕ → ι → ℝ) (hq : ∀ j, Continuous (fun z => q z j))
    (x : Z → ι → ℝ) (hx : Continuous x)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P : T.Assignment → ℝ) :
    Continuous (fun z => disorderProfileJets w φ v (q z) (x z) Ks T P) := by
  induction Ks generalizing T with
  | nil =>
    change Continuous (fun z => ∑ σ, T.disorderWeight w φ v (q z) σ (x z)*P σ)
    exact continuous_finsetSum _ (fun σ _ =>
      (T.actual_disorderWeight_joint_continuous hw φ ho v q hq σ x hx).mul continuous_const)
  | cons K Ks ih =>
    simp only [disorderProfileJets]
    apply Continuous.div_const
    apply joint_continuous_listSum
    intro p hp
    apply Continuous.const_mul
    apply joint_continuous_listSum
    intro r hr
    exact (ih r.tree (ClockTree.profilePairTest P K p r)).const_mul r.coeff

end OAI.SKFluctuations.Hierarchy
