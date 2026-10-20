module

public import SKConstants.Completion.Blueprint.Experiment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology unitInterval
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] runMag

theorem measurable_completionComb {N : ℕ} (c s : ℝ) : (K : ℕ) →
    Measurable (fun p : PaperCompletionNoise N K × PaperCompletionNoise N K =>
      completionComb c s K p.1 p.2)
  | 0 => measurable_const
  | K + 1 => by
    have ih := measurable_completionComb (N := N) c s K
    have h1 : Measurable (fun p : (EuclideanSpace ℝ (Fin N) × PaperCompletionNoise N K) ×
        (EuclideanSpace ℝ (Fin N) × PaperCompletionNoise N K) =>
        ((c • p.1.1 + s • p.2.1, completionComb c s K p.1.2 p.2.2) :
          EuclideanSpace ℝ (Fin N) × PaperCompletionNoise N K)) :=
      (((measurable_fst.fst).const_smul c).add ((measurable_snd.fst).const_smul s)).prodMk
        (ih.comp ((measurable_fst.snd).prodMk measurable_snd.snd))
    exact h1

theorem measurable_combineAux {δ : ℝ≥0} {r₀ q : ℕ} (c s : ℝ) :
    Measurable (fun p : ReplayAux δ r₀ q × ReplayAux δ r₀ q => combineAux c s p.1 p.2) := by
  unfold combineAux
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine Measurable.prodMk ?_ ?_
    · refine Measurable.of_eval (fun i => ?_)
      exact (((measurable_pi_apply i).comp measurable_fst.fst.fst).const_smul c).add
        (((measurable_pi_apply i).comp measurable_snd.fst.fst).const_smul s)
    · refine Measurable.of_eval (fun j => Measurable.of_eval (fun i => ?_))
      have h1 : Measurable (fun p : ReplayAux δ r₀ q × ReplayAux δ r₀ q => p.1.1.2 j i) := by
        fun_prop
      have h2 : Measurable (fun p : ReplayAux δ r₀ q × ReplayAux δ r₀ q => p.2.1.2 j i) := by
        fun_prop
      exact (h1.const_smul c).add (h2.const_smul s)
  · exact (measurable_completionComb c s q).comp
      ((measurable_fst.snd.fst).prodMk measurable_snd.snd.fst)
  · refine Measurable.of_eval (fun i => ?_)
    exact (((measurable_pi_apply i).comp measurable_fst.snd.snd).const_smul c).add
      (((measurable_pi_apply i).comp measurable_snd.snd.snd).const_smul s)

theorem measurable_angleMatrix (p : Parameters) (n : ℕ) (θ : ℝ) :
    Measurable (fun z : Outer n × Internal p n => angleMatrix p n θ z.1 z.2) := by
  unfold angleMatrix baseMatrix gaussianRotation
  fun_prop

theorem measurable_angleAux (p : Parameters) (n : ℕ) (θ : ℝ) :
    Measurable (fun z : Outer n × Internal p n => angleAux p n θ z.2) :=
  (measurable_combineAux _ _).comp ((measurable_snd.snd.fst.fst).prodMk measurable_snd.snd.fst.snd)

theorem measurable_thresholdAt (p : Parameters) (n k : ℕ) :
    Measurable (fun z : Outer n × Internal p n => z.2.2.2 k) :=
  (measurable_pi_apply k).comp measurable_snd.snd.snd

theorem measurable_angleSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (t : ℝ≥0) (θ : ℝ) (k : ℕ) :
    Measurable (fun z : Outer n × Internal p n =>
      thresholdSpin (runMag W β hβ p n t (angleMatrix p n θ z.1 z.2) (angleAux p n θ z.2))
        (z.2.2.2 k)) :=
  (measurable_spinAt W β hβ p n t).comp
    (((measurable_angleMatrix p n θ).prodMk (measurable_angleAux p n θ)).prodMk
      (measurable_thresholdAt p n k))

theorem measurable_pathSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (i : ℕ) :
    Measurable (fun z : Outer n × Internal p n => pathSpin W β hβ p n z.1 z.2 i) := by
  cases i with
  | zero => exact measurable_angleSpin W β hβ p n _ 0 0
  | succ k =>
    by_cases hk : k ≤ gridSize p n
    · simp only [pathSpin, hk, ite_true]
      exact measurable_angleSpin W β hβ p n _ _ _
    · simp only [pathSpin, hk, ite_false]
      exact measurable_angleSpin W β hβ p n _ _ _

theorem measurable_pathSpin_internal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (o : Outer n) (i : ℕ) :
    Measurable (fun ω : Internal p n => pathSpin W β hβ p n o ω i) := by
  have h := (measurable_pathSpin W β hβ p n i).comp
    (measurable_prodMk_left : Measurable (fun ω : Internal p n => ((o, ω) : Outer n × Internal p n)))
  simp only [Function.comp_def] at h
  exact h

theorem measurableSet_spin_pair {α : Type*} [MeasurableSpace α] {n : ℕ}
    {F G : α → Spin n} (hF : Measurable F) (hG : Measurable G) (P : Spin n → Spin n → Prop) :
    MeasurableSet {z | P (F z) (G z)} := by
  have hs : MeasurableSet {x : Spin n × Spin n | P x.1 x.2} := (Set.toFinite _).measurableSet
  exact hs.preimage (hF.prodMk hG)

theorem measurableSet_excludedSet_mem (β : ℝ) (p : Parameters) (n : ℕ) (x : Spin n) :
    MeasurableSet {G : Prim n | x ∈ excludedSet β p n G} :=
  measurableSet_pressureSelectedSparseBoundary_mem _ _ _ _ _ _ _ _ x

theorem measurableSet_not_mem_excludedSet {α : Type*} [MeasurableSpace α] (β : ℝ)
    (p : Parameters) (n : ℕ) {F : α → Spin n} {G : α → Prim n}
    (hF : Measurable F) (hG : Measurable G) :
    MeasurableSet {z | F z ∉ excludedSet β p n (G z)} := by
  have he : {z | F z ∉ excludedSet β p n (G z)} =
      ⋃ x : Spin n, {z | F z = x} ∩ G ⁻¹' {g | x ∉ excludedSet β p n g} := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun x => (hF (measurableSet_singleton x)).inter
    (hG (measurableSet_excludedSet_mem β p n x).compl))

theorem measurableSet_goodEvent_joint (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    MeasurableSet {z : Outer n × Internal p n | z.2 ∈ goodEvent W β hβ p n z.1} := by
  have h1 : MeasurableSet {z : Outer n × Internal p n | ∀ i < gridSize p n + 2,
      hammingDist (pathSpin W β hβ p n z.1 z.2 i) (pathSpin W β hβ p n z.1 z.2 (i + 1)) ≤
        hammingRadius p n} := by
    have he : {z : Outer n × Internal p n | ∀ i < gridSize p n + 2,
        hammingDist (pathSpin W β hβ p n z.1 z.2 i) (pathSpin W β hβ p n z.1 z.2 (i + 1)) ≤
          hammingRadius p n} = ⋂ i ∈ Finset.range (gridSize p n + 2),
        {z | hammingDist (pathSpin W β hβ p n z.1 z.2 i) (pathSpin W β hβ p n z.1 z.2 (i + 1)) ≤
          hammingRadius p n} := by
      ext z
      simp
    rw [he]
    exact Finset.measurableSet_biInter _ (fun i _ => measurableSet_spin_pair
      (measurable_pathSpin W β hβ p n i) (measurable_pathSpin W β hβ p n (i + 1))
      (fun x y => hammingDist x y ≤ hammingRadius p n))
  have h2 : MeasurableSet {z : Outer n × Internal p n | ∀ j ≤ gridSize p n,
      pathSpin W β hβ p n z.1 z.2 (j + 1) ∉ excludedSet β p n z.1.1} := by
    have he : {z : Outer n × Internal p n | ∀ j ≤ gridSize p n,
        pathSpin W β hβ p n z.1 z.2 (j + 1) ∉ excludedSet β p n z.1.1} =
        ⋂ j ∈ Finset.range (gridSize p n + 1),
          {z | pathSpin W β hβ p n z.1 z.2 (j + 1) ∉ excludedSet β p n z.1.1} := by
      ext z
      simp
    rw [he]
    exact Finset.measurableSet_biInter _ (fun j _ => measurableSet_not_mem_excludedSet β p n
      (measurable_pathSpin W β hβ p n (j + 1)) measurable_fst.fst)
  exact h1.inter h2

theorem measurableSet_goodEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (o : Outer n) : MeasurableSet (goodEvent W β hβ p n o) := by
  have h := (measurableSet_goodEvent_joint W β hβ p n).preimage
    (measurable_prodMk_left : Measurable (fun ω : Internal p n => ((o, ω) : Outer n × Internal p n)))
  simp only [Set.preimage_ofPred_eq] at h
  exact h

end SKConstants.Blueprint
