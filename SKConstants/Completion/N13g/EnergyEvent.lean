module

public import SKConstants.Completion.N13g.JointLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13g
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC4a LM3 N13t N13e LM4b LGram LC5 LM5
variable {Ω : Type} [MeasurableSpace Ω]

def statisticsRows {δ : ℝ≥0} {r q : ℕ} (u : CoarseStatistics δ r q) :
    Fin (r+q) → EuclideanSpace ℝ (Fin (q+(q+1))) :=
  fun i => WithLp.toLp 2 (Fin.append (fun j => u.2.2.1 j i)
    (Fin.append (fun j => u.2.2.2.1 j i) (fun _ : Fin 1 => scalarHiddenSign (u.2.1 i))))

theorem measurable_statisticsRows (δ : ℝ≥0) (r q : ℕ) :
    Measurable (statisticsRows (δ := δ) (r := r) (q := q)) := by
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro c
  refine Fin.addCases (fun j => ?_) (fun c => ?_) c
  · simpa only [statisticsRows, Fin.append_left, Function.comp_def] using
      ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd.snd.fst))
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) c
    · simpa only [statisticsRows, Fin.append_right, Fin.append_left, Function.comp_def] using
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd.snd.snd.fst))
    · simpa only [statisticsRows, Fin.append_right, Function.comp_def] using
        (measurable_of_finite scalarHiddenSign).comp
          ((measurable_pi_apply i).comp measurable_snd.fst)

def rowEnergyLinearPart (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ)
    (z : Fin (r+q) → EuclideanSpace ℝ (Fin (q+(q+1)))) : ℝ :=
  let P := empiricalGram z
  let s := populationTargetSpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
  let b := populationQuerySpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
  let H0 := populationCross W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
  energyLinearPart (P.submatrix (posteriorIndex q) (posteriorIndex q)-1)
    (P.submatrix (posteriorIndex q) (queryIndex q)-H0)
    s (WithLp.toLp 2 (fun j => P (posteriorIndex q j) (spinIndex q))-s)
    b (WithLp.toLp 2 (fun j => P (queryIndex q j) (spinIndex q))-b)

theorem rowEnergyLinearPart_eq_columns
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (z : Fin (r+q) → EuclideanSpace ℝ (Fin (q+(q+1)))) :
    rowEnergyLinearPart W β hβ δ r q z =
      let T := fun j => sampleColumn z (posteriorIndex q j)
      let g := fun j => sampleColumn z (queryIndex q j)
      let x := sampleColumn z (spinIndex q)
      let s := populationTargetSpin W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
      let b := populationQuerySpin W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
      let H0 := populationCross W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
      energyLinearPart (familyGram T-1) (familyCross T g-H0)
        s (familyCoordinates T x-s) b (familyCoordinates g x-b) := by
  have hA : familyGram (fun j => sampleColumn z (posteriorIndex q j)) =
      (empiricalGram z).submatrix (posteriorIndex q) (posteriorIndex q) := by
    ext i j
    exact sampleColumn_inner z _ _
  have hH : familyCross (fun j => sampleColumn z (posteriorIndex q j))
      (fun j => sampleColumn z (queryIndex q j)) =
      (empiricalGram z).submatrix (posteriorIndex q) (queryIndex q) := by
    ext i j
    exact sampleColumn_inner z _ _
  have hT : familyCoordinates (fun j => sampleColumn z (posteriorIndex q j))
      (sampleColumn z (spinIndex q)) =
      WithLp.toLp 2 (fun j => empiricalGram z (posteriorIndex q j) (spinIndex q)) := by
    ext j
    exact sampleColumn_inner z _ _
  have hg : familyCoordinates (fun j => sampleColumn z (queryIndex q j))
      (sampleColumn z (spinIndex q)) =
      WithLp.toLp 2 (fun j => empiricalGram z (queryIndex q j) (spinIndex q)) := by
    ext j
    exact sampleColumn_inner z _ _
  dsimp only
  rw [hA,hH,hT,hg]
  rfl

theorem measurable_energyLinearPart {q : ℕ} (s b : EuclideanSpace ℝ (Fin q)) :
    Measurable (fun y : (Matrix (Fin q) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ) ×
        (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) =>
      energyLinearPart y.1.1 y.1.2 s y.2.1 b y.2.2) := by
  let Y := (Matrix (Fin q) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ) ×
    (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q))
  have hhalf (i j : Fin q) : Measurable (fun y : Y => halfUpperTruncation y.1.1 i j) := by
    unfold halfUpperTruncation
    split_ifs <;> fun_prop
  have hfull (i j : Fin q) : Measurable (fun y : Y => fullUpperTruncation y.1.2 i j) := by
    unfold fullUpperTruncation
    split_ifs <;> fun_prop
  unfold energyLinearPart
  simp only [Matrix.inner_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_trivial]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
  fun_prop

theorem measurable_gram_energyLinearPart {q : ℕ}
    (s b : EuclideanSpace ℝ (Fin q)) (H0 : Matrix (Fin q) (Fin q) ℝ) :
    Measurable (fun P : Matrix (Fin (q+(q+1))) (Fin (q+(q+1))) ℝ =>
      energyLinearPart (P.submatrix (posteriorIndex q) (posteriorIndex q)-1)
        (P.submatrix (posteriorIndex q) (queryIndex q)-H0)
        s (WithLp.toLp 2 (fun j => P (posteriorIndex q j) (spinIndex q))-s)
        b (WithLp.toLp 2 (fun j => P (queryIndex q j) (spinIndex q))-b)) := by
  let D := Matrix (Fin (q+(q+1))) (Fin (q+(q+1))) ℝ
  have hhalf (i j : Fin q) : Measurable (fun P : D =>
      halfUpperTruncation (P.submatrix (posteriorIndex q) (posteriorIndex q)-1) i j) := by
    unfold halfUpperTruncation
    split_ifs <;> fun_prop
  have hfull (i j : Fin q) : Measurable (fun P : D =>
      fullUpperTruncation (P.submatrix (posteriorIndex q) (queryIndex q)-H0) i j) := by
    unfold fullUpperTruncation
    split_ifs <;> fun_prop
  unfold energyLinearPart
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, WithLp.ofLp_sub, WithLp.ofLp_toLp, Pi.sub_apply]
  fun_prop

theorem measurable_empirical_energyLinearPart {N q : ℕ}
    (s b : EuclideanSpace ℝ (Fin q)) (H0 : Matrix (Fin q) (Fin q) ℝ) :
    Measurable (fun z : Fin N → EuclideanSpace ℝ (Fin (q+(q+1))) =>
      energyLinearPart ((empiricalGram z).submatrix (posteriorIndex q) (posteriorIndex q)-1)
        ((empiricalGram z).submatrix (posteriorIndex q) (queryIndex q)-H0)
        s (WithLp.toLp 2 (fun j => empiricalGram z (posteriorIndex q j) (spinIndex q))-s)
        b (WithLp.toLp 2 (fun j => empiricalGram z (queryIndex q j) (spinIndex q))-b)) := by
  have hP : Measurable (empiricalGram (N := N) (d := q+(q+1))) := by
    unfold empiricalGram
    fun_prop
  exact (measurable_gram_energyLinearPart s b H0).comp hP

theorem measurable_rowEnergyLinearPart
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) :
    Measurable (rowEnergyLinearPart W β hβ δ r q) :=
  measurable_empirical_energyLinearPart
    (populationTargetSpin W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1)))
    (populationQuerySpin W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1)))
    (populationCross W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1)))

theorem sourceStatistics_rows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (u : (Fin (r+q) → Bool) × M1.SourceInput δ r q) :
    statisticsRows (sourceStatistics W β hβ δ r q u) = literalSourceRows W β hβ δ r q u := by
  funext i
  apply WithLp.ofLp_injective
  funext c
  refine Fin.addCases (fun j => ?_) (fun c => ?_) c
  · simp only [statisticsRows, sourceStatistics, literalSourceRows, paperRows,
      M1.SourceTargets, WithLp.ofLp_toLp, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) c
    · simp only [statisticsRows, sourceStatistics, literalSourceRows, paperRows,
        M1.SourceEndpoints, NDH.paperEndpointTrace_eq_noiseTrace,
        WithLp.ofLp_toLp, Fin.append_right, Fin.append_left]
    · simp only [statisticsRows, sourceStatistics, literalSourceRows, paperRows,
        WithLp.ofLp_toLp, Fin.append_right]

theorem rowEnergyLinearPart_source
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (u : (Fin (r+q) → Bool) × M1.SourceInput δ r q) :
    rowEnergyLinearPart W β hβ δ r q (statisticsRows (sourceStatistics W β hβ δ r q u)) =
      sourceEnergyLinearPart W β hβ δ r q u := by
  rw [sourceStatistics_rows, rowEnergyLinearPart_eq_columns]
  dsimp only [sampleColumn, literalSourceRows, paperRows, posteriorIndex, queryIndex, spinIndex,
    Fin.append_left, Fin.append_right, sourceEnergyLinearPart]
  simp only [Fin.append_left, Fin.append_right]

def energyStatisticsEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (η u R : ℝ) : Set (CoarseStatistics δ r q) :=
  {z | statisticsRows z ∈ rowGramEvent (mixedPopulation W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))) (r+q) η ∧
    |quadraticEnergy (r+q : ℕ) (signSpin z.2.1) z.1 - actualCoarseEnergy W β (growingQueryTime δ) q -
      rowEnergyLinearPart W β hβ δ r q (statisticsRows z)| ≤ u+R}

theorem measurableSet_energyStatisticsEvent
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) (η u R : ℝ) :
    MeasurableSet (energyStatisticsEvent W β hβ δ r q η u R) := by
  have hE : Measurable (fun z : CoarseStatistics δ r q =>
      quadraticEnergy (r+q : ℕ) (signSpin z.2.1) z.1) := by
    unfold quadraticEnergy signSpin dotProduct Matrix.mulVec
    fun_prop
  exact ((measurableSet_rowGramEvent _ _ _).preimage (measurable_statisticsRows δ r q)).inter
    (measurableSet_le (((hE.sub_const _).sub
      ((measurable_rowEnergyLinearPart W β hβ δ r q).comp
        (measurable_statisticsRows δ r q))).abs) measurable_const)

theorem raw_energyStatisticsEvent_compl_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q R m : ℕ) (hdim : q+m=2^R)
    (hN : 0 < r+q) (η u : ℝ) (hη : 0 < η) (hu : 0 < u)
    (hsmall : 16*((R+1 : ℕ) : ℝ)^2*η ≤ 1) :
    (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
      ((rawStatistics W β hβ δ r q) ⁻¹'
        energyStatisticsEvent W β hβ δ r q η u (1400*((R+1 : ℕ) : ℝ)^4*η^2))ᶜ ≤
      gramTailBudget (r+q) (q+(q+1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ q)) η +
        2*Real.exp (-((r+q : ℕ) : ℝ)*u^2) := by
  let E := energyStatisticsEvent W β hβ δ r q η u (1400*((R+1 : ℕ) : ℝ)^4*η^2)
  have hE : MeasurableSet E := measurableSet_energyStatisticsEvent W β hβ δ r q _ _ _
  have hsrc : Measurable (sourceStatistics W β hβ δ r q) := by
    rw [← replayStatistics_toReplay W β hβ δ r q hN]
    exact (measurable_replayStatistics W β hβ δ r q).comp
      (measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r q).comp measurable_snd))
  have he := congrArg (fun μ => μ.real Eᶜ) (source_raw_joint_statistics_law W β hβ δ r q hN)
  simp only [Measure.real, Measure.map_apply hsrc hE.compl,
    Measure.map_apply (measurable_rawStatistics W β hβ δ r q) hE.compl] at he
  have hsub : ((sourceStatistics W β hβ δ r q) ⁻¹' E)ᶜ ⊆
      (sourceCoarseEnergyEvent W β hβ δ r q η u)ᶜ := by
    apply compl_subset_compl.mpr
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [sourceStatistics_rows]
      exact hz.1
    · rw [rowEnergyLinearPart_source]
      exact sourceCoarseEnergyEvent_energy_error W β hβ δ hδ r q R m hdim hN η u hη.le hsmall z hz
  change (M1.SourceLinkedLaw W β hβ δ r q).real
    ((sourceStatistics W β hβ δ r q) ⁻¹' E)ᶜ =
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
        ((rawStatistics W β hβ δ r q) ⁻¹' E)ᶜ at he
  rw [← he]
  exact (measureReal_mono hsub).trans (sourceCoarseEnergyEvent_compl_le W β hβ δ hδ r q hN η u
    hη hu (NDH.sourceMixedRowsLaw_holds W β hβ δ hδ r q))

end SKConstants.Completion.N13g
