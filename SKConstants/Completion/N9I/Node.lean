module

public import SKConstants.Completion.Blueprint5.FineStatements
public import SKConstants.Completion.LM1b.TraceMeasurability
public import SKConstants.Completion.N13A.EnergyMeasurable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.N9I
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LM5 M1 Blueprint5

variable {Past : Type*}

theorem paperQueryDirectionTrace_entry_abs_le_sqrt (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (e : Fin K) (i : Fin n) :
    |paperQueryDirectionTrace r n N target update K s z e i| ≤ Real.sqrt N := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact N9b.normalizedQuery_entry_abs_le_sqrt N _
        (paperFrame_orthogonal _ _ horth) i
    · exact ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2
        (tailRows_orthogonal _ (paperFrame_orthogonal _ _ horth)) e

theorem paperRemainingProjectionTrace_succ_entry_abs_le_one (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (e : Fin K) (i j : Fin n) :
    |paperRemainingProjectionTrace r n target update K s z e.succ i j| ≤ 1 := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · simpa only [paperRemainingProjectionTrace, Fin.cases_succ,
        GaussianProposal.paperRemainingProjectionTrace_zero, frameProjection, remainingProjection] using
        N9b.remainingProjection_entry_abs_le_one (paperFrame s.2 (target K s.1))
          (paperFrame_orthogonal _ _ horth) i j
    · exact ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2
        (tailRows_orthogonal _ (paperFrame_orthogonal _ _ horth)) e

theorem paperEndpointTrace_integrable (n K : ℕ) (e : Fin K) (i : Fin n ⊕ Unit) :
    Integrable (fun z => paperEndpointTrace n K z e i) (stoppedNoiseLaw (Fin n) K) := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact (coordinate_gaussian i).integrable.comp_fst (stoppedNoiseLaw (Fin n) K)
    · exact (ih e).comp_snd (primitiveGaussian (Fin n ⊕ Unit))

variable {Ω : Type*} [MeasurableSpace Ω]

theorem linkedSourceEndpoint_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) (i : Fin (r+K) ⊕ Unit) :
    Integrable (fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
      paperEndpointTrace (r+K) K (Original δ r K z.2) e i)
        (SourceLinkedLaw W β hβ δ r K) := by
  have horiginal : MeasurePreserving (paperAugmentedOriginal (r+K) K)
      (paperAugmentedNoiseLaw (r+K) K) (stoppedNoiseLaw (Fin (r+K)) K) :=
    ⟨paperAugmentedOriginal_measurable _ _, paperAugmentedOriginal_law _ _⟩
  have haug := horiginal.integrable_comp_of_integrable
    (paperEndpointTrace_integrable (r+K) K e i)
  have hsource := haug.comp_snd (scalarGrowingPaperInitialDataLaw W (Horizon δ K) δ (r+K))
  have hlinked : MeasurePreserving Prod.snd (SourceLinkedLaw W β hβ δ r K)
      (SourceLaw W δ r K) :=
    ⟨measurable_snd, sourceLinkedLaw_base_marginal W β hβ δ r K⟩
  exact hlinked.integrable_comp_of_integrable hsource

theorem fineCellQueryEnergy_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) :
    Integrable (fineCellQueryEnergy W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K) := by
  let A := (Fin (r+K) → Bool) × SourceInput δ r K
  let μ := SourceLinkedLaw W β hβ δ r K
  let arg (z : A) : PaperState r (r+K) K (ScalarGrowingPaperPast (Horizon δ K) δ (r+K)) ×
      StoppedNoise (Fin (r+K)) K :=
    ((growingInitial δ r K z.2.1, 1), Original δ r K z.2)
  let U (z : A) := paperQueryDirectionTrace r (r+K) (r+K : ℕ)
    (Target W β hβ δ r K) (Update δ r K) K (arg z).1 (arg z).2 e
  let P (z : A) : Fin (r+K) → Fin (r+K) → ℝ := paperRemainingProjectionTrace r (r+K)
    (Target W β hβ δ r K) (Update δ r K) K (arg z).1 (arg z).2 e.succ
  let X (z : A) := signSpin z.1
  let G (z : A) (i : Fin (r+K)) := paperEndpointTrace (r+K) K (arg z).2 e (.inl i)
  have harg : Measurable arg :=
    (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_snd.fst).prodMk
      measurable_const).prodMk ((paperAugmentedOriginal_measurable _ _).comp measurable_snd.snd)
  have hdir := (measurable_paperQueryDirectionTrace r (r+K) (r+K : ℕ)
    (Target W β hβ δ r K) (Update δ r K)
    (measurable_growingTarget W β hβ δ r K) (measurable_growingUpdate δ r K) K).comp harg
  have hproj := (N13A.measurable_paperRemainingProjectionTrace r (r+K)
    (Target W β hβ δ r K) (Update δ r K)
    (measurable_growingTarget W β hβ δ r K) (measurable_growingUpdate δ r K) K).comp harg
  have hU (i : Fin (r+K)) : Measurable (fun z => U z i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply e).comp hdir)
  have hP (i j : Fin (r+K)) : Measurable (fun z => P z i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply e.succ).comp hproj))
  have hX (i : Fin (r+K)) : Measurable (fun z : A => X z i) :=
    (measurable_pi_apply i).comp ((measurable_signSpin (r+K)).comp measurable_fst)
  have horth (z : A) (i j : Fin (r+K)) :
      dot ((arg z).1.2 i) ((arg z).1.2 j) = if i=j then 1 else 0 := by
    change dot (canonicalBasis i) (canonicalBasis j) = _
    exact canonicalBasis_orthogonal i j
  have hUnorm (z : A) (i : Fin (r+K)) : ‖U z i‖ ≤ Real.sqrt (r+K : ℕ) :=
    paperQueryDirectionTrace_entry_abs_le_sqrt r (r+K) (r+K : ℕ) _ _ K _ _ (horth z) e i
  have hPnorm (z : A) (i j : Fin (r+K)) : ‖P z i j‖ ≤ 1 :=
    paperRemainingProjectionTrace_succ_entry_abs_le_one r (r+K) _ _ K _ _ (horth z) e i j
  have hXnorm (z : A) (i : Fin (r+K)) : ‖X z i‖ = 1 := by
    dsimp [X, signSpin, scalarHiddenSign]
    split <;> norm_num
  have hG (i : Fin (r+K)) : Integrable (fun z => G z i) μ :=
    linkedSourceEndpoint_integrable W β hβ δ r K e (.inl i)
  have hterm (i j k : Fin (r+K)) : Integrable
      (fun z => U z i * P z j k * (X z i * X z j) * G z k) μ := by
    apply (hG k).bdd_mul
      (((hU i).mul (hP j k)).mul ((hX i).mul (hX j))).aestronglyMeasurable
      (c := Real.sqrt (r+K : ℕ))
    apply ae_of_all
    intro z
    change ‖U z i * P z j k * (X z i * X z j)‖ ≤ Real.sqrt (r+K : ℕ)
    rw [norm_mul, norm_mul, norm_mul, hXnorm z i, hXnorm z j, one_mul, mul_one]
    exact (mul_le_mul (hUnorm z i) (hPnorm z j k) (norm_nonneg _)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  have hsum : Integrable (fun z => (((r+K : ℕ) : ℝ)⁻¹)^2 *
      ∑ j, ∑ k, ∑ i, U z i * P z j k * (X z i * X z j) * G z k) μ :=
    (integrable_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun i _ => hterm i j k)))).const_mul _
  convert hsum using 1
  funext z
  change (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, X z i * U z i) *
    (((r+K : ℕ) : ℝ)⁻¹ * ∑ j, X z j * ∑ k, P z j k * G z k) = _
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fineCellIntegrable_holds : FineCellIntegrableStatement := by
  intro Ω _ W β hβ δ _ r K _ e
  exact fineCellQueryEnergy_integrable W β hβ δ r K e

end SKConstants.Completion.N9I
