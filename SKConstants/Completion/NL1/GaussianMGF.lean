module

public import SKConstants.Completion.NL1.RowMeasurable
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal ENNReal

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem source_sharp_setLIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (S : Set (RowArray p n)) (hS : MeasurableSet S)
    (f : RowArray p n × ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in (sourceSharpRows W β hβ p n) ⁻¹' S,
      f (sourceSharpRows W β hβ p n u,
        sourceQueryEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u,
        growingSourceDiscardedEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u)
      ∂M1.SourceLinkedLaw W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)) =
    ∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
      f (sharpRows W β hβ p n y, sharpQueryEnergy W β hβ p n y, sharpDiscarded W β hβ p n y)
      ∂sharpLinkedLaw W β hβ p n := by
  have hsource := measurable_sourceSharpJointEnergy W β hβ p n hn
  have hsharp := (measurable_sharpRows W β hβ p n).prodMk
    ((measurable_sharpQueryEnergy W β hβ p n).prodMk (measurable_sharpDiscarded W β hβ p n))
  have hset : MeasurableSet {z : RowArray p n × ℝ × ℝ | z.1 ∈ S} := hS.preimage measurable_fst
  have hl := setLIntegral_map
    (μ := M1.SourceLinkedLaw W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    hset hf hsource
  have hr := setLIntegral_map (μ := sharpLinkedLaw W β hβ p n) hset hf hsharp
  have he := congrArg (fun μ : Measure (RowArray p n × ℝ × ℝ) =>
    ∫⁻ z in {z | z.1 ∈ S}, f z ∂μ) (source_sharp_joint_energy_law W β hβ p n hn)
  convert hl.symm.trans (he.trans hr) using 1
  all_goals rfl

theorem sharpDiscarded_mgf_on_rows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n)
    (S : Set (RowArray p n)) (hS : MeasurableSet S) (hSG : S ⊆ gramGood W β hβ p n) (θ : ℝ) :
    (∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ * sharpDiscarded W β hβ p n y)) ∂sharpLinkedLaw W β hβ p n) =
    ∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ^2 * discardedVariance (sharpRows W β hβ p n y) / 2))
      ∂sharpLinkedLaw W β hβ p n := by
  let δ := coarseMesh p n
  let r := coarseRank p n
  let K := coarseCount p n
  have hN : 0 < r+K := by simpa only [r, K, coarseRank, coarseCount, rankCount_add] using hn
  let castRows := fun z : Fin (r+K) → EuclideanSpace ℝ (Fin (K+(K+1))) =>
    fun i : Fin n => z (Fin.cast (rankCount_add p.a p.b n).symm i)
  have hcast : Measurable castRows :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have h := N13d.growingSourceDiscardedEnergy_mgf_on_rows W β hβ δ r K hN
    (castRows ⁻¹' S) (hS.preimage hcast) θ
  change (∫⁻ u in (sourceSharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ * growingSourceDiscardedEnergy W β hβ δ r K u))
        ∂M1.SourceLinkedLaw W β hβ δ r K) =
    ∫⁻ u in (sourceSharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ^2 * completionVariance (r+K : ℕ)
        (fun j => N13d.growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1 j)
        (N13d.growingResidual W β hβ δ r K (growingSourceCompact δ r K u).1) / 2))
        ∂M1.SourceLinkedLaw W β hβ δ r K at h
  have hvar : (∫⁻ u in (sourceSharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ^2 * completionVariance (r+K : ℕ)
        (fun j => N13d.growingCoefficients W β hβ δ r K (growingSourceCompact δ r K u).1 j)
        (N13d.growingResidual W β hβ δ r K (growingSourceCompact δ r K u).1) / 2))
        ∂M1.SourceLinkedLaw W β hβ δ r K) =
    ∫⁻ u in (sourceSharpRows W β hβ p n) ⁻¹' S,
      ENNReal.ofReal (Real.exp (θ^2 * discardedVariance (sourceSharpRows W β hβ p n u) / 2))
        ∂M1.SourceLinkedLaw W β hβ δ r K := by
    apply setLIntegral_congr_fun (hS.preimage (measurable_sourceSharpRows W β hβ p n))
    intro u hu
    exact congrArg (fun v : ℝ => ENNReal.ofReal (Real.exp (θ^2 * v / 2)))
      (completionVariance_eq_discardedVariance W β hβ p n hn u (hSG hu))
  have hl := source_sharp_setLIntegral W β hβ p n hn S hS
    (fun z => ENNReal.ofReal (Real.exp (θ * z.2.2)))
    ((measurable_snd.snd.const_mul θ).exp.ennreal_ofReal)
  have hr := source_sharp_setLIntegral W β hβ p n hn S hS
    (fun z => ENNReal.ofReal (Real.exp (θ^2 * discardedVariance z.1 / 2)))
    (((((measurable_discardedVariance p n).comp measurable_fst).const_mul (θ^2)).div_const 2).exp.ennreal_ofReal)
  exact hl.symm.trans ((h.trans hvar).trans hr)

end SKConstants.Completion.NL1
