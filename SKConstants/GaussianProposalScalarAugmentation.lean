module

public import SKConstants.GaussianProposalIndependentCompletions
public import SKConstants.GaussianProposalScalarInitialState
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

lemma scalarMeshPaperUpdate_eq_of_endpoint_eq (H : ℝ≥0) (δ τ : ℕ → ℝ≥0)
    (n K k : ℕ) (s : ScalarMeshPaperPast H δ τ n)
    (z w : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hz : ∀ i : Fin n,z (.inl i)=w (.inl i)) :
    scalarMeshPaperUpdate H δ τ n K k s z = scalarMeshPaperUpdate H δ τ n K k s w := by
  apply Prod.ext
  · rfl
  · funext i
    change scalarAppendQueryInterval H (δ (K-k)) (scalarMeshPaperQueryTime τ K k)
      (s.2 i,(z (.inl i),s.1.2.2 (K-k) i)) = _
    rw [hz i]
    rfl

lemma scalarGrowingPaperUpdate_eq_of_endpoint_eq (H δ : ℝ≥0)
    (n K k : ℕ) (s : ScalarGrowingPaperPast H δ n)
    (z w : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hz : ∀ i : Fin n,z (.inl i)=w (.inl i)) :
    scalarGrowingPaperUpdate H δ n K k s z = scalarGrowingPaperUpdate H δ n K k s w :=
  scalarMeshPaperUpdate_eq_of_endpoint_eq H _ _ n K k s z w hz

open GaussianProposal

def scalarGrowingSourceAugmentedOutput (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : PaperAugmentedNoise (ranks+q) q) :
    Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ × PaperCompletionNoise (ranks+q) q :=
  actualPaperAugmentedOutput ranks q (skSigma (ranks+q))
    (scalarGrowingPaperTarget b f g hf hg m r (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
    (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
    (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p) z

lemma measurable_scalarGrowingSourceAugmentedOutput (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    Measurable (Function.uncurry (scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q)) := by
  exact (actualPaperAugmentedOutput_measurable ranks q (skSigma (ranks+q)) _ _
    (fun k i => measurable_scalarMeshPaperTarget b f g hf hg m hm _ _ _ _ (ranks+q) q k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ (ranks+q) q k)).comp
    (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst).prodMk measurable_snd)

lemma scalarGrowingSourceAugmentedOutput_fiber_law (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q)) :
    (paperAugmentedNoiseLaw (ranks+q) q).map
      (scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p) =
      (skDisorderLaw (ranks+q)).prod (paperCompletionNoiseLaw (ranks+q) q) := by
  unfold scalarGrowingSourceAugmentedOutput
  simpa only [skDisorderLaw,skSigma,Nat.cast_add,Nat.cast_ofNat] using
    actualPaperAugmentedOutput_law ranks q (skSigma (ranks+q))
      (scalarGrowingPaperTarget b f g hf hg m r (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
      (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
      (fun k i => measurable_scalarMeshPaperTarget b f g hf hg m hm _ _ _ _ (ranks+q) q k i)
      (fun k => measurable_scalarMeshPaperUpdate _ _ _ (ranks+q) q k)
      (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p)

theorem scalarGrowingSourceAugmentedOutput_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : Measurable (Function.uncurry m))
    (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) :
    ((scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
      (paperAugmentedNoiseLaw (ranks+q) q)).map (fun p =>
        (p.1,scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p.1 p.2)) =
      (scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
        ((skDisorderLaw (ranks+q)).prod (paperCompletionNoiseLaw (ranks+q) q)) :=
  adaptiveStep_joint_law
    (measurable_scalarGrowingSourceAugmentedOutput b f g hf hg m hm r δ ranks q)
    (scalarGrowingSourceAugmentedOutput_fiber_law b f g hf hg m hm r δ ranks q)

lemma scalarGrowingSourceAugmentedOutput_matrix (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : PaperAugmentedNoise (ranks+q) q) :
    (scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p z).1 =
      scalarGrowingSourceProposal b f g hf hg m r δ ranks q p
        (paperAugmentedOriginal (ranks+q) q z) := rfl

theorem scalarGrowingSourceAugmentedOutput_matrix_query_coupling
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (δ : ℝ≥0) (ranks q : ℕ) (hn : 0<ranks+q)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : PaperAugmentedNoise (ranks+q) q) :
    paperMatrixQueryRun ranks (ranks+q) (ranks+q)
      (scalarGrowingPaperTarget b f g hf hg m r (scalarGrowingSourceHorizon δ q) δ (ranks+q) q)
      (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q) q
      (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p,1)
      (paperCompletionReplayNoise (ranks+q) q
        (scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p z).2)
      (scalarGrowingSourceAugmentedOutput b f g hf hg m r δ ranks q p z).1 =
    proposalTerminalPast (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q) q
      (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p)
      (paperAugmentedOriginal (ranks+q) q z) := by
  have hI : ∀ i j : Fin (ranks+q), dot ((1 : Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ) i)
      ((1 : Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ) j)=if i=j then 1 else 0 := by
    intro i j
    have he : (1 : Matrix (Fin (ranks+q)) (Fin (ranks+q)) ℝ)=canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [he]
    exact canonicalBasis_orthogonal i j
  apply paperIndependentCompletions_matrix_query_coupling ranks (ranks+q) (ranks+q)
    (by exact_mod_cast hn) _ _
    (fun k a z w hz => scalarGrowingPaperUpdate_eq_of_endpoint_eq _ _ _ _ k a z w hz)
    q _ hI z _
  simp only [frameProjection,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  rfl

end SKConstants
