module

public import CavityAllocationTopology
public import SKFluctuationsOAI.Probability.SKFluctuations.EvalStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal
variable {ι : Type*} [Fintype ι]
variable {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

def plantedNodeValue (a b : ℝ) (F : (ι → ℝ) → ℝ) {k : ℕ}
    (A : Fin k → (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (a*shiftedContinuation μ b F x) *
    ∏ i, shiftedMean μ b F (A i) x

theorem plantedNodeValue_eq_realPower {a b : ℝ} (hb : b ≠ 0)
    (F : (ι → ℝ) → ℝ) {k : ℕ} (A : Fin k → (ι → ℝ) → ℝ) (x : ι → ℝ)
    (hi : Integrable (fun z => Real.exp (b*F (x+z))) μ) :
    plantedNodeValue (μ := μ) a b F A x =
      (∫ z, Real.exp (b*F (x+z)) ∂μ)^(a/b-(k:ℝ))*
        ∏ i, (∫ z, A i (x+z)*Real.exp (b*F (x+z)) ∂μ) := by
  let I := ∫ z, Real.exp (b*F (x+z)) ∂μ
  have hI : 0 < I := partition_pos b hi
  have hpow : Real.exp (a*(Real.log I/b)) = I^(a/b) := by
    rw [Real.rpow_def_of_pos hI]
    congr 1
    ring
  unfold plantedNodeValue shiftedContinuation shiftedMean tiltedMean
  change Real.exp (a*(Real.log I/b)) *
    (∏ i, (∫ z, A i (x+z)*Real.exp (b*F (x+z)) ∂μ)/I) = _
  rw [hpow, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change I^(a/b)*((∏ i, (∫ z, A i (x+z)*Real.exp (b*F (x+z)) ∂μ))/I^k) =
    I^(a/b-(k:ℝ))*(∏ i, (∫ z, A i (x+z)*Real.exp (b*F (x+z)) ∂μ))
  rw [Real.rpow_sub hI, Real.rpow_natCast]
  ring

theorem actual_planted_node_new_child {a b I : ℝ} (hb : 0 < b) (hI : 0 < I)
    (k : ℕ) (oldChildIntegralProduct : ℝ) :
    HasDerivAt (fun t : ℝ => b*t^(a/b-(k:ℝ))*oldChildIntegralProduct)
      ((a-(k:ℝ)*b)*I^(a/b-(k:ℝ)-1)*oldChildIntegralProduct) I :=
  (realPowerNode_new_child hb hI k).mul_const oldChildIntegralProduct

theorem actual_replica_children_realPower {S : Type*} [Fintype S] [Nonempty S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {tail : List (GaussianStep ι)} {a b : ℝ} (hb : 0 < b)
    (ho : OrderedSteps b tail) (q : ι → ℝ≥0) {k : ℕ}
    (R : Fin k → ReplicaTree ι S tail) (P : ∀ i, (R i).Assignment → ℝ) (x : ι → ℝ) :
    Real.exp (a*gaussianHierarchy w φ ((b,q)::tail) x)*
      (∏ i, ((R i).step (b,q)).expect w φ (P i) x) =
    (∫ z, Real.exp (b*gaussianHierarchy w φ tail (x+z))
      ∂Measure.pi (fun j => gaussianReal 0 (q j)))^(a/b-(k:ℝ))*
      (∏ i, ∫ z, (R i).expect w φ (P i) (x+z)*
        Real.exp (b*gaussianHierarchy w φ tail (x+z))
        ∂Measure.pi (fun j => gaussianReal 0 (q j))) := by
  have h := plantedNodeValue_eq_realPower (μ := Measure.pi (fun j => gaussianReal 0 (q j)))
    (a := a) hb.ne' (gaussianHierarchy w φ tail)
    (fun i => (R i).expect w φ (P i)) x
    (gaussianHierarchy_integrable hw φ tail ho b q x)
  unfold plantedNodeValue at h
  simpa only [gaussianHierarchy, ReplicaTree.expect_step hw φ _ b q ho] using h

end OAI.SKFluctuations.Cavity
