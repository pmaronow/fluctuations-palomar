module

public import SKConstants.Completion.LC5.QueryCoordinates
public import SKConstants.GaussianProposalScalarMeshCallbacks
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.L2Operator NNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5
open GaussianProposal

def paperEndpointTrace (n : ℕ) : (K : ℕ) → StoppedNoise (Fin n) K →
    Fin K → EuclideanSpace ℝ (Fin n ⊕ Unit)
  | 0, _ => Fin.elim0
  | K+1, z => Fin.cases z.1 (paperEndpointTrace n K z.2)

variable {Past : Type*}

def paperOffColumnTrace (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin K) : Fin n → ℝ :=
  paperRemainingProjectionTrace r n target update K s z j.succ *ᵥ
    (fun i => paperEndpointTrace n K z j (.inl i))

def paperDiagonalTrace (N : ℝ) (n K : ℕ) (z : StoppedNoise (Fin n) K) (j : Fin K) : ℝ :=
  2*skSigma N*paperEndpointTrace n K z j (.inr ())

def paperResidualProjection (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) : Matrix (Fin n) (Fin n) ℝ :=
  paperRemainingProjectionTrace r n target update K s z (Fin.last K)

theorem paperRemainingProjectionTrace_zero (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperRemainingProjectionTrace r n target update K s z 0 = frameProjection s.2 := by
  cases K <;> rfl

theorem paperTensorProposal_columnAssembly (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperTensorProposal r n (skSigma N) target update K s z =
      columnAssembly N (paperQueryDirectionTrace r n N target update K s z)
        (paperOffColumnTrace r n target update K s z) (paperDiagonalTrace N n K z)
        (paperResidualProjection r n target update K s z *
          goeMatrix (skSigma N) (proposalResidualPrimitive K z) *
          paperResidualProjection r n target update K s z) := by
  induction K with
  | zero => simp [paperTensorProposal, columnAssembly, paperResidualProjection,
      paperRemainingProjectionTrace, proposalResidualPrimitive, frameProjection]
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    change physicalColumnTerm (skSigma N) (r+K) F z.1 +
      paperTensorProposal r n (skSigma N) target update K (update K s.1 z.1,tailRows F) z.2 = _
    rw [physicalColumnTerm_SK_normalized N hN, ih]
    simp only [columnAssembly, Fin.sum_univ_succ, paperQueryDirectionTrace,
      paperOffColumnTrace, paperDiagonalTrace, paperEndpointTrace,
      Fin.cases_zero, Fin.cases_succ, paperRemainingProjectionTrace,
      paperRemainingProjectionTrace_zero, normalizedColumnMatrix,
      paperResidualProjection, proposalResidualPrimitive, ← Fin.succ_last, Fin.cases_succ]
    dsimp only [F, frameProjection]
    abel

theorem paperTensorProposal_energy (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (x : Fin n → ℝ) :
    let u := paperQueryDirectionTrace r n N target update K s z
    let f := paperOffColumnTrace r n target update K s z
    let d := paperDiagonalTrace N n K z
    let P := paperResidualProjection r n target update K s z
    quadraticEnergy N x (paperTensorProposal r n (skSigma N) target update K s z) =
      (∑ j, (N⁻¹*(x ⬝ᵥ u j))*(N⁻¹*(x ⬝ᵥ f j))) +
        (1/2 : ℝ)*(∑ j, (N⁻¹*(x ⬝ᵥ u j))^2*d j) +
        quadraticEnergy N x (P*goeMatrix (skSigma N) (proposalResidualPrimitive K z)*P) := by
  rw [paperTensorProposal_columnAssembly r n N hN target update K s z]
  exact columnAssembly_energy _ _ _ _ _ _

theorem paperQueryDirectionTrace_scale (r n : ℕ) (N : ℝ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin K) :
    paperQueryDirectionTrace r n N target update K s z j =
      Real.sqrt N • paperQueryDirectionTrace r n 1 target update K s z j := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [paperQueryDirectionTrace, normalizedQuery]
    · exact ih _ _ j

theorem actualPaper_offColumnTrace_eq_projection (r K : ℕ)
    (target : (j : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (j : Fin K) :
    WithLp.toLp 2 (paperOffColumnTrace r (r+K) target update K (a,1) z j) =
      WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l)) -
      ∑ i ∈ Finset.Iic j,
        inner (𝕜 := ℝ)
          (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i))
          (WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l))) •
          WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i) := by
  unfold paperOffColumnTrace
  rw [actualPaper_remainingProjection_eq_past_queries r K 1 (by norm_num)]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  ext l
  simp only [WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
    smul_eq_mul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec,
    dotProduct, inv_one, one_smul, EuclideanSpace.inner_toLp_toLp,
    Pi.star_apply, star_trivial]
  congr 1
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (i : Fin K) : i.val < j.succ.val ↔ i ≤ j := by
    change i.val < j.val+1 ↔ i.val ≤ j.val
    omega
  simp only [he]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr (by ext i; simp)
  intro i hi
  apply Finset.sum_congr rfl
  intro q hq
  ring

def paperQueryEnergy (r n : ℕ) (N : ℝ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (N⁻¹*(x ⬝ᵥ paperQueryDirectionTrace r n N target update K s z j))*
    (N⁻¹*(x ⬝ᵥ paperOffColumnTrace r n target update K s z j))

theorem paperQueryEnergy_eq_projected (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (j : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    paperQueryEnergy r (r+K) N target update K (a,1) z x =
      projectedQueryEnergy
        (fun j => WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j))
        (fun j => (Real.sqrt N)⁻¹ • WithLp.toLp 2
          (fun l => paperEndpointTrace (r+K) K z j (.inl l)))
        ((Real.sqrt N)⁻¹ • WithLp.toLp 2 x) := by
  let α := (Real.sqrt N)⁻¹
  have hα : N⁻¹ = α^2 := by dsimp [α]; rw [inv_pow, Real.sq_sqrt hN.le]
  have hαs : N⁻¹*Real.sqrt N = α := by
    rw [hα]
    dsimp [α]
    field_simp
  unfold paperQueryEnergy projectedQueryEnergy
  apply Finset.sum_congr rfl
  intro j hj
  have hp : α • WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l)) -
      ∑ i ∈ Finset.Iic j,
        inner (𝕜 := ℝ)
          (WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i))
          (α • WithLp.toLp 2 (fun l => paperEndpointTrace (r+K) K z j (.inl l))) •
          WithLp.toLp 2 (paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z i) =
      α • WithLp.toLp 2 (paperOffColumnTrace r (r+K) target update K (a,1) z j) := by
    rw [actualPaper_offColumnTrace_eq_projection]
    simp only [smul_sub, Finset.smul_sum, inner_smul_right, smul_smul]
  change _ = inner (𝕜 := ℝ) _ (α • WithLp.toLp 2 x) *
    inner (𝕜 := ℝ) (α • WithLp.toLp 2 x) _
  rw [hp, paperQueryDirectionTrace_scale r (r+K) N target update K (a,1) z j]
  simp only [inner_smul_right, real_inner_smul_left, EuclideanSpace.inner_toLp_toLp,
    star_trivial, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm _ x, ← mul_assoc N⁻¹, hαs, hα]
  ring

theorem scalarMeshPaperUpdate_ambient_congr (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K j : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (z w : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hzw : ∀ i, z (.inl i) = w (.inl i)) :
    scalarMeshPaperUpdate H δ τ n K j s z = scalarMeshPaperUpdate H δ τ n K j s w := by
  simp only [scalarMeshPaperUpdate]
  congr 1
  funext i
  rw [hzw i]

end SKConstants.Completion.LC5
