module

public import SKConstants.GaussianProposalMatrixQueryTrace
public import SKConstants.GaussianProposalEndpointStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal
variable {Past : Type*}

def paperNoiseTrace (n : ℕ) : (K : ℕ) → StoppedNoise (Fin n) K →
    Fin K → EuclideanSpace ℝ (Fin n ⊕ Unit)
  | 0, _, j => Fin.elim0 j
  | K+1, z, j => Fin.cases z.1 (paperNoiseTrace n K z.2) j

@[simp] theorem paperScalarPastTrace_zero (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperScalarPastTrace r n target update K s z 0=s.1 := by cases K <;> rfl

@[simp] theorem paperRemainingProjectionTrace_zero (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperRemainingProjectionTrace r n target update K s z 0=frameProjection s.2 := by
  cases K <;> rfl

theorem paperScalarPastTrace_invariant {A : Type*} (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (π : Past → A) (hπ : ∀ k s z, π (update k s z)=π s)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (j : Fin (K+1)) :
    π (paperScalarPastTrace r n target update K s z j)=π s.1 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    revert j
    apply Fin.cases
    · rfl
    · intro j
      exact (ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 j).trans
        (hπ K s.1 z.1)

theorem paperScalarPastTrace_step (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin K) :
    paperScalarPastTrace r n target update K s z j.succ =
      update (K-1-j.val) (paperScalarPastTrace r n target update K s z j.castSucc)
        (paperNoiseTrace n K z j) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    revert j
    apply Fin.cases
    · simp only [paperScalarPastTrace,paperNoiseTrace,Fin.castSucc_zero,
        Fin.cases_zero,Fin.cases_succ,Fin.val_zero,
        Nat.add_sub_cancel,Nat.sub_zero,paperScalarPastTrace_zero]
    · intro j
      have hj : K+1-1-j.succ.val=K-1-j.val := by simp; omega
      simpa only [paperScalarPastTrace,paperNoiseTrace,Fin.castSucc_succ,
        Fin.cases_succ,hj] using
        ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 j

theorem paperTargetTrace_eq_current_state (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin K) :
    paperTargetTrace r n target update K s z j =
      target (K-1-j.val) (paperScalarPastTrace r n target update K s z j.castSucc) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    revert j
    apply Fin.cases
    · simp only [paperTargetTrace,paperScalarPastTrace,Fin.castSucc_zero,
        Fin.cases_zero,Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero]
    · intro j
      have hj : K+1-1-j.succ.val=K-1-j.val := by simp; omega
      simpa only [paperTargetTrace,paperScalarPastTrace,Fin.castSucc_succ,
        Fin.cases_succ,hj] using
        ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 j

theorem paperQueryDirectionTrace_scale (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (j : Fin K) :
    WithLp.toLp 2 (paperQueryDirectionTrace r n N target update K s z j) =
      Real.sqrt N • WithLp.toLp 2 (paperQueryDirectionTrace r n 1 target update K s z j) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    revert j
    apply Fin.cases
    · ext i
      simp only [paperQueryDirectionTrace,Fin.cases_zero,normalizedQuery,
        WithLp.ofLp_smul,WithLp.ofLp_toLp,Pi.smul_apply,smul_eq_mul,Real.sqrt_one,one_mul]
    · intro j
      simpa only [paperQueryDirectionTrace,Fin.cases_succ] using
        ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 j

theorem paperRemainingProjectionTrace_apply_norm_le (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (horth : ∀ i j, dot (s.2 i) (s.2 j)=if i=j then 1 else 0)
    (j : Fin (K+1)) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (paperRemainingProjectionTrace r n target update K s z j) x‖≤‖x‖ := by
  induction K with
  | zero =>
    simpa only [paperRemainingProjectionTrace] using frameProjection_apply_norm_le s.2 horth x
  | succ K ih =>
    revert j
    apply Fin.cases
    · exact frameProjection_apply_norm_le s.2 horth x
    · intro j
      exact ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2
        (tailRows_orthogonal _ (paperFrame_orthogonal _ _ horth)) j

theorem paperScalarPastTrace_last (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperScalarPastTrace r n target update K s z (Fin.last K)=proposalTerminalPast update K s.1 z := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hl : Fin.last (K+1)=(Fin.last K).succ := by rfl
    simpa only [paperScalarPastTrace,hl,Fin.cases_succ,proposalTerminalPast] using
      ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2

theorem paperMatrixQueryNoiseTrace_endpoint (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) (j : Fin K) :
    WithLp.toLp 2 (fun i =>
      paperNoiseTrace n K (paperMatrixQueryNoiseRun r n N target update K s z W) j (.inl i)) =
      completedMatrixEndpoint
        (paperRemainingProjectionTrace r n target update K s
          (paperMatrixQueryNoiseRun r n N target update K s z W) j.succ) W
        (WithLp.toLp 2 (paperQueryDirectionTrace r n N target update K s
          (paperMatrixQueryNoiseRun r n N target update K s z W) j))
        (WithLp.toLp 2 (fun i=>paperNoiseTrace n K z j (.inl i))) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    revert j
    apply Fin.cases
    · simp only [paperNoiseTrace,paperMatrixQueryNoiseRun,paperRemainingProjectionTrace,
        paperQueryDirectionTrace,Fin.cases_zero,Fin.cases_succ,paperRemainingProjectionTrace_zero]
      ext i
      simp only [paperQueriedNoise,completedMatrixEndpoint,WithLp.ofLp_toLp,
        WithLp.ofLp_add,WithLp.ofLp_sub,Matrix.ofLp_toEuclideanCLM,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,Sum.elim_inl,
        Pi.add_apply,Pi.sub_apply,remainingProjection,frameProjection,Matrix.sub_mulVec,Matrix.one_mulVec]
    · intro j
      simpa only [paperNoiseTrace,paperMatrixQueryNoiseRun,paperRemainingProjectionTrace,
        paperQueryDirectionTrace,Fin.cases_succ] using
        ih (update K s.1 (paperQueriedNoise N (paperFrame s.2 (target K s.1)) W z.1),
          tailRows (paperFrame s.2 (target K s.1))) z.2 j

end SKConstants.GaussianProposal
