module

public import SKConstants.Completion.LFine.QueryPrefix
public import SKConstants.GaussianProposalScalarPrefixReplay
public import SKConstants.ParisiFullVarianceIntegral
public import SKConstants.GaussianProposalActualParisiCallbacks
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators NNReal Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal SKConstantsOAI.ZeroTemperatureSK

def scalarMeshMeanAt (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n : ℕ)
    (a : ℝ≥0) (s : ScalarMeshPaperPast H δ τ n) : Fin n → ℝ :=
  fun i => m a (scalarMeshPaperObservation b f g hf hg H δ τ n s i
    (projIcc 0 (H : ℝ) H.coe_nonneg a))

theorem scalarMeshMeanAt_update (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n q k : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (z : EuclideanSpace ℝ (Fin n ⊕ Unit))
    (hH : τ (q-k) ≤ H) :
    scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-k)) (scalarMeshPaperUpdate H δ τ n q k s z) =
      scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-k)) s := by
  have hp : ScalarMeshPastPrefixEq H δ τ n (τ (q-k))
      (scalarMeshPaperUpdate H δ τ n q k s z) s := by
    refine ⟨rfl,rfl,?_,fun _ _ _ => rfl⟩
    intro i u hu
    exact scalarAppendQueryInterval_prefix H (δ (q-k)) (τ (q-k)) _ u hu
  ext i
  unfold scalarMeshMeanAt
  rw [scalarMeshPaperObservation_eq_of_prefix b f g hf hg H δ τ n _ hH _ _ hp]
  have ha : (τ (q-k) : ℝ) ∈ Icc (0 : ℝ) (H : ℝ) :=
    ⟨(τ (q-k)).coe_nonneg,NNReal.coe_le_coe.mpr hH⟩
  rw [projIcc_of_mem _ ha]

theorem scalarMeshPaper_projection_kills_posterior (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (n r q K : ℕ) (hK : K ≤ q) (hH : τ q ≤ H)
    (hscale : ∀ j, 0 < j → j ≤ q → scale j ≠ 0)
    (s : PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (hE : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (hzero : s.2 *ᵥ scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-K)) s.1 = 0)
    (z : StoppedNoise (Fin n) K) (j : Fin (K+1)) :
    paperRemainingProjectionTrace r n
      (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
      (scalarMeshPaperUpdate H δ τ n q) K s z j *ᵥ
        scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-K+j.val))
          (paperScalarPastTrace r n
            (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
            (scalarMeshPaperUpdate H δ τ n q) K s z j) = 0 := by
  induction K with
  | zero =>
    have hj : j=0 := Fin.ext (by omega)
    subst j
    change frameProjection s.2 *ᵥ scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-0+0)) s.1 = 0
    simp only [Nat.sub_zero, Nat.add_zero] at hzero ⊢
    simp [frameProjection, ← Matrix.mulVec_mulVec, hzero]
  | succ K ih =>
    let target := scalarMeshPaperTarget b f g hf hg m scale H δ τ n q
    let update := scalarMeshPaperUpdate H δ τ n q
    let F := paperFrame s.2 (target K s.1)
    let old := scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-(K+1))) s.1
    let cur := scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-K)) s.1
    have hs : scale (q-K) ≠ 0 := hscale _ (by omega) (Nat.sub_le _ _)
    have hcur : old + scale (q-K) • target K s.1 = cur := by
      ext i
      dsimp [target,scalarMeshPaperTarget,scalarMeshPaperQueryTime,old,cur,scalarMeshMeanAt]
      field_simp
      ring
    have hnew : tailRows F *ᵥ cur = 0 := by
      rw [← hcur, Matrix.mulVec_add, Matrix.mulVec_smul,
        paperFrame_tail_kills_target s.2 (target K s.1) hE, smul_zero, add_zero]
      ext i
      exact congrFun (paperFrame_inherits_killed_mean s.2 (target K s.1) old hzero) i.succ
    have hupdated : scalarMeshMeanAt b f g hf hg m H δ τ n (τ (q-K)) (update K s.1 z.1) = cur :=
      scalarMeshMeanAt_update b f g hf hg m H δ τ n q K s.1 z.1
        ((hτ (Nat.sub_le _ _)).trans hH)
    have hnew' : tailRows F *ᵥ scalarMeshMeanAt b f g hf hg m H δ τ n
        (τ (q-K)) (update K s.1 z.1) = 0 := by rw [hupdated]; exact hnew
    refine Fin.cases ?_ (fun j => ?_) j
    · change frameProjection s.2 *ᵥ old = 0
      unfold frameProjection
      rw [← Matrix.mulVec_mulVec]
      have hz : s.2 *ᵥ old = 0 := hzero
      rw [hz,Matrix.mulVec_zero]
    · have hi := ih (by omega) (update K s.1 z.1,tailRows F)
        (tailRows_orthogonal F (paperFrame_orthogonal s.2 (target K s.1) hE)) hnew' z.2 j
      have hind : q-(K+1)+j.succ.val = q-K+j.val := by simp only [Fin.val_succ]; omega
      simpa only [paperRemainingProjectionTrace,paperScalarPastTrace,Fin.cases_succ,hind] using hi

theorem actualGrowing_incrementScale_pos {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (j : ℕ) (hj : 0 < j) :
    0 < scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
      (growingQueryTime δ) j := by
  have htime := growingQueryTime_strictMono δ hδ (show j-1 < j by omega)
  change 0 < Real.sqrt (∫ v in (growingQueryTime δ (j-1) : ℝ)..(growingQueryTime δ j : ℝ),
    actualParisiFullSusceptibilitySquareExpected W β v)
  rw [← actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _ htime]
  exact NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _ htime)

def actualGrowingMeanAt {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ)
    (a : ℝ≥0) (s : ScalarGrowingPaperPast (scalarGrowingSourceHorizon δ q) δ n) : Fin n → ℝ :=
  scalarMeshMeanAt (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
    (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ) n a s

theorem actualGrowing_projection_kills_posterior {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (ranks q : ℕ) (s : ScalarGrowingPaperPast (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (hzero : actualGrowingMeanAt W β hβ δ (ranks+q) q 0 s = 0)
    (z : StoppedNoise (Fin (ranks+q)) q) (j : Fin (q+1)) :
    let target := actualParisiGrowingSourceTarget W β hβ δ ranks q
    let update := scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q
    paperRemainingProjectionTrace ranks (ranks+q) target update q (s,1) z j *ᵥ
      actualGrowingMeanAt W β hβ δ (ranks+q) q (growingQueryTime δ j.val)
        (paperScalarPastTrace ranks (ranks+q) target update q (s,1) z j) = 0 := by
  have hi := scalarMeshPaper_projection_kills_posterior
    (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
    (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β) (growingQueryTime δ))
    (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ).monotone (ranks+q) ranks q q le_rfl
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ q))
    (fun k hk _ => (actualGrowing_incrementScale_pos W β hβ δ hδ k hk).ne')
    (s,1) (by intro i k; simp [dot,Matrix.one_apply]) (by
      rw [Matrix.one_mulVec]
      simpa only [Nat.sub_self,growingQueryTime_zero,actualGrowingMeanAt] using hzero) z j
  dsimp only [actualGrowingMeanAt,actualParisiGrowingSourceTarget,
    scalarGrowingPaperTarget,scalarGrowingPaperUpdate]
  unfold scalarGrowingPaperTarget scalarGrowingPaperUpdate
  simpa only [Nat.sub_self,zero_add] using hi

end SKConstants.Completion.LFine
