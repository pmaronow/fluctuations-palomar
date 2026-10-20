module

public import SKConstants.Completion.N9T1.Frame
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 Blueprint5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem castPaperState_frame_congr {A B : Type*} {r n a b : ℕ} (h : a = b)
    (s : PaperState r n a A) (t : PaperState r n a B) (hs : s.2 = t.2) :
    (castPaperState h s).2 = (castPaperState h t).2 := by
  subst b
  exact hs

theorem paperStateBefore_frame_congr {A B : Type*} (r n : ℕ)
    (target : ℕ → A → Fin n → ℝ) (update : ℕ → A → EuclideanSpace ℝ (Fin n ⊕ Unit) → A)
    (target' : ℕ → B → Fin n → ℝ) (update' : ℕ → B → EuclideanSpace ℝ (Fin n ⊕ Unit) → B)
    (K : ℕ) (s : PaperState r n K A) (t : PaperState r n K B)
    (z w : StoppedNoise (Fin n) K) (hs : s.2 = t.2) (e : Fin (K+1))
    (hT : ∀ j : Fin K, j.val < e.val →
      paperTargetTrace r n target update K s z j = paperTargetTrace r n target' update' K t w j) :
    (paperStateBefore r n target update K s z e).2 =
      (paperStateBefore r n target' update' K t w e).2 := by
  induction K with
  | zero => exact castPaperState_frame_congr _ s t hs
  | succ K ih =>
    revert hT
    refine Fin.cases (fun _ => hs) (fun e hT => ?_) e
    have h0 := hT 0 (by simp)
    change target K s.1 = target' K t.1 at h0
    have hf : tailRows (paperFrame s.2 (target K s.1)) =
        tailRows (paperFrame t.2 (target' K t.1)) := by rw [hs,h0]
    have hi := ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1)))
      (update' K t.1 w.1,tailRows (paperFrame t.2 (target' K t.1))) z.2 w.2 hf e
      (fun j hj => hT j.succ (by simpa using hj))
    exact castPaperState_frame_congr (by simp only [Fin.val_succ,Nat.succ_sub_succ_eq_sub]) _ _ hi

def zeroStoppedNoise (n : ℕ) : (K : ℕ) → StoppedNoise (Fin n) K
  | 0 => (0 : EuclideanSpace ℝ (Fin n × Fin n))
  | K+1 => (0,zeroStoppedNoise n K)

abbrev OriginalPastRows (a : ℝ≥0) (n : ℕ) :=
  Fin n → ScalarContinuousPath a × ScalarContinuousPath a

def pastMeanAt {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a t : ℝ≥0) {n : ℕ} (p : OriginalPastRows a n) : Fin n → ℝ :=
  fun i => actualParisiFullMagnetization β t
    (scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) a (0,p i)
        (projIcc 0 (a : ℝ) a.coe_nonneg (t : ℝ)))

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_pastMeanAt (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a t : ℝ≥0) (n : ℕ) : Measurable (pastMeanAt W β hβ a t (n := n)) := by
  apply Measurable.of_eval
  intro i
  have hm : Measurable (fun x : ℝ => actualParisiFullMagnetization β t x) :=
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
  exact hm.comp ((ContinuousMap.measurable_eval _).comp
    ((measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
      (measurable_const.prodMk (measurable_pi_apply i))))

def pastTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ a : ℝ≥0) {n : ℕ} (j : ℕ) (p : OriginalPastRows a n) : Fin n → ℝ :=
  fun i => (pastMeanAt W β hβ a (growingQueryTime δ (j+1)) p i -
    pastMeanAt W β hβ a (growingQueryTime δ j) p i) / actualFineScale W β δ j

theorem measurable_pastTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ a : ℝ≥0) (n j : ℕ) : Measurable (pastTarget W β hβ δ a (n := n) j) := by
  exact Measurable.of_eval fun i =>
    (((measurable_pi_apply i).comp (measurable_pastMeanAt W β hβ a _ n)).sub
      ((measurable_pi_apply i).comp (measurable_pastMeanAt W β hβ a _ n))).div_const _

def originalPastRows (δ : ℝ≥0) (r K : ℕ) (a : ℝ≥0) (ha : a ≤ Horizon δ K)
    (s : SourceInput δ r K) : OriginalPastRows a (r+K) :=
  fun i => (scalarInitialAuxiliaryRestriction (Horizon δ K) a ha (SourceDrivers δ r K s i).1,
    scalarInitialAuxiliaryRestriction (Horizon δ K) a ha (SourceDrivers δ r K s i).2)

theorem pastMeanAt_originalPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (a : ℝ≥0) (ha : a ≤ Horizon δ K)
    (t : ℝ≥0) (ht : t ≤ a) (s : SourceInput δ r K) :
    pastMeanAt W β hβ a t (originalPastRows δ r K a ha s) =
      sourceMeanAt W β hβ δ r K t s := by
  ext i
  let ta : Icc (0 : ℝ) (a : ℝ) := ⟨t,t.coe_nonneg,ht⟩
  let tH : Icc (0 : ℝ) (Horizon δ K : ℝ) := ⟨t,t.coe_nonneg,ht.trans ha⟩
  have hpa : projIcc 0 (a : ℝ) a.coe_nonneg (t : ℝ) = ta := projIcc_of_mem _ ta.property
  have hpH : projIcc 0 (Horizon δ K : ℝ) (Horizon δ K).coe_nonneg (t : ℝ) = tH :=
    projIcc_of_mem _ tH.property
  apply congrArg (actualParisiFullMagnetization β t)
  exact (congrArg _ hpa).trans
    ((scalarTwoDriverPicardPath_restriction _ _ _ _ _ _ _ ha 0
      (SourceDrivers δ r K s i).1 (SourceDrivers δ r K s i).2 ta).trans
      ((congrArg (fun Y : ScalarContinuousPath (Horizon δ K) => Y tH)
        (source_observation_eq_driver W β hβ δ r K s i)).symm.trans
          (congrArg _ hpH).symm))

def pastCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K)) :
    Matrix (Fin (fineCellRank r K e+1)) (Fin (r+K)) ℝ :=
  fun i => (paperStateBefore r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ (e.val+1)) (K-1-k) p)
    (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) e.castSucc).2
      (Fin.cast (fineCellRank_rows r K e) i)

theorem pastCellFrame_orthogonal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K)) :
    ∀ i k, dot (pastCellFrame W β hβ δ r K e p i)
      (pastCellFrame W β hβ δ r K e p k) = if i=k then 1 else 0 := by
  intro i k
  have h := paperStateBefore_orthogonal r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ (e.val+1)) (K-1-k) p)
    (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K)
    (by intro i k; simp [dot,Matrix.one_apply]) e.castSucc
  simpa only [pastCellFrame,Fin.cast_inj] using
    h (Fin.cast (fineCellRank_rows r K e) i) (Fin.cast (fineCellRank_rows r K e) k)

theorem measurable_pastCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) : Measurable (pastCellFrame W β hβ δ r K e) := by
  have hX : Measurable (fun p : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K) =>
      ((p,(1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)),zeroStoppedNoise (r+K) K)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  have hS := (measurable_paperStateBefore r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ (e.val+1)) (K-1-k) p)
    (fun _ p _ => p) (fun k i => (measurable_pi_apply i).comp
      (measurable_pastTarget W β hβ δ _ (r+K) (K-1-k))) (fun _ => measurable_fst)
    K e.castSucc).comp hX
  exact Measurable.of_eval fun i =>
    (measurable_pi_apply (Fin.cast (fineCellRank_rows r K e) i)).comp hS.snd

theorem pastTargetTrace_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ a : ℝ≥0) (r K : ℕ) (p : OriginalPastRows a (r+K)) (j : Fin K) :
    paperTargetTrace r (r+K) (fun k p => pastTarget W β hβ δ a (K-1-k) p)
        (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) j =
      pastTarget W β hβ δ a j.val p := by
  rw [paperTargetTrace_eq_current_state]
  have hp := paperScalarPastTrace_invariant r (r+K)
    (fun k p => pastTarget W β hβ δ a (K-1-k) p) (fun _ p _ => p)
    id (fun _ _ _ => rfl) K (p,1) (zeroStoppedNoise (r+K) K) j.castSucc
  change paperScalarPastTrace r (r+K) _ _ K (p,1) (zeroStoppedNoise (r+K) K) j.castSucc = p at hp
  change pastTarget W β hβ δ a (K-1-(K-1-j.val)) _ = _
  rw [hp,show K-1-(K-1-j.val) = j.val by omega]

theorem pastCellFrame_originalPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    pastCellFrame W β hβ δ r K e
        (originalPastRows δ r K (growingQueryTime δ (e.val+1))
          (fineCellStart_le_horizon δ hδ K e) z.2) =
      fineCellFrame W β hβ δ r K e z := by
  let a := growingQueryTime δ (e.val+1)
  let p := originalPastRows δ r K a (fineCellStart_le_horizon δ hδ K e) z.2
  have hi := paperStateBefore_frame_congr r (r+K) (Target W β hβ δ r K) (Update δ r K)
    (fun k p => pastTarget W β hβ δ a (K-1-k) p) (fun _ p _ => p)
    K (Initial δ r K z.2,1) (p,1) (Original δ r K z.2) (zeroStoppedNoise (r+K) K)
    rfl e.castSucc (by
      intro j hj
      have hj' : j.val < e.val := by simpa only [Fin.val_castSucc] using hj
      rw [pastTargetTrace_eq]
      change SourceTargets W β hβ δ r K z.2 j = _
      rw [sourceTargets_eq_mean_increment W β hβ δ hδ r K j z.2]
      unfold pastTarget
      have ht : growingQueryTime δ (j.val+1) ≤ a :=
        (growingQueryTime_strictMono δ hδ).monotone (by omega)
      have ht' : growingQueryTime δ j.val ≤ a :=
        ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)).trans ht
      rw [pastMeanAt_originalPastRows W β hβ δ r K a _ _ ht z.2,
        pastMeanAt_originalPastRows W β hβ δ r K a _ _ ht' z.2])
  exact congrArg (fun E : Matrix (Fin (r+(K-e.val))) (Fin (r+K)) ℝ =>
    fun i => E (Fin.cast (fineCellRank_rows r K e) i)) hi.symm

def cellPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K) :=
  fun i => (fineCellPastB W β hβ δ hδ r K e z i, fineCellPastD W β hβ δ hδ r K e z i)

theorem cellPastRows_eq_originalPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    cellPastRows W β hβ δ hδ r K e z =
      originalPastRows δ r K (growingQueryTime δ (e.val+1))
        (fineCellStart_le_horizon δ hδ K e) z.2 := rfl

theorem pastCellFrame_cellPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    pastCellFrame W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z) =
      fineCellFrame W β hβ δ r K e z :=
  pastCellFrame_originalPastRows W β hβ δ hδ r K e z

def pastCellEarlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K)) : Fin (r+K) → ℝ :=
  pastMeanAt W β hβ (growingQueryTime δ (e.val+1)) (growingQueryTime δ e.val) p -
    frameProjection (pastCellFrame W β hβ δ r K e p) *ᵥ
      pastMeanAt W β hβ (growingQueryTime δ (e.val+1)) (growingQueryTime δ e.val) p

theorem pastCellEarlierMean_cellPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    pastCellEarlierMean W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z) =
      fineCellEarlierMean W β hβ δ r K e z := by
  unfold pastCellEarlierMean
  rw [pastCellFrame_cellPastRows]
  have hm := pastMeanAt_originalPastRows W β hβ δ r K (growingQueryTime δ (e.val+1))
    (fineCellStart_le_horizon δ hδ K e) (growingQueryTime δ e.val)
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)) z.2
  change pastMeanAt W β hβ _ _ (cellPastRows W β hβ δ hδ r K e z) = _ at hm
  rw [hm]
  rfl

theorem pastCellFrame_kills_earlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K)) :
    pastCellFrame W β hβ δ r K e p *ᵥ pastCellEarlierMean W β hβ δ r K e p = 0 := by
  unfold pastCellEarlierMean
  rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,
    frame_mul_projection _ (pastCellFrame_orthogonal W β hβ δ r K e p),sub_self]

theorem measurable_pastCellEarlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) : Measurable (pastCellEarlierMean W β hβ δ r K e) := by
  have hm := measurable_pastMeanAt W β hβ (growingQueryTime δ (e.val+1))
    (growingQueryTime δ e.val) (r+K)
  have hP : Measurable (fun p => frameProjection (pastCellFrame W β hβ δ r K e p)) := by
    have hc : Continuous (frameProjection (m := fineCellRank r K e+1) (n := r+K)) := by
      unfold frameProjection
      fun_prop
    exact hc.measurable.comp (measurable_pastCellFrame W β hβ δ r K e)
  apply hm.sub
  apply Measurable.of_eval
  intro i
  change Measurable (fun p => ∑ j, frameProjection (pastCellFrame W β hβ δ r K e p) i j *
    pastMeanAt W β hβ _ _ p j)
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hP)).mul
      ((measurable_pi_apply j).comp hm)

theorem paperFrame_firstRow_cast {a b n : ℕ} (h : a=b)
    (E : Matrix (Fin (a+1)) (Fin n) ℝ) (F : Matrix (Fin (b+1)) (Fin n) ℝ)
    (v : Fin n → ℝ) (hEF : E = fun i => F (Fin.cast (congrArg (·+1) h) i)) :
    paperFrame E v 0 = paperFrame F v 0 := by
  subst b
  change E = F at hEF
  rw [hEF]

theorem paperQueryDirectionTrace_eq_frameBefore {Past : Type*} (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (e : Fin K) :
    paperQueryDirectionTrace r n N target update K s z e =
      normalizedQuery N (paperFrame
        (fun i : Fin (fineCellRank r K e+1) =>
          (paperStateBefore r n target update K s z e.castSucc).2
            (Fin.cast (fineCellRank_rows r K e) i))
        (paperTargetTrace r n target update K s z e) 0) := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · rfl
    · simp only [paperQueryDirectionTrace,paperTargetTrace,Fin.cases_succ]
      rw [ih]
      apply congrArg (normalizedQuery N)
      apply paperFrame_firstRow_cast (by unfold fineCellRank; simp only [Fin.val_succ]; omega)
      ext i j
      rfl

theorem fineCellDirection_eq_pastFrame_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
      paperQueryDirectionTrace r (r+K) (r+K : ℕ) (Target W β hβ δ r K) (Update δ r K) K
        (Initial δ r K z.2,1) (Original δ r K z.2) e =
      normalizedQuery (r+K : ℕ) (paperFrame
        (pastCellFrame W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z))
        (frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (pastCellEarlierMean W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z))
          (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)) 0) := by
  filter_upwards [fineCell_frozenTarget_eq_sourceTargets_ae W β hβ δ hδ r K e] with z hz
  rw [pastCellFrame_cellPastRows, pastCellEarlierMean_cellPastRows,funext hz]
  exact paperQueryDirectionTrace_eq_frameBefore r (r+K) (r+K : ℕ)
    (Target W β hβ δ r K) (Update δ r K) K (Initial δ r K z.2,1) (Original δ r K z.2) e

theorem fineCell_causal_frame_and_earlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    fineCellRank r K e + (e.val+1) = r+K ∧
    Measurable (pastCellFrame W β hβ δ r K e) ∧
    Measurable (pastCellEarlierMean W β hβ δ r K e) ∧
    (∀ p i k, dot (pastCellFrame W β hβ δ r K e p i)
      (pastCellFrame W β hβ δ r K e p k) = if i=k then 1 else 0) ∧
    (∀ p, pastCellFrame W β hβ δ r K e p *ᵥ pastCellEarlierMean W β hβ δ r K e p = 0) ∧
    (∀ z, pastCellFrame W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z) =
      fineCellFrame W β hβ δ r K e z) ∧
    (∀ z, pastCellEarlierMean W β hβ δ r K e (cellPastRows W β hβ δ hδ r K e z) =
      fineCellEarlierMean W β hβ δ r K e z) :=
  ⟨fineCellRank_dimension r K e, measurable_pastCellFrame W β hβ δ r K e,
    measurable_pastCellEarlierMean W β hβ δ r K e, pastCellFrame_orthogonal W β hβ δ r K e,
    pastCellFrame_kills_earlierMean W β hβ δ r K e,
    pastCellFrame_cellPastRows W β hβ δ hδ r K e, pastCellEarlierMean_cellPastRows W β hβ δ hδ r K e⟩

end SKConstants.Completion.N9T1
