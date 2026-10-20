module

public import SKConstants.Completion.Blueprint5.FineStatements
public import SKConstants.Completion.LM1b.SourceTrace
public import SKConstants.Completion.LM1b.TraceMeasurability
public import SKConstants.Completion.N9T1.Posterior
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 LC5 LM5 Blueprint5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def FineCellFrameStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r → ∀ e : Fin K,
    ∃ (m : ℕ) (_ : m + (e.val+1) = r+K)
      (E : (Fin (r+K) → Bool) × SourceInput δ r K → Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
      (m₀ : (Fin (r+K) → Bool) × SourceInput δ r K → Fin (r+K) → ℝ),
      Measurable E ∧ Measurable m₀ ∧
      (∀ z i k, dot (E z i) (E z k) = if i = k then 1 else 0) ∧
      (∀ z, E z *ᵥ m₀ z = 0) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        frameProjection (E z) = fineCellRemainingProjection W β hβ δ r K e z) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
        frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (m₀ z) (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
        SourceTargets W β hβ δ r K z.2 e i)

variable {Past : Type*}

def castPaperState {r n a b : ℕ} (h : a = b) (s : PaperState r n a Past) :
    PaperState r n b Past :=
  (s.1, fun i => s.2 (Fin.cast (congrArg (r + ·) h.symm) i))

@[simp] theorem castPaperState_past {r n a b : ℕ} (h : a = b) (s : PaperState r n a Past) :
    (castPaperState h s).1 = s.1 := rfl

@[simp] theorem castPaperState_projection {r n a b : ℕ} (h : a = b)
    (s : PaperState r n a Past) : frameProjection (castPaperState h s).2 = frameProjection s.2 := by
  subst b
  rfl

theorem castPaperState_orthogonal {r n a b : ℕ} (h : a = b) (s : PaperState r n a Past)
    (hs : ∀ i k, dot (s.2 i) (s.2 k) = if i=k then 1 else 0) :
    ∀ i k, dot ((castPaperState h s).2 i) ((castPaperState h s).2 k) =
      if i=k then 1 else 0 := by
  subst b
  exact hs

theorem measurable_castPaperState [MeasurableSpace Past] {r n a b : ℕ} (h : a = b) :
    Measurable (castPaperState (Past := Past) (r := r) (n := n) h) := by
  subst b
  exact measurable_id

def paperStateBefore (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      (e : Fin (K+1)) → PaperState r n (K-e.val) Past
  | 0, s, _, e => castPaperState (by omega) s
  | K+1, s, z, e =>
    Fin.cases (motive := fun e => PaperState r n (K+1-e.val) Past) s
      (fun e => castPaperState (by simp only [Fin.val_succ, Nat.succ_sub_succ_eq_sub])
        (paperStateBefore r n target update K
          (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2 e)) e

theorem paperStateBefore_past (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (e : Fin (K+1)) :
    (paperStateBefore r n target update K s z e).1 =
      paperScalarPastTrace r n target update K s z e := by
  induction K with
  | zero => rfl
  | succ K ih =>
    refine Fin.cases rfl (fun e => ?_) e
    simpa only [paperStateBefore, paperScalarPastTrace, Fin.cases_succ,
      castPaperState_past] using
      ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2 e

theorem paperStateBefore_projection (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (e : Fin (K+1)) :
    frameProjection (paperStateBefore r n target update K s z e).2 =
      paperRemainingProjectionTrace r n target update K s z e := by
  induction K with
  | zero => exact castPaperState_projection _ s
  | succ K ih =>
    refine Fin.cases rfl (fun e => ?_) e
    simpa only [paperStateBefore, paperRemainingProjectionTrace, Fin.cases_succ,
      castPaperState_projection] using
      ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2 e

theorem paperStateBefore_orthogonal (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (hs : ∀ i k, dot (s.2 i) (s.2 k) = if i = k then 1 else 0)
    (e : Fin (K+1)) :
    ∀ i k, dot ((paperStateBefore r n target update K s z e).2 i)
      ((paperStateBefore r n target update K s z e).2 k) = if i = k then 1 else 0 := by
  induction K with
  | zero => exact castPaperState_orthogonal _ s hs
  | succ K ih =>
    refine Fin.cases hs (fun e => ?_) e
    exact castPaperState_orthogonal (by simp only [Fin.val_succ, Nat.succ_sub_succ_eq_sub]) _
      (ih (update K s.1 z.1, tailRows (paperFrame s.2 (target K s.1))) z.2
        (tailRows_orthogonal _ (paperFrame_orthogonal _ _ hs)) e)

theorem measurable_paperStateBefore [MeasurableSpace Past] (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) (e : Fin (K+1)) :
    Measurable (fun x : PaperState r n K Past × StoppedNoise (Fin n) K =>
      paperStateBefore r n target update K x.1 x.2 e) := by
  induction K with
  | zero => exact (measurable_castPaperState _).comp measurable_fst
  | succ K ih =>
    refine Fin.cases measurable_fst (fun e => ?_) e
    have hF : Measurable (fun s : PaperState r n (K+1) Past => paperFrame s.2 (target K s.1)) :=
      Measurable.of_eval fun j => Measurable.of_eval fun k =>
        paperFrame_measurable (m := r+K) (n := n) (A := PaperState r n (K+1) Past)
          (fun s => s.2) (fun s => target K s.1)
          (fun _ _ => by fun_prop) (fun k => (ht K k).comp measurable_fst) j k
    have hNext : Measurable (fun x : PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1) =>
        ((update K x.1.1 x.2.1, tailRows (paperFrame x.1.2 (target K x.1.1))), x.2.2)) :=
      (((hu K).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
        (Measurable.of_eval fun j : Fin (r+K) => (measurable_pi_apply j.succ).comp
          (hF.comp measurable_fst))).prodMk measurable_snd.snd
    exact (measurable_castPaperState (by simp only [Fin.val_succ,
      Nat.succ_sub_succ_eq_sub])).comp ((ih e).comp hNext)

def fineCellRank (r K : ℕ) (e : Fin K) : ℕ := r + (K-(e.val+1))

theorem fineCellRank_dimension (r K : ℕ) (e : Fin K) :
    fineCellRank r K e + (e.val+1) = r+K := by
  unfold fineCellRank
  omega

theorem fineCellRank_rows (r K : ℕ) (e : Fin K) :
    fineCellRank r K e + 1 = r + (K-e.val) := by
  unfold fineCellRank
  omega

theorem frameProjection_castRows {a b n : ℕ} (h : a = b)
    (E : Matrix (Fin b) (Fin n) ℝ) :
    frameProjection (fun i : Fin a => E (Fin.cast h i)) = frameProjection E := by
  subst b
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

def fineCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    Matrix (Fin (fineCellRank r K e+1)) (Fin (r+K)) ℝ :=
  fun i => (paperStateBefore r (r+K) (Target W β hβ δ r K) (Update δ r K) K
    (Initial δ r K z.2,1) (Original δ r K z.2) e.castSucc).2
      (Fin.cast (fineCellRank_rows r K e) i)

theorem fineCellFrame_projection (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    frameProjection (fineCellFrame W β hβ δ r K e z) =
      fineCellRemainingProjection W β hβ δ r K e z := by
  exact (frameProjection_castRows (fineCellRank_rows r K e) _).trans
    (paperStateBefore_projection r (r+K) (Target W β hβ δ r K) (Update δ r K) K
      (Initial δ r K z.2,1) (Original δ r K z.2) e.castSucc)

theorem fineCellFrame_orthogonal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    ∀ i k, dot (fineCellFrame W β hβ δ r K e z i)
      (fineCellFrame W β hβ δ r K e z k) = if i = k then 1 else 0 := by
  intro i k
  have h := paperStateBefore_orthogonal r (r+K) (Target W β hβ δ r K) (Update δ r K) K
    (Initial δ r K z.2,1) (Original δ r K z.2)
    (by intro i k; simp [dot,Matrix.one_apply]) e.castSucc
  simpa only [fineCellFrame, Fin.cast_inj] using
    h (Fin.cast (fineCellRank_rows r K e) i) (Fin.cast (fineCellRank_rows r K e) k)

theorem measurable_fineCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellFrame W β hβ δ r K e) := by
  have hI : Measurable (Initial δ r K) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst
  have hO : Measurable (Original δ r K) :=
    (paperAugmentedOriginal_measurable (r+K) K).comp measurable_snd
  have hX : Measurable (fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
      ((Initial δ r K z.2,(1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)),Original δ r K z.2)) :=
    ((hI.comp measurable_snd).prodMk measurable_const).prodMk (hO.comp measurable_snd)
  have hS := (measurable_paperStateBefore r (r+K) (Target W β hβ δ r K) (Update δ r K)
    (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _
      (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) K e.castSucc).comp hX
  exact Measurable.of_eval fun i =>
    (measurable_pi_apply (Fin.cast (fineCellRank_rows r K e) i)).comp hS.snd

def fineCellEarlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : Fin (r+K) → ℝ :=
  sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) z.2 -
    frameProjection (fineCellFrame W β hβ δ r K e z) *ᵥ
      sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) z.2

theorem measurable_fineCellEarlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellEarlierMean W β hβ δ r K e) := by
  have hm := (measurable_sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val)).comp
    (measurable_snd : Measurable (Prod.snd :
      ((Fin (r+K) → Bool) × SourceInput δ r K) → SourceInput δ r K))
  have hE := measurable_fineCellFrame W β hβ δ r K e
  have hP : Measurable (fun z => frameProjection (fineCellFrame W β hβ δ r K e z)) := by
    have hcont : Continuous (frameProjection (m := fineCellRank r K e+1) (n := r+K)) := by
      unfold frameProjection
      fun_prop
    exact hcont.measurable.comp hE
  apply hm.sub
  apply Measurable.of_eval
  intro i
  change Measurable (fun z => ∑ j, frameProjection (fineCellFrame W β hβ δ r K e z) i j *
    sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) z.2 j)
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hP)).mul
      ((measurable_pi_apply j).comp hm)

theorem fineCellFrame_kills_earlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellFrame W β hβ δ r K e z *ᵥ fineCellEarlierMean W β hβ δ r K e z = 0 := by
  unfold fineCellEarlierMean
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    frame_mul_projection _ (fineCellFrame_orthogonal W β hβ δ r K e z), sub_self]

theorem fineCellEarlierMean_eq_sourceMeanAt_ae (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
      fineCellEarlierMean W β hβ δ r K e z =
        sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) z.2 := by
  filter_upwards [fineCellRemainingProjection_kills_sourceMeanAt_ae W β hβ δ hδ r K e]
    with z hz
  unfold fineCellEarlierMean
  rw [fineCellFrame_projection, hz, sub_zero]

theorem fineCell_frozenTarget_eq_sourceTargets_ae (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
      frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
        (fineCellEarlierMean W β hβ δ r K e z)
        (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
      SourceTargets W β hβ δ r K z.2 e i := by
  filter_upwards [fineCellEarlierMean_eq_sourceMeanAt_ae W β hβ δ hδ r K e] with z hz
  intro i
  rw [sourceTargets_eq_mean_increment W β hβ δ hδ r K e z.2]
  unfold frozenQueryTarget
  rw [hz, fixedPastPosterior_fineCell]

theorem fineCell_frame_and_earlierMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    fineCellRank r K e + (e.val+1) = r+K ∧
    Measurable (fineCellFrame W β hβ δ r K e) ∧
    Measurable (fineCellEarlierMean W β hβ δ r K e) ∧
    (∀ z i k, dot (fineCellFrame W β hβ δ r K e z i)
      (fineCellFrame W β hβ δ r K e z k) = if i=k then 1 else 0) ∧
    (∀ z, fineCellFrame W β hβ δ r K e z *ᵥ fineCellEarlierMean W β hβ δ r K e z = 0) ∧
    (∀ z, frameProjection (fineCellFrame W β hβ δ r K e z) =
      fineCellRemainingProjection W β hβ δ r K e z) ∧
    (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
      frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
        (fineCellEarlierMean W β hβ δ r K e z)
        (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
      SourceTargets W β hβ δ r K z.2 e i) :=
  ⟨fineCellRank_dimension r K e, measurable_fineCellFrame W β hβ δ r K e,
    measurable_fineCellEarlierMean W β hβ δ r K e,
    fineCellFrame_orthogonal W β hβ δ r K e, fineCellFrame_kills_earlierMean W β hβ δ r K e,
    fineCellFrame_projection W β hβ δ r K e,
    fineCell_frozenTarget_eq_sourceTargets_ae W β hβ δ hδ r K e⟩

end SKConstants.Completion.N9T1
