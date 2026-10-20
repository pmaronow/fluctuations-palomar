module

public import SKConstants.Completion.N9T2b.HistoryEnergy
public import SKConstants.Completion.LM1b.SourceTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T2b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9 N9c Blueprint5 LC5 LM5
variable {Ω : Type*} [MeasurableSpace Ω]

def fineCellPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) :=
  fun i => (fineCellPastB W β hβ δ hδ r K e z i, fineCellPastD W β hβ δ hδ r K e z i)

theorem fineCellPastRows_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    fineCellPastRows W β hβ δ hδ r K e =
      driverPastRows (growingQueryTime δ (e.val+1)) (Horizon δ K)
        (fineCellStart_le_horizon δ hδ K e) (r+K) ∘ SourceHistories W β hβ δ r K := rfl

theorem measurable_fineCellPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellPastRows W β hβ δ hδ r K e) :=
  (measurable_driverPastRows _ _ _ _).comp (measurable_SourceHistories W β hβ δ r K)

def fineCellDirection (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : Fin (r+K) → ℝ :=
  paperQueryDirectionTrace r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K)
    (M1.Update δ r K) K (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) e

def fineCellProjectionAfter (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : Matrix (Fin (r+K)) (Fin (r+K)) ℝ :=
  paperRemainingProjectionTrace r (r+K) (M1.Target W β hβ δ r K)
    (M1.Update δ r K) K (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) e.succ

theorem remainingProjection_eq_sub_query (N : ℝ) (hN : 0 < N) {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ) :
    remainingProjection (paperFrame E t) = frameProjection E -
      N⁻¹ • Matrix.vecMulVec (normalizedQuery N (paperFrame E t 0))
        (normalizedQuery N (paperFrame E t 0)) := by
  rw [inverse_scale_query_outer N hN]
  have he := frameProjection_eq_first_add_remaining (paperFrame E t)
  rw [paperFrame_projection] at he
  rw [he]
  abel

theorem paperProjectionTrace_step {Past : Type*} (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) (e : Fin K) :
    paperRemainingProjectionTrace r n target update K s z e.succ =
      paperRemainingProjectionTrace r n target update K s z e.castSucc -
        N⁻¹ • Matrix.vecMulVec (paperQueryDirectionTrace r n N target update K s z e)
          (paperQueryDirectionTrace r n N target update K s z e) := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · change paperRemainingProjectionTrace r n target update K
        (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 0 =
          frameProjection s.2 - N⁻¹ • Matrix.vecMulVec
            (normalizedQuery N (paperFrame s.2 (target K s.1) 0))
            (normalizedQuery N (paperFrame s.2 (target K s.1) 0))
      rw [GaussianProposal.paperRemainingProjectionTrace_zero]
      exact remainingProjection_eq_sub_query N hN s.2 (target K s.1)
    · simpa only [paperRemainingProjectionTrace, paperQueryDirectionTrace,
        Fin.castSucc_succ, Fin.cases_succ] using
          ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 e

theorem fineCellProjectionAfter_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hn : 0 < r+K) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellProjectionAfter W β hβ δ r K e z = fineCellRemainingProjection W β hβ δ r K e z -
      (((r+K : ℕ) : ℝ)⁻¹) • Matrix.vecMulVec (fineCellDirection W β hβ δ r K e z)
        (fineCellDirection W β hβ δ r K e z) :=
  paperProjectionTrace_step r (r+K) (r+K : ℕ) (Nat.cast_pos.mpr hn)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) e

theorem historyCellEndpoint_cast (a h f H : ℝ≥0) (heq : a+(h+f) = H)
    (v : ScalarDriverHistory H) :
    historyCellEndpoint a h f (castDriverHistory heq.symm v) =
      (v.2.2.1 (projIcc 0 (H : ℝ) H.coe_nonneg ((a : ℝ)+h)) -
        v.2.2.1 (projIcc 0 (H : ℝ) H.coe_nonneg a)) / Real.sqrt h := by
  subst H
  have h₁ : (a : ℝ)+h ≤ (a+(h+f) : ℝ≥0) := by simp only [NNReal.coe_add]; linarith [f.coe_nonneg]
  have h₂ : (a : ℝ) ≤ (a+(h+f) : ℝ≥0) := by simp only [NNReal.coe_add]; linarith [h.coe_nonneg,f.coe_nonneg]
  rw [projIcc_of_mem _ ⟨add_nonneg a.coe_nonneg h.coe_nonneg,h₁⟩,
    projIcc_of_mem _ ⟨a.coe_nonneg,h₂⟩]
  rfl

theorem historyQueryRows_source (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) :
    historyQueryRows (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
        (Horizon δ K-growingQueryTime δ (e.val+2)) (Horizon δ K)
        (fineCell_horizon_eq δ hδ K e) (r+K) i (SourceHistories W β hβ δ r K z) =
      (signSpin z.1 i, SourceEndpoints δ r K z.2 e i) := by
  apply Prod.ext
  · rfl
  · dsimp only [historyQueryRows]
    rw [historyCellEndpoint_cast _ _ _ _ (fineCell_horizon_eq δ hδ K e),
      endpointTraceIdentification_holds δ hδ r K z.2 e i]
    have ht : growingQueryTime δ (e.val+1) + growingQueryDuration δ (e.val+1) =
        growingQueryTime δ (e.val+2) := by
      simpa only [show e.val+1+1 = e.val+2 by omega] using
        (growingQueryTime_succ δ (e.val+1)).symm
    have htR : (growingQueryTime δ (e.val+1) : ℝ) +
        (growingQueryDuration δ (e.val+1) : ℝ) = growingQueryTime δ (e.val+2) := by
      exact_mod_cast ht
    rw [htR]
    rfl

theorem paperEndpointTrace_eq_noise (n K : ℕ) (z : StoppedNoise (Fin n) K) :
    paperEndpointTrace n K z = paperNoiseTrace n K z := by
  induction K with
  | zero => funext e; exact Fin.elim0 e
  | succ K ih =>
    funext e
    refine Fin.cases rfl (fun e => ?_) e
    exact congrFun (ih z.2) e

theorem fineCellQueryEnergy_eq_history (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K) (e : Fin K) (m : ℕ)
    (E : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) →
      Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
    (m₀ : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) → Fin (r+K) → ℝ)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K)
    (hP : frameProjection (E (fineCellPastRows W β hβ δ hδ r K e z)) =
      fineCellRemainingProjection W β hβ δ r K e z)
    (hU : fineCellDirection W β hβ δ r K e z =
      normalizedQuery (r+K : ℕ) (paperFrame (E (fineCellPastRows W β hβ δ hδ r K e z))
        (frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (m₀ (fineCellPastRows W β hβ δ hδ r K e z))
          (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)) 0)) :
    fineCellQueryEnergy W β hβ δ r K e z =
      historyFrozenQueryEnergy W β hβ (growingQueryTime δ (e.val+1))
        (growingQueryDuration δ (e.val+1)) (Horizon δ K-growingQueryTime δ (e.val+2))
        (Horizon δ K) (fineCell_horizon_eq δ hδ K e) (fineCellStart_le_horizon δ hδ K e)
        (r+K) m (actualFineScale W β δ e.val) E m₀ (SourceHistories W β hβ δ r K z) := by
  let p := fineCellPastRows W β hβ δ hδ r K e z
  let t := frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
    (m₀ p) (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)
  have hA : fineCellProjectionAfter W β hβ δ r K e z = remainingProjection (paperFrame (E p) t) := by
    rw [fineCellProjectionAfter_eq W β hβ δ r K hn e z, ← hP, hU]
    exact (remainingProjection_eq_sub_query (r+K : ℕ) (Nat.cast_pos.mpr hn) (E p) t).symm
  unfold historyFrozenQueryEnergy
  rw [oneQueryEnergy_eq_product]
  simp only [spin, gaussian, historyQueryRows_source W β hβ δ hδ r K e z]
  unfold fineCellQueryEnergy paperOffColumnTrace
  rw [paperEndpointTrace_eq_noise]
  change ((((r+K : ℕ) : ℝ)⁻¹ * (signSpin z.1 ⬝ᵥ fineCellDirection W β hβ δ r K e z)) *
    (((r+K : ℕ) : ℝ)⁻¹ * (signSpin z.1 ⬝ᵥ
      (fineCellProjectionAfter W β hβ δ r K e z *ᵥ SourceEndpoints δ r K z.2 e)))) = _
  rw [hA, hU]
  congr 1
  congr 1
  exact dotProduct_comm _ _

end SKConstants.Completion.N9T2b
