module
public import SKConstants.Completion.LM1b.Statements

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem scalarMeshSourceRun_static (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n q K : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (z : StoppedNoise (Fin n) K) :
    (proposalTerminalPast (scalarMeshPaperUpdate H δ τ n q) K s z).1 = s.1 := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih => exact ih (scalarMeshPaperUpdate H δ τ n q K s z.1) z.2

theorem scalarMeshSourceRun_B_prefix_of_before (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n q K : ℕ)
    (s : ScalarMeshPaperPast H δ τ n) (z : StoppedNoise (Fin n) K)
    (a : ℝ≥0) (hbefore : ∀ k < K, a ≤ τ (q-k))
    (i : Fin n) (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ) ≤ a) :
    (proposalTerminalPast (scalarMeshPaperUpdate H δ τ n q) K s z).2 i u = s.2 i u := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    rw [proposalTerminalPast]
    rw [ih (scalarMeshPaperUpdate H δ τ n q K s z.1) z.2
      (fun k hk => hbefore k (hk.trans (Nat.lt_succ_self K)))]
    exact scalarAppendQueryInterval_prefix H (δ (q-K)) (τ (q-K)) _ u
      (hu.trans (hbefore K (Nat.lt_succ_self K)))

theorem scalarMeshSourceTrace_static (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r n q : ℕ)
    (target : ℕ → ScalarMeshPaperPast H δ τ n → Fin n → ℝ)
    (K : ℕ) (s : PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (z : StoppedNoise (Fin n) K) (e : Fin (K+1)) :
    (paperScalarPastTrace r n target (scalarMeshPaperUpdate H δ τ n q) K s z e).1 = s.1.1 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    refine Fin.cases rfl (fun e => ?_) e
    exact ih (scalarMeshPaperUpdate H δ τ n q K s.1 z.1,
      tailRows (paperFrame s.2 (target K s.1))) z.2 e

theorem scalarMeshSourceTrace_prefix (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (r n q : ℕ) (target : ℕ → ScalarMeshPaperPast H δ τ n → Fin n → ℝ)
    (K : ℕ) (hK : K ≤ q) (s : PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (z : StoppedNoise (Fin n) K) (e : Fin (K+1)) (i : Fin n)
    (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ) ≤ τ (q-K+e.val+1)) :
    (paperScalarPastTrace r n target (scalarMeshPaperUpdate H δ τ n q) K s z e).2 i u =
      (proposalTerminalPast (scalarMeshPaperUpdate H δ τ n q) K s.1 z).2 i u := by
  induction K with
  | zero => rfl
  | succ K ih =>
    revert hu
    refine Fin.cases ?_ (fun e => ?_) e
    · intro hu
      have hidx : q-(K+1)+0+1 = q-K := by omega
      simp only [Fin.val_zero] at hu
      rw [hidx] at hu
      exact (scalarMeshSourceRun_B_prefix_of_before H δ τ n q (K+1) s.1 z (τ (q-K))
        (fun k hk => hτ (by omega)) i u hu).symm
    · intro hu
      have hidx : q-(K+1)+e.succ.val+1 = q-K+e.val+1 := by simp only [Fin.val_succ]; omega
      rw [hidx] at hu
      exact ih (by omega) (scalarMeshPaperUpdate H δ τ n q K s.1 z.1,
        tailRows (paperFrame s.2 (target K s.1))) z.2 e hu

theorem growingSource_prefix_eq_terminal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (s : SourceInput δ r₀ q)
    (e : Fin (q+1)) (i : Fin (Size r₀ q))
    (t : Icc (0 : ℝ) (Horizon δ q : ℝ))
    (ht : (t : ℝ) ≤ growingQueryTime δ (e.val+1)) :
    (paperScalarPastTrace r₀ (Size r₀ q) (Target W β hβ δ r₀ q) (Update δ r₀ q)
      q (Initial δ r₀ q s, 1) (Original δ r₀ q s) e).2 i t = (SourcePast δ r₀ q s).2 i t := by
  apply scalarMeshSourceTrace_prefix (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ).monotone r₀ (Size r₀ q) q
    (Target W β hβ δ r₀ q) q le_rfl (Initial δ r₀ q s, 1) (Original δ r₀ q s) e i t
  simpa using ht

theorem targetTraceIdentification_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    TargetTraceIdentificationStatement W β hβ δ r₀ q := by
  intro s e i
  let a := paperScalarPastTrace r₀ (Size r₀ q) (Target W β hβ δ r₀ q) (Update δ r₀ q)
    q (Initial δ r₀ q s, 1) (Original δ r₀ q s) e.castSucc
  have hm := (growingQueryTime_strictMono δ hδ).monotone
  have htH : growingQueryTime δ (e.val+1) ≤ Horizon δ q := hm (by exact Nat.succ_le_succ e.isLt.le)
  have haH : growingQueryTime δ e.val ≤ Horizon δ q := (hm (Nat.le_succ e.val)).trans htH
  have hp : ScalarMeshPastPrefixEq (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
      (Size r₀ q) (growingQueryTime δ (e.val+1)) a (SourcePast δ r₀ q s) := by
    have hs : a.1 = (SourcePast δ r₀ q s).1 :=
      (scalarMeshSourceTrace_static _ _ _ r₀ (Size r₀ q) q (Target W β hβ δ r₀ q) q
        (Initial δ r₀ q s, 1) (Original δ r₀ q s) e.castSucc).trans
        (scalarMeshSourceRun_static _ _ _ (Size r₀ q) q q (Initial δ r₀ q s) (Original δ r₀ q s)).symm
    exact ⟨congrArg Prod.fst hs, congrArg (fun x => x.2.2) hs,
      fun i u hu => growingSource_prefix_eq_terminal W β hβ δ hδ r₀ q s e.castSucc i u hu,
      fun i u _ => congrArg (fun c : ScalarContinuousPath (Horizon δ q) => c u)
        (congrFun (congrArg (fun x => x.2.1) hs) i)⟩
  have he : q-(q-1-e.val) = e.val+1 := by omega
  have hv : q-(q-1-e.val+1) = e.val := by omega
  have hT := congrFun (scalarMeshPaperTarget_eq_of_prefix (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
    (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β) (growingQueryTime δ))
    (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q) q (q-1-e.val)
    (growingQueryTime δ (e.val+1)) htH a (SourcePast δ r₀ q s) hp
    (by rw [he]) (by rw [hv]; exact hm (Nat.le_succ _))) i
  change paperTargetTrace _ _ _ _ _ _ _ _ _ = _
  rw [paperTargetTrace_eq_current_state]
  change Target W β hβ δ r₀ q (q-1-e.val) a i = _
  change scalarMeshPaperTarget _ _ _ _ _ _ _ _ _ _ _ _ _ a i = _
  rw [hT]
  dsimp only [scalarMeshPaperTarget, scalarMeshPaperQueryTime]
  rw [he, hv, actualParisiGrowingIncrementScale_eq_posterior W β hβ δ hδ (e.val+1) (by omega)]
  simp only [Nat.add_sub_cancel]
  rfl

theorem scalarGrowingSourceRun_endpoint (H δ : ℝ≥0) (hδ : 0 < δ) (n q : ℕ)
    (hH : growingQueryTime δ (q+1) ≤ H)
    (K : ℕ) (hK : K ≤ q) (s : ScalarGrowingPaperPast H δ n)
    (z : StoppedNoise (Fin n) K) (e : Fin K) (i : Fin n) :
    paperNoiseTrace n K z e (.inl i) =
      (let B := (proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K s z).2 i
       B (projIcc 0 (H : ℝ) H.coe_nonneg (growingQueryTime δ (q-K+e.val+2))) -
       B (projIcc 0 (H : ℝ) H.coe_nonneg (growingQueryTime δ (q-K+e.val+1)))) /
        Real.sqrt (growingQueryDuration δ (q-K+e.val+1)) := by
  have hm := (growingQueryTime_strictMono δ hδ).monotone
  induction K generalizing s with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    change EuclideanSpace ℝ (Fin n ⊕ Unit) × StoppedNoise (Fin n) K at z
    refine Fin.cases ?_ (fun e => ?_) e
    · have hj : q-(K+1)+0+1 = q-K := by omega
      have hj' : q-(K+1)+0+2 = q-K+1 := by omega
      simp only [Fin.val_zero, hj, hj', paperNoiseTrace, Fin.cases_zero]
      have htH : growingQueryTime δ (q-K+1) ≤ H := (hm (by omega)).trans hH
      have haH : growingQueryTime δ (q-K) ≤ H := (hm (by omega)).trans htH
      have he := scalarGrowingPaperUpdate_B_endpoint H δ hδ n q K s i z.1 htH
      let b := scalarGrowingPaperUpdate H δ n q K s z.1
      have hf (u : Icc (0 : ℝ) (H : ℝ)) (hu : (u : ℝ) ≤ growingQueryTime δ (q-K+1)) :
          (proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K b z.2).2 i u = b.2 i u :=
        scalarMeshSourceRun_B_prefix_of_before H (growingQueryDuration δ) (growingQueryTime δ)
          n q K b z.2 (growingQueryTime δ (q-K+1)) (fun k hk => hm (by omega)) i u hu
      have hb : b.2 i ⟨growingQueryTime δ (q-K), (growingQueryTime δ (q-K)).coe_nonneg, haH⟩ =
          s.2 i ⟨growingQueryTime δ (q-K), (growingQueryTime δ (q-K)).coe_nonneg, haH⟩ :=
        scalarAppendQueryInterval_prefix H (growingQueryDuration δ (q-K)) (growingQueryTime δ (q-K))
          _ _ le_rfl
      change z.1 (.inl i) =
        ((proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K b z.2).2 i
            (projIcc 0 (H : ℝ) H.coe_nonneg (growingQueryTime δ (q-K+1))) -
          (proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K b z.2).2 i
            (projIcc 0 (H : ℝ) H.coe_nonneg (growingQueryTime δ (q-K)))) / _
      have hp (j : ℕ) (hj : growingQueryTime δ j ≤ H) :
          projIcc (0 : ℝ) (H : ℝ) H.coe_nonneg (growingQueryTime δ j : ℝ) =
            (⟨growingQueryTime δ j, (growingQueryTime δ j).coe_nonneg, hj⟩ : Icc (0 : ℝ) (H : ℝ)) :=
        projIcc_of_mem _ ⟨(growingQueryTime δ j).coe_nonneg, hj⟩
      rw [hp _ htH, hp _ haH]
      rw [hf _ le_rfl, hf _ (by exact_mod_cast hm (Nat.le_succ (q-K))), hb, he]
      exact (mul_div_cancel_left₀ _ (Real.sqrt_ne_zero'.mpr (by
        exact_mod_cast growingQueryDuration_pos δ hδ (q-K)))).symm
    · have hj : q-(K+1)+e.succ.val+1 = q-K+e.val+1 := by simp only [Fin.val_succ]; omega
      have hj' : q-(K+1)+e.succ.val+2 = q-K+e.val+2 := by simp only [Fin.val_succ]; omega
      simpa only [paperNoiseTrace, Fin.cases_succ, proposalTerminalPast, hj, hj'] using
        ih (by omega) (scalarGrowingPaperUpdate H δ n q K s z.1) z.2 e

theorem endpointTraceIdentification_holds (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    EndpointTraceIdentificationStatement δ r₀ q := by
  intro s e i
  simpa only [SourceEndpoints, SourcePast, Update, Nat.sub_self, Nat.zero_add] using
    scalarGrowingSourceRun_endpoint (Horizon δ q) δ hδ (Size r₀ q) q le_rfl q le_rfl
      (Initial δ r₀ q s) (Original δ r₀ q s) e i

end SKConstants.M1
