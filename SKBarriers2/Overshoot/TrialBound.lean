module

public import SKBarriers2.Overshoot.Schedule
public import SKBarriers2.Static.FractionalGuerra
public import OAI.Probability.SKBarriers.Scalar.DyadicPenalty

@[expose] public section

noncomputable section
open scoped BigOperators Matrix NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2.OW

section Terminal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_uniform_nonexpansive {f g : E → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {m ε : ℝ}
    (hm : 0 ≤ m) (hfg : ∀ x, |f x - g x| ≤ ε) (v x : E) :
    |vectorStep m v f x - vectorStep m v g x| ≤ ε := by
  exact gaussianStep_uniform_nonexpansive
    (hf.compCLM (vectorTranslation v)) (hg.compCLM (vectorTranslation v))
    hm (fun z => hfg (vectorTranslation v z)) x

theorem vectorIncrementChain_uniform_nonexpansive (l : List (ℝ × E))
    (hm : ∀ p ∈ l, 0 ≤ p.1) {f g : E → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {ε : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ ε) (x : E) :
    |vectorIncrementChain l f x - vectorIncrementChain l g x| ≤ ε := by
  induction l generalizing x with
  | nil => exact hfg x
  | cons p l ih =>
    exact vectorStep_uniform_nonexpansive (vectorIncrementChain_regular l hf)
      (vectorIncrementChain_regular l hg) (hm p List.mem_cons_self)
      (ih (fun q hq => hm q (List.mem_cons_of_mem p hq))) p.2 x

end Terminal

def outsideChain (α : ℝ → ℝ) (n : ℕ) (a b : ℝ) : List (ℝ × ℝ) :=
  rawTimeChain (dyadicIntervals α n a (Real.toNNReal (b - a)))

def trialChain (γ α : ℝ → ℝ) (p s h k : ℝ) (M n : ℕ) :
    List (ℝ × (Fin 3 → ℝ)) :=
  tripleCommonSchedule (outsideChain γ n 0 s) ++ window α p s h k M ++
    tripleTailSchedule (outsideChain α n (s + 4*h) 1)

private theorem outside_variance (α : ℝ → ℝ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    rawVariance (outsideChain α n a b) = b - a := by
  rw [outsideChain, rawVariance_rawTimeChain, dyadicIntervals_duration,
    Real.coe_toNNReal _ (sub_nonneg.mpr hab)]

private theorem common_covariance (l : List (ℝ × ℝ)) :
    matrixChainCovariance (tripleCommonSchedule l) = fun _ _ => rawVariance l := by
  have H := tripleCommonSchedule_covariance l 0
  have hz : tripleClockMatrix 0 0 0 0 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hz, zero_add] at H
  rw [H]
  ext i j; fin_cases i <;> fin_cases j <;> simp [tripleClockMatrix]

private theorem tail_covariance (l : List (ℝ × ℝ)) :
    matrixChainCovariance (tripleTailSchedule l) =
      rawVariance l • (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
  have H := tripleTailSchedule_covariance l 0 0 0 0 0 0 0 0
  have hz : tripleClockPerturbed 0 0 0 0 0 0 0 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [tripleClockPerturbed, tripleClockMatrix]
  rw [hz, zero_add] at H
  rw [H]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tripleClockPerturbed, tripleClockMatrix, Matrix.one_apply]

theorem trialChain_covariance (γ α : ℝ → ℝ) (p s h k : ℝ) {M : ℕ}
    (hM : 0 < M) (hs : 0 ≤ s) (hh : 0 ≤ h) (hT : s + 4*h ≤ 1)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ)) (n : ℕ) :
    matrixChainCovariance (trialChain γ α p s h k M n) =
      tripleGram (s+h) (h*k) (s+(1+p)*h) := by
  rw [trialChain, matrixChainCovariance_append, matrixChainCovariance_append,
    common_covariance, tail_covariance, outside_variance γ n hs,
    outside_variance α n hT, sub_zero]
  rw [show 1 - (s + 4*h) = 1-s-4*h by ring]
  exact window_full_covariance_admissible α p s h k hM hh hp hk

private theorem tail_block_diagonal (p : ℝ × ℝ) (Q : Fin 3 → Fin 3 → ℝ) (t : ℝ)
    (hQ : ∀ i, Q i i = t) :
    matrixChainPenalty (tripleTailBlock p) Q = 3 * p.1 * ((t+p.2^2)^2-t^2) := by
  simp [tripleTailBlock, matrixChainPenalty_cons, matrixChainPenalty_nil,
    matrixSquare, Fin.sum_univ_succ, rankOneMatrix, hQ]
  ring

private theorem tail_block_covariance_diagonal (p : ℝ × ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (t : ℝ) (hQ : ∀ i, Q i i = t) :
    ∀ i, (Q + matrixChainCovariance (tripleTailBlock p)) i i = t+p.2^2 := by
  intro i
  fin_cases i <;>
    simp [tripleTailBlock, matrixChainCovariance_cons, rankOneMatrix, hQ, pow_two]

private theorem tail_penalty_diagonal (l : List (ℝ × ℝ))
    (Q : Fin 3 → Fin 3 → ℝ) (t : ℝ) (hQ : ∀ i, Q i i = t) :
    matrixChainPenalty (tripleTailSchedule l) Q = 3 * rawPenalty l t := by
  induction l generalizing Q t with
  | nil => simp [tripleTailSchedule, rawPenalty, chainPotentialPenalty]
  | cons p l ih =>
    change matrixChainPenalty (tripleTailBlock p ++ tripleTailSchedule l) Q = _
    rw [matrixChainPenalty_append,
      tail_block_diagonal p Q t hQ,
      ih _ _ (tail_block_covariance_diagonal p Q t hQ)]
    simp only [rawPenalty, List.map_cons, chainPotentialPenalty]
    ring

private theorem common_penalty (l : List (ℝ × ℝ)) :
    matrixChainPenalty (tripleCommonSchedule l) 0 = 3 * rawPenalty l 0 := by
  have hz : tripleClockMatrix 0 0 0 0 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  simpa only [hz] using tripleCommonSchedule_penalty l 0

theorem window_endpoint_diagonal (α : ℝ → ℝ) (p s h k : ℝ) {M : ℕ}
    (hM : 0 < M) (hh : 0 ≤ h) (hp : p ∈ Icc (0 : ℝ) (1/2))
    (hk : |k| ≤ (1/2 : ℝ)) (i : Fin 3) :
    s + matrixChainCovariance (window α p s h k M) i i = s+4*h := by
  have H := congrFun (congrFun
    (window_full_covariance_admissible α p s h k hM hh hp hk) i) i
  have hd : tripleGram (s+h) (h*k) (s+(1+p)*h) i i = 1 := by
    fin_cases i <;> rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one,
    hd] at H
  linarith

theorem trialChain_penalty (γ α : ℝ → ℝ) (p s h k : ℝ) {M : ℕ}
    (hM : 0 < M) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ)) (n : ℕ) :
    matrixChainPenalty (trialChain γ α p s h k M n) 0 =
      3 * rawPenalty (outsideChain γ n 0 s) 0 +
      matrixChainPenalty (window α p s h k M) (fun _ _ => s) +
      3 * rawPenalty (outsideChain α n (s+4*h) 1) (s+4*h) := by
  rw [trialChain, matrixChainPenalty_append, matrixChainPenalty_append,
    matrixChainCovariance_append, common_penalty, common_covariance,
    outside_variance γ n hs, sub_zero, zero_add, zero_add]
  rw [tail_penalty_diagonal _ _ (s+4*h)
    (window_endpoint_diagonal α p s h k hM hh hp hk)]

private theorem sum_terminal_regular {φ : ℝ → ℝ} (hφ : BoundedDerivs φ) :
    BoundedDerivs (fun x : Fin 3 → ℝ => ∑ i, φ (x i)) := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    ((hφ.compCLM (tripleCoordinate 0)).add
      (hφ.compCLM (tripleCoordinate 1))).add (hφ.compCLM (tripleCoordinate 2))

theorem boundary_regular (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (p s h k : ℝ) (M : ℕ) (hT : s+4*h ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (boundary β α p s h k M) := by
  have ht : Real.toNNReal (1-(s+4*h)) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith [hT.1])
  have hφ : BoundedDerivs (Phi β α (s+4*h)) :=
    scalarCDFValue_regular β hα hm _ _ ht
  exact (vectorIncrementChain_regular _ (sum_terminal_regular hφ)).compCLM diagonalEmbedding

private theorem regular_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨C, D, hC, _, hb, _⟩ := hf.2
  refine ⟨⟨C,hC⟩, lipschitzWith_of_nnnorm_fderiv_le (hf.1.differentiable (by norm_num)) ?_⟩
  intro x
  exact_mod_cast hb x

private theorem outside_mass (α : ℝ → ℝ) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (n : ℕ) (a b : ℝ) : ∀ p ∈ outsideChain α n a b, p.1 ∈ Icc (0 : ℝ) 1 := by
  exact rawTimeChain_mass _ (fun _ hp => dyadicIntervals_mass_bounds hα n a _ hp)

private theorem scaled_nonneg {E : Type} [SMul ℝ E]
    (β : ℝ) (l : List (ℝ × E)) (hm : ∀ p ∈ l, 0 ≤ p.1) :
    ∀ p ∈ scaleIncrementChain β l, 0 ≤ p.1 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hm q hq

private theorem common_value (β : ℝ) (γ : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (f : (Fin 3 → ℝ) → ℝ) :
    vectorIncrementChain (scaleIncrementChain β
      (tripleCommonSchedule (outsideChain γ n 0 s))) f 0 =
      3 * dyadicScalar β γ n 0 (Real.toNNReal s)
        (fun z => f (fun _ => z) / 3) 0 := by
  rw [tripleCommonSchedule_scale]
  change vectorIncrementChain (tripleCommonSchedule (scaleIncrementChain β
    (outsideChain γ n 0 s))) f (fun _ => 0) = _
  rw [common_chain_diagonal _ f (fun z => f (fun _ => z) / 3) (fun z => by ring) 0,
    outsideChain, sub_zero, scalarIncrementChain_rawTimeChain]
  rfl

theorem trialChain_value_tendsto (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (p s h k : ℝ) (M : ℕ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hT : s+4*h ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => vectorIncrementChain
      (scaleIncrementChain β (trialChain γ α p s h k M n))
      (fun x => ∑ i : Fin 3, scalarSpinTerminal (x i)) 0) atTop
      (𝓝 (scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal s)
        (boundary β α p s h k M) 0)) := by
  let W := scaleIncrementChain β (window α p s h k M)
  let G : (Fin 3 → ℝ) → ℝ := fun x => ∑ i, Phi β α (s+4*h) (x i)
  let F := vectorIncrementChain W G
  let C := fun n => scaleIncrementChain β (tripleCommonSchedule (outsideChain γ n 0 s))
  let T := fun n => vectorIncrementChain
    (scaleIncrementChain β (tripleTailSchedule (outsideChain α n (s+4*h) 1)))
    (fun x => ∑ i : Fin 3, scalarSpinTerminal (x i))
  have ht : Real.toNNReal (1-(s+4*h)) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith [hT.1])
  have hG : BoundedDerivs G := sum_terminal_regular
    (scalarCDFValue_regular β hα hαm _ _ ht)
  have hF : BoundedDerivs F := vectorIncrementChain_regular W hG
  have hB := boundary_regular β α hα hαm p s h k M hT
  have hB3 : BoundedDerivs (fun z => boundary β α p s h k M z / 3) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hB.const_mul (1/3)
  obtain ⟨K,hK⟩ := regular_lipschitz hB3
  have hbase := ((dyadicScalar_general_uniform hB3 hK β hγ hγm 0
    (Real.toNNReal s) (Real.toNNReal_le_one.mpr hs.2)).tendsto_at 0).const_mul 3
  have hscale := scalarCDFOperator_div_three β γ hγ hγm 0 (Real.toNNReal s)
    (Real.toNNReal_le_one.mpr hs.2) hB3 hK 0
  have heB : (fun y => 3 * (boundary β α p s h k M y / 3)) =
      boundary β α p s h k M := by funext y; ring
  rw [heB] at hscale
  rw [← hscale] at hbase
  have hbase' : Tendsto (fun n => vectorIncrementChain (C n) F 0) atTop
      (𝓝 (scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal s)
        (boundary β α p s h k M) 0)) := by
    convert hbase using 1
    funext n
    exact common_value β γ n s F
  have herror (n : ℕ) (x : Fin 3 → ℝ) :
      |T n x - G x| ≤ 6 * scalarTimeMassConstant β * (1/2 : ℝ)^n := by
    dsimp [T]
    rw [tripleTailSchedule_scale, tail_factorization _ scalarSpinTerminal_regular]
    simp only [outsideChain, scalarIncrementChain_rawTimeChain]
    change |(∑ i : Fin 3, dyadicScalar β α n (s+4*h)
      (Real.toNNReal (1-(s+4*h))) scalarSpinTerminal (x i)) - ∑ i : Fin 3,
        Phi β α (s+4*h) (x i)| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin 3, |dyadicScalar β α n (s+4*h)
          (Real.toNNReal (1-(s+4*h))) scalarSpinTerminal (x i) -
            Phi β α (s+4*h) (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, 2 * scalarTimeMassConstant β * (1/2 : ℝ)^n :=
        Finset.sum_le_sum (fun i _ => dyadicScalar_value_error β hα hαm _ _ ht n (x i))
      _ = _ := by simp; ring
  have hclose (n : ℕ) :
      |vectorIncrementChain (scaleIncrementChain β (trialChain γ α p s h k M n))
        (fun x => ∑ i : Fin 3, scalarSpinTerminal (x i)) 0 -
          vectorIncrementChain (C n) F 0| ≤
        6 * scalarTimeMassConstant β * (1/2 : ℝ)^n := by
    have hW : ∀ q ∈ W, 0 ≤ q.1 := scaled_nonneg β _
      (fun q hq => (window_mass_mem α hα p s h k M q hq).1)
    have hC : ∀ q ∈ C n, 0 ≤ q.1 := by
      apply scaled_nonneg
      intro q hq
      obtain ⟨v,hv,hqv⟩ := tripleCommonSchedule_mem_mass hq
      rw [hqv]
      exact div_nonneg (outside_mass γ hγ n 0 s v hv).1 (by norm_num)
    have hTn : BoundedDerivs (T n) := vectorIncrementChain_regular _
      (sum_terminal_regular scalarSpinTerminal_regular)
    have H := vectorIncrementChain_uniform_nonexpansive (C n ++ W)
      (fun q hq => (List.mem_append.mp hq).elim (hC q) (hW q)) hTn hG (herror n) 0
    simpa only [trialChain, scaleIncrementChain_append, vectorIncrementChain_append,
      C, W, T, F] using H
  have hz : Tendsto (fun n => vectorIncrementChain
      (scaleIncrementChain β (trialChain γ α p s h k M n))
      (fun x => ∑ i : Fin 3, scalarSpinTerminal (x i)) 0 -
        vectorIncrementChain (C n) F 0) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hez : Tendsto (fun n : ℕ => 6 * scalarTimeMassConstant β * (1/2 : ℝ)^n)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
          (by norm_num : (1/2 : ℝ) < 1)).const_mul (6 * scalarTimeMassConstant β))
    simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hclose hez
  simpa only [sub_add_cancel, zero_add] using hz.add hbase'

private theorem outside_penalty_tendsto (α : ℝ → ℝ) (hm : Monotone α)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n => rawPenalty (outsideChain α n a b) a) atTop
      (𝓝 (2 * ∫ t in Icc a b, t * α t)) := by
  have he : a + (Real.toNNReal (b-a) : ℝ) = b := by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab)]; ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H (n : ℕ) := dyadicPenalty_error hm n a (Real.toNNReal (b-a)) ha (by rw [he]; exact hb)
  simp only [he, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at H
  have hz : Tendsto (fun n : ℕ =>
      2 * (Real.toNNReal (b-a) : ℝ) / (2 : ℝ)^n * (α b - α a)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).mul_const (α b - α a))
  simpa only [outsideChain, rawPenalty_rawTimeChain, Real.norm_eq_abs] using
    squeeze_zero (fun _ => abs_nonneg _) H hz

theorem trialChain_penalty_tendsto (γ α : ℝ → ℝ) (hγm : Monotone γ) (hαm : Monotone α)
    (p s h k : ℝ) {M : ℕ} (hM : 0 < M) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hT : s+4*h ≤ 1) (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ)) :
    Tendsto (fun n => matrixChainPenalty (trialChain γ α p s h k M n) 0) atTop
      (𝓝 (penalty γ α p s h k M)) := by
  have h₁ := (outside_penalty_tendsto γ hγm 0 s le_rfl hs (by linarith)).const_mul 3
  have h₂ := (outside_penalty_tendsto α hαm (s+4*h) 1 (by linarith) hT le_rfl).const_mul 3
  have H := (h₁.add_const (matrixChainPenalty (window α p s h k M) (fun _ _ => s))).add h₂
  have he : penalty γ α p s h k M =
      3 * (2 * ∫ t in Icc (0 : ℝ) s, t * γ t) +
        matrixChainPenalty (window α p s h k M) (fun _ _ => s) +
          3 * (2 * ∫ t in Icc (s+4*h) 1, t * α t) := by
    unfold penalty
    ring
  simpa only [trialChain_penalty γ α p s h k hM hs hh hp hk, he] using H

private theorem grid_mass_between (α : ℝ → ℝ) (hm : Monotone α)
    (ha : ∀ t, 0 ≤ α t) (s h a len c : ℝ) {M j : ℕ} (hj : j < M)
    (hh : 0 ≤ h) (ha0 : 0 ≤ a) (hlen : 0 ≤ len) (ha4 : a+len ≤ 4)
    (hc : c ∈ Icc (1 : ℝ) 3) :
    α (s+h*(a+len*(j:ℝ)/(M:ℝ))) / c ∈ Icc (α s / 3) (α (s+4*h)) := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le j) hj)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (j : ℝ) / M ≤ 1 := (div_le_one hM).mpr (Nat.cast_le.mpr hj.le)
  have hjn : 0 ≤ (j : ℝ) / M := div_nonneg hj0 hM.le
  have htime : s ≤ s+h*(a+len*(j:ℝ)/(M:ℝ)) ∧
      s+h*(a+len*(j:ℝ)/(M:ℝ)) ≤ s+4*h := by
    rw [mul_div_assoc]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg hh (by positivity))
    · have H : a + len * ((j : ℝ) / M) ≤ 4 := by nlinarith
      nlinarith [mul_nonneg hh (sub_nonneg.mpr H)]
  have hcp : 0 < c := lt_of_lt_of_le (by norm_num) hc.1
  constructor
  · exact (div_le_div_of_nonneg_left (ha s) hcp hc.2).trans
      (div_le_div_of_nonneg_right (hm htime.1) hcp.le)
  · exact (div_le_self (ha _) hc.1).trans (hm htime.2)

theorem window_mass_between (α : ℝ → ℝ) (hm : Monotone α)
    (ha : ∀ t, 0 ≤ α t) (p s h k : ℝ) (M : ℕ) (hh : 0 ≤ h)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ))
    (q : ℝ × (Fin 3 → ℝ)) (hq : q ∈ window α p s h k M) :
    q.1 ∈ Icc (α s / 3) (α (s+4*h)) := by
  have hl := repairLength_mem hp hk
  have H (a len c : ℝ) (vs : List (Fin 3 → ℝ))
      (ha0 : 0 ≤ a) (hlen : 0 ≤ len) (ha4 : a+len ≤ 4)
      (hc : c ∈ Icc (1 : ℝ) 3)
      (hq : q ∈ windowGrid α s h M a len c vs) :
      q.1 ∈ Icc (α s / 3) (α (s+4*h)) := by
    obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hq
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact grid_mass_between α hm ha s h a len c (List.mem_range.mp hj)
      hh ha0 hlen ha4 hc
  rw [window_eq] at hq
  simp only [List.mem_append] at hq
  rcases hq with ((((hq | hq) | hq) | hq) | hq) | hq
  · exact H 0 1 3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq
  · exact H 1 p 2 _ (by norm_num) hp.1 (by linarith [hp.2]) (by norm_num) hq
  · exact H 1 p 1 _ (by norm_num) hp.1 (by linarith [hp.2]) (by norm_num) hq
  · exact H (1+p) (1-p) 1 _ (by linarith [hp.1]) (by linarith [hp.2])
      (by linarith) (by norm_num) hq
  · obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hq
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact grid_mass_between α hm ha s h 2 (repairLength p k) 1
      (List.mem_range.mp hj) hh (by norm_num) hl.1 (by linarith [hl.2]) (by norm_num)
  · exact H (2+repairLength p k) (2-repairLength p k) 1 _
      (by linarith [hl.1]) (by linarith [hl.2]) (by linarith) (by norm_num) hq

private theorem outside_mass_between (α : ℝ → ℝ) (hm : Monotone α)
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) (q : ℝ × ℝ) (hq : q ∈ outsideChain α n a b) :
    q.1 ∈ Icc (α a) (α b) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have H := dyadicIntervals_mem_bounds hm n a (Real.toNNReal (b-a)) hv
  have he : a+(Real.toNNReal (b-a) : ℝ) = b := by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab)]; ring
  exact ⟨H.1, he ▸ H.2.1⟩

private theorem outside_sorted (α : ℝ → ℝ) (hm : Monotone α) (n : ℕ) (a b : ℝ) :
    (outsideChain α n a b).Pairwise (fun p q => p.1 ≤ q.1) := by
  exact rawTimeChain_sorted _ (dyadicIntervals_pairwise hm n a _)

theorem trialChain_admissible (γ α : ℝ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hγ : ∀ t, γ t ∈ Icc (3*θ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (p s h k : ℝ) (M n : ℕ) (hs : 0 ≤ s) (hh : 0 ≤ h) (hT : s+4*h ≤ 1)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ))
    (heq : γ s = α s) (hsep : α (s+h*(1+p))/2 ≤ α (s+h)) :
    (∀ q ∈ trialChain γ α p s h k M n, q.1 ∈ Icc θ 1) ∧
      (trialChain γ α p s h k M n).Pairwise (fun q v => q.1 ≤ v.1) := by
  have hγ0 : ∀ t, γ t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨(by linarith [(hγ t).1]), (hγ t).2⟩
  have hα0 : ∀ t, 0 ≤ α t := fun t => (hα t).1
  have hstart : 3*θ ≤ α s := heq ▸ (hγ s).1
  have hTs : s ≤ s+4*h := by linarith
  have hmassC (q) (hq : q ∈ tripleCommonSchedule (outsideChain γ n 0 s)) :
      q.1 ∈ Icc θ 1 := by
    obtain ⟨v,hv,hqv⟩ := tripleCommonSchedule_mem_mass hq
    have H := outside_mass γ hγ0 n 0 s v hv
    have Hlow := outside_mass_between γ hγm n 0 s hs v hv
    rw [hqv]
    constructor <;> linarith [(hγ 0).1, Hlow.1, H.2]
  have hmassW (q) (hq : q ∈ window α p s h k M) : q.1 ∈ Icc θ 1 := by
    have H := window_mass_between α hαm hα0 p s h k M hh hp hk q hq
    exact ⟨by linarith [H.1], (window_mass_mem α hα p s h k M q hq).2⟩
  have hmassT (q) (hq : q ∈ tripleTailSchedule (outsideChain α n (s+4*h) 1)) :
      q.1 ∈ Icc θ 1 := by
    obtain ⟨v,hv,hqv⟩ := tripleTailSchedule_mem_mass hq
    have H := outside_mass_between α hαm n (s+4*h) 1 hT v hv
    rw [hqv]
    exact ⟨by linarith [H.1, hαm hTs], (outside_mass α hα n _ _ v hv).2⟩
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact (List.mem_append.mp hq).elim (hmassC q) (hmassW q)
    · exact hmassT q hq
  · have hC : (tripleCommonSchedule (outsideChain γ n 0 s)).Pairwise
        (fun q v => q.1 ≤ v.1) := by
      rw [tripleCommonSchedule, List.pairwise_map]
      exact (outside_sorted γ hγm n 0 s).imp
        (fun hqv => div_le_div_of_nonneg_right hqv (by norm_num))
    have hW := window_mass_sorted α hαm hα0 p s h k M hh
      ⟨hp.1, by linarith [hp.2]⟩ (repairLength_mem hp hk) hsep
    have htail := tripleTailSchedule_monotone _ (outside_sorted α hαm n (s+4*h) 1)
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨hC,hW,?_⟩,htail,?_⟩
    · intro q hq v hv
      obtain ⟨a,ha,hqa⟩ := tripleCommonSchedule_mem_mass hq
      have H := outside_mass_between γ hγm n 0 s hs a ha
      have HV := window_mass_between α hαm hα0 p s h k M hh hp hk v hv
      rw [hqa]
      rw [heq] at H
      linarith [H.2, HV.1]
    · intro q hq v hv
      obtain ⟨b,hb,hvb⟩ := tripleTailSchedule_mem_mass hv
      have HB := outside_mass_between α hαm n (s+4*h) 1 hT b hb
      rw [hvb]
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨a,ha,hqa⟩ := tripleCommonSchedule_mem_mass hq
        have HA := outside_mass_between γ hγm n 0 s hs a ha
        rw [hqa, heq] at *
        linarith [HA.2, HB.1, hαm hTs, (hα s).1]
      · exact (window_mass_between α hαm hα0 p s h k M hh hp hk q hq).2.trans HB.1

theorem matrixConstrainedPressure_window {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (β : ℝ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (p s h k : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (hT : s+4*h ≤ 1)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ))
    (heq : γ s = α s) (hsep : α (s+h*(1+p))/2 ≤ α (s+h))
    (hD : Nonempty (MatrixStates N 3 (tripleGram (s+h) (h*k) (s+(1+p)*h)))) :
    matrixConstrainedPressure N 3 β (tripleGram (s+h) (h*k) (s+(1+p)*h)) ≤
      scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal s)
        (boundary β α p s h k M) 0 - β^2/4 * penalty γ α p s h k M := by
  have hv := trialChain_value_tendsto β γ α hγ hγm hα hαm p s h k M
    ⟨hs, by linarith⟩ ⟨by linarith, hT⟩
  have hp' := trialChain_penalty_tendsto γ α hγm hαm p s h k hM hs hh hT hp hk
  apply ge_of_tendsto (hv.sub (hp'.const_mul (β^2/4)))
  apply Eventually.of_forall
  intro n
  have ha := trialChain_admissible γ α 0 le_rfl (by simpa using hγ) hγm hα hαm
    p s h k M n hs hh hT hp hk heq hsep
  have H := matrixConstrainedPressure_chain hN β _ hD
    (trialChain γ α p s h k M n) ha.1 ha.2
  have hc := trialChain_covariance γ α p s h k hM hs hh hT hp hk n
  have hz : (fun i j => tripleGram (s+h) (h*k) (s+(1+p)*h) i j -
      matrixChainCovariance (trialChain γ α p s h k M n) i j) = 0 := by
    rw [hc]; ext i j; exact sub_self _
  have hsq : matrixSquare 3 (fun i j => tripleGram (s+h) (h*k) (s+(1+p)*h) i j -
      matrixChainCovariance (trialChain γ α p s h k M n) i j) = 0 := by
    rw [hz]
    simp only [matrixSquare, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  rw [hsq] at H
  simpa only [scaleIncrementChain, mul_zero, add_zero, Nat.cast_ofNat] using H

theorem fractionalPressure_window {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (β θ : ℝ) (hθ : 0 < θ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (3*θ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (p s h k : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (hT : s+4*h ≤ 1)
    (hp : p ∈ Icc (0 : ℝ) (1/2)) (hk : |k| ≤ (1/2 : ℝ))
    (heq : γ s = α s) (hsep : α (s+h*(1+p))/2 ≤ α (s+h))
    (hD : Nonempty (MatrixStates N 3 (tripleGram (s+h) (h*k) (s+(1+p)*h)))) :
    fractionalPressure N 3 β θ (tripleGram (s+h) (h*k) (s+(1+p)*h)) +
      β^2 * (3 : ℝ)^2 * θ / (4*(N : ℝ)) ≤
      scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal s)
        (boundary β α p s h k M) 0 - β^2/4 * penalty γ α p s h k M := by
  have hγ0 : ∀ t, γ t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨by linarith [(hγ t).1], (hγ t).2⟩
  have hθ1 : θ ≤ 1 := by linarith [(hγ 0).1, (hγ 0).2]
  have hv := trialChain_value_tendsto β γ α hγ0 hγm hα hαm p s h k M
    ⟨hs, by linarith⟩ ⟨by linarith, hT⟩
  have hp' := trialChain_penalty_tendsto γ α hγm hαm p s h k hM hs hh hT hp hk
  apply ge_of_tendsto (hv.sub (hp'.const_mul (β^2/4)))
  apply Eventually.of_forall
  intro n
  have ha := trialChain_admissible γ α θ hθ.le hγ hγm hα hαm
    p s h k M n hs hh hT hp hk heq hsep
  have H := fractionalPressure_chain hN β θ hθ hθ1 _ hD
    (trialChain γ α p s h k M n) ha.1 ha.2
  have hc := trialChain_covariance γ α p s h k hM hs hh hT hp hk n
  have hz : (fun i j => tripleGram (s+h) (h*k) (s+(1+p)*h) i j -
      matrixChainCovariance (trialChain γ α p s h k M n) i j) = 0 := by
    rw [hc]; ext i j; exact sub_self _
  have hsq : matrixSquare 3 (fun i j => tripleGram (s+h) (h*k) (s+(1+p)*h) i j -
      matrixChainCovariance (trialChain γ α p s h k M n) i j) = 0 := by
    rw [hz]
    simp only [matrixSquare, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  rw [hsq] at H
  simpa only [scaleIncrementChain, mul_zero, add_zero, Nat.cast_ofNat] using H

theorem matrixConstrainedPressure_trialValue {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (β : ℝ) (α : ℝ → ℝ) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (r d δ : ℝ) (hd : 0 < d) (hs : 0 ≤ r-2*d) (hT : r+6*d ≤ 1)
    (hk : |δ/(2*d)| ≤ (1/2 : ℝ)) (hsep : α (r+d)/2 ≤ α r)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ (r+d)))) :
    matrixConstrainedPressure N 3 β (tripleGram r δ (r+d)) ≤
      trialValue β α α r d δ M := by
  have hr : r-2*d+2*d = r := by ring
  have hq : r-2*d+(1+(1/2 : ℝ))*(2*d) = r+d := by ring
  have hδ : 2*d*(δ/(2*d)) = δ := by field_simp [ne_of_gt hd]
  have htime : r-2*d+4*(2*d) = r+6*d := by ring
  have hsep' : α (r-2*d+(2*d)*(1+(1/2 : ℝ)))/2 ≤ α (r-2*d+2*d) := by
    simpa only [hr, show r-2*d+(2*d)*(1+(1/2 : ℝ)) = r+d by ring] using hsep
  have H := matrixConstrainedPressure_window hN hM β α α hα hαm hα hαm
    (1/2) (r-2*d) (2*d) (δ/(2*d)) hs (by linarith)
    (by rw [htime]; exact hT) (by norm_num) hk rfl hsep'
    (by simpa only [hr,hq,hδ] using hD)
  simpa only [hr,hq,hδ,trialValue] using H

theorem fractionalPressure_trialValue {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (β θ : ℝ) (hθ : 0 < θ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (3*θ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (r d δ : ℝ) (hd : 0 < d) (hs : 0 ≤ r-2*d) (hT : r+6*d ≤ 1)
    (hk : |δ/(2*d)| ≤ (1/2 : ℝ)) (hsep : α (r+d)/2 ≤ α r)
    (heq : ∀ t ∈ Icc (r-2*d) 1, γ t = α t)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ (r+d)))) :
    fractionalPressure N 3 β θ (tripleGram r δ (r+d)) +
      β^2 * (3 : ℝ)^2 * θ / (4*(N : ℝ)) ≤ trialValue β γ α r d δ M := by
  have hr : r-2*d+2*d = r := by ring
  have hq : r-2*d+(1+(1/2 : ℝ))*(2*d) = r+d := by ring
  have hδ : 2*d*(δ/(2*d)) = δ := by field_simp [ne_of_gt hd]
  have htime : r-2*d+4*(2*d) = r+6*d := by ring
  have hsep' : α (r-2*d+(2*d)*(1+(1/2 : ℝ)))/2 ≤ α (r-2*d+2*d) := by
    simpa only [hr, show r-2*d+(2*d)*(1+(1/2 : ℝ)) = r+d by ring] using hsep
  have H := fractionalPressure_window hN hM β θ hθ γ α hγ hγm hα hαm
    (1/2) (r-2*d) (2*d) (δ/(2*d)) hs (by linarith)
    (by rw [htime]; exact hT) (by norm_num) hk
    (heq _ ⟨le_rfl, by linarith⟩) hsep'
    (by simpa only [hr,hq,hδ] using hD)
  simpa only [hr,hq,hδ,trialValue] using H

theorem fractionalPressure_le_trialValue {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (β θ : ℝ) (hθ : 0 < θ) (γ α : ℝ → ℝ)
    (hγ : ∀ t, γ t ∈ Icc (3*θ) 1) (hγm : Monotone γ)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (r d δ : ℝ) (hd : 0 < d) (hs : 0 ≤ r-2*d) (hT : r+6*d ≤ 1)
    (hk : |δ/(2*d)| ≤ (1/2 : ℝ)) (hsep : α (r+d)/2 ≤ α r)
    (heq : ∀ t ∈ Icc (r-2*d) 1, γ t = α t)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ (r+d)))) :
    fractionalPressure N 3 β θ (tripleGram r δ (r+d)) ≤ trialValue β γ α r d δ M := by
  have H := fractionalPressure_trialValue hN hM β θ hθ γ α hγ hγm hα hαm
    r d δ hd hs hT hk hsep heq hD
  have hc : 0 ≤ β^2 * (3 : ℝ)^2 * θ / (4*(N : ℝ)) := by positivity
  exact (le_add_of_nonneg_right hc).trans H

end SKBarriers2.OW
