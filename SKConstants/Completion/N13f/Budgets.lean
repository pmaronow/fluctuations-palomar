module

public import SKConstants.Completion.N13f.ExponentAbsorption
public import SKConstants.Completion.N13e.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LGram
variable {Ω : Type*} [MeasurableSpace Ω]

def coarseGramTailBudget (W : BrownianSystem Ω) (β : ℝ) (p : Parameters) (n : ℕ) : ℝ :=
  let k := queryCount p.a p.b n
  gramTailBudget n (k+(k+1))
    (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n) k))
    ((n : ℝ)^(-p.gamma))

def coarsePsiTailBudget (β : ℝ) (p : Parameters) (n : ℕ) : ℝ :=
  ordinaryPsiTailBudget n p.z (LM4b.psiMomentConstant β*(1+(readoutTime p.a p.b n : ℝ)))

def coarseCompletionTailBudget (p : Parameters) (n : ℕ) : ℝ :=
  2*Real.exp (-(n : ℝ)*((n : ℝ)^(-p.z))^2)

theorem coarse_schedule_bounds (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      queryCount p.a p.b n + 1 = stopIndex p.a p.b n ∧
      0 < rankCount p.a p.b n ∧
      ((queryCount p.a p.b n+(queryCount p.a p.b n+1) : ℕ) : ℝ) ≤ 17*(n : ℝ)^p.a ∧
      p.b*Real.log n ≤ (readoutTime p.a p.b n : ℝ) ∧
      (readoutTime p.a p.b n : ℝ) ≤ p.b*Real.log n+1 := by
  rcases hf with ⟨hfa, haf, hkf, hkfa, hkff, hkf1⟩
  have hb0 := hb.1
  have hbf := hb.2.1
  have ha0 : 0 < p.a := hkf.trans hkfa
  have ha1 : p.a < 1 := by linarith
  have hba : p.b/4 ≤ p.a := by linarith
  filter_upwards [schedule_eventually p.a p.b hb0 hba ha1] with n hn
  have hq : queryCount p.a p.b n ≤ stopIndex p.a p.b n := by
    unfold queryCount
    omega
  have hqR : (queryCount p.a p.b n : ℝ) ≤ 8*(n : ℝ)^p.a :=
    (Nat.cast_le.mpr hq).trans (stopIndex_le p.a p.b hb0 hba n (by omega))
  have hpow : 1 ≤ (n : ℝ)^p.a := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) ha0.le
  have hH := horizon_bounds p.a p.b hb0 hba n hn.1 hn.2.1
  refine ⟨hn.1, hn.2.1, hn.2.2, ?_, hH.1, hH.2⟩
  push_cast
  linarith

theorem coarseGramTailBudget_eventually
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, coarseGramTailBudget W β p n ≤
      Real.exp (-((n : ℝ)^(1-p.sb)))/4 := by
  rcases hb with ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  have ha0 : 0 < p.a := hkb.trans hka
  let ε := (p.sb-2*p.gamma-p.b/2)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hvar⟩ := mixedRowVarianceScale_log_horizon W β hβ p.b ε hb0.le hε
  have hsch := coarse_schedule_bounds p hf
    ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  have hd : ∀ᶠ n : ℕ in atTop,
      ((queryCount p.a p.b n+(queryCount p.a p.b n+1) : ℕ) : ℝ) ≤ 17*(n : ℝ)^p.a :=
    hsch.mono (fun _ hn => hn.2.2.2.1)
  have hv : ∀ᶠ n : ℕ in atTop,
      Concentration.squareVarianceScale
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime (meshSize p.a n)
          (queryCount p.a p.b n))) 3 ≤ C*(n : ℝ)^(p.b/2+ε) := by
    filter_upwards [hsch] with n hn
    apply hvar n (by omega) _
    have ht : growingQueryTime (meshSize p.a n) (queryCount p.a p.b n) ≤
        readoutTime p.a p.b n :=
      (growingQueryTime_strictMono _ (paperGrowingQueryMeshSize_pos p.a n (by omega))).monotone
        (Nat.le_succ _)
    exact (NNReal.coe_le_coe.mpr ht).trans hn.2.2.2.2.2
  exact gramTailBudget_eventually _ _ p.a p.gamma (p.b/2+ε) (1-p.sb) 17 C
    hγ.le (by norm_num) hC (by dsimp [ε]; linarith) (by dsimp [ε]; linarith)
    (by dsimp [ε]; linarith) hd hv

theorem coarsePsiTailBudget_eventually
    (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, coarsePsiTailBudget β p n ≤
      Real.exp (-((n : ℝ)^(1-p.sb)))/4 := by
  rcases hb with ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  have ha0 : 0 < p.a := hkb.trans hka
  let ε := (p.sb-2*p.z)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hK1 : 1 ≤ LM4b.psiMomentConstant β := by
    unfold LM4b.psiMomentConstant
    nlinarith
  have hK : 0 < LM4b.psiMomentConstant β := by linarith
  let C := LM4b.psiMomentConstant β*(2+p.b/ε)
  have hC : 0 < C := by dsimp [C]; positivity
  have hsch := coarse_schedule_bounds p hf
    ⟨hb0, hbf, hz, hγ, hkb, hkz, hkγ, hka, hkb', hzsb, hγsb, hasb⟩
  filter_upwards [hsch, exp_power_budget_absorb 0 (1-2*p.z-2*ε) (1-p.sb) 0
    (1/(8*C^2)) 2 (by dsimp [ε]; linarith) (by dsimp [ε]; linarith)
    (by dsimp [ε]; linarith) (by positivity) (by norm_num)] with n hn habs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hS1 : 1 ≤ LM4b.psiMomentConstant β*(1+(readoutTime p.a p.b n : ℝ)) := by
    nlinarith [(readoutTime p.a p.b n).coe_nonneg]
  have hS := mul_le_mul_of_nonneg_left
    (log_term_le (n : ℝ) _ p.b ε hn1 hb0.le hε hn.2.2.2.2.2) hK.le
  have ht := ordinaryPsiTailBudget_power_le n (by omega) p.z ε
    (LM4b.psiMomentConstant β*(1+(readoutTime p.a p.b n : ℝ))) C hz.le hS1 hC
    (by dsimp [C]; nlinarith [hS])
  exact ht.trans (by simpa only [zero_mul, zero_sub] using habs)

theorem coarseCompletionTailBudget_eventually (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop, coarseCompletionTailBudget p n ≤
      Real.exp (-((n : ℝ)^(1-p.sb)))/4 := by
  have hzsb : 2*p.z < p.sb := hb.2.2.2.2.2.2.2.2.2.1
  have ha0 : 0 < p.a := hf.2.2.1.trans hf.2.2.2.1
  have hasb : p.a < 1-p.sb := hb.2.2.2.2.2.2.2.2.2.2.2
  filter_upwards [exp_power_budget_absorb 0 (1-2*p.z) (1-p.sb) 0 1 2
    (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num),
    eventually_ge_atTop 1] with n habs hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ)*((n : ℝ)^(-p.z))^2 = (n : ℝ)^(1-2*p.z) := by
    rw [show 1-2*p.z = 1+(-p.z)*2 by ring, Real.rpow_add hn0,
      Real.rpow_one, Real.rpow_mul hn0.le, Real.rpow_two]
  simpa only [coarseCompletionTailBudget, neg_mul, hp, zero_mul, zero_sub, one_mul] using habs

theorem coarseFailureBudget_eventually
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop,
      coarseGramTailBudget W β p n + coarsePsiTailBudget β p n +
        coarseCompletionTailBudget p n ≤ Real.exp (-((n : ℝ)^(1-p.sb))) := by
  filter_upwards [coarseGramTailBudget_eventually W β hβ p hf hb,
    coarsePsiTailBudget_eventually β hβ p hf hb,
    coarseCompletionTailBudget_eventually p hf hb] with n hg hp hc
  linarith [Real.exp_pos (-((n : ℝ)^(1-p.sb)))]

end SKConstants.Completion.N13f
