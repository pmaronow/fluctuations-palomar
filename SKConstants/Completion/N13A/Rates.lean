module

public import SKConstants.Completion.N13A.Statements
public import SKConstants.Completion.Blueprint.AssemblyFine
public import SKConstants.Completion.LFine.EntropyPowers
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4

theorem coarse_exponent_margins {p : Parameters}
    (hf : FineExponents p) (hc : CoarseExponents4 p) :
    0 < p.a ∧ p.a < 1 ∧ 0 < p.z ∧ 0 < 1-p.sb ∧ p.kb < p.z ∧
      p.kb < p.a ∧ p.kb < p.b/2 ∧ p.kb < 2*p.gamma := by
  rcases hf with ⟨_, _, hk, hka, _, _⟩
  rcases hc with ⟨_, _, _, hkb, hkz, hza, hzb, hzγ, _, _, _, _, _, _, has⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    hkz, by linarith, by linarith, by linarith⟩

theorem exists_weighted_variance_saving {p : Parameters} (hc : CoarseExponents4 p) :
    ∃ w : ℝ, p.z < w ∧ w < 2*p.gamma ∧ 2*p.z-w < p.sb := by
  rcases hc with ⟨_, _, _, _, _, _, _, hzγ, _, _, _, _, hzw, _, _⟩
  refine ⟨(max p.z (2*p.z-p.sb) + 2*p.gamma)/2, ?_⟩
  have hm : max p.z (2*p.z-p.sb) < 2*p.gamma := max_lt hzγ (by linarith)
  have h1 := le_max_left p.z (2*p.z-p.sb)
  have h2 := le_max_right p.z (2*p.z-p.sb)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem eventually_coarse_lagMesh {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (p : Parameters)
    (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ LagMesh β (coarseMesh p n) (coarseCount p n) ∧
      p.b * Real.log (n : ℝ) ≤ (coarseTime p n : ℝ) := by
  have hm := coarse_exponent_margins hf hc
  have hb := hc.1
  have hba := hc.2.2.1
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
    ((parisiEquilibriumPhysicalEndpoint β : ℝ) / p.b)
  filter_upwards [schedule_eventually p.a p.b hb hba.le hm.2.1, hlog] with n hn hln
  have hn0 : 0 < n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hV := horizon_bounds p.a p.b hb hba.le n hn.1 hn.2.1
  refine ⟨hn.1, ⟨paperGrowingQueryMeshSize_pos p.a n hn0, ?_, ?_, ?_⟩, hV.1⟩
  · change (coarseMesh p n : ℝ) ≤ 1
    rw [paperGrowingQueryMeshSize_coe]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith [hm.1])
  · intro j hj
    change (growingQueryDuration (coarseMesh p n) j : ℝ) ≤ 1
    exact (duration_bound p.a p.b hb n hn.1 hn.2.1 j hj).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith))
  · change (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ (coarseTime p n : ℝ)
    have h := (div_le_iff₀ hb).mp hln
    change (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ Real.log (n:ℝ) * p.b at h
    have hVlo : p.b * Real.log (n:ℝ) ≤ (coarseTime p n : ℝ) := hV.1
    nlinarith

theorem eventually_coarse_susceptibility {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      actualParisiFullSusceptibilityExpected W β (coarseTime p n) ≤ C*(n : ℝ)^(-p.b/2) := by
  obtain ⟨C, hC, hp⟩ := susceptibility_exp_tail W β hβ
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_coarse_lagMesh W β p hf hc] with n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ C * Real.exp (-(coarseTime p n : ℝ)/2) := hp _ (NNReal.coe_nonneg _)
    _ ≤ C * Real.exp (Real.log (n:ℝ) * (-p.b/2)) := by
      gcongr
      linarith [hn.2.2]
    _ = _ := by rw [Real.rpow_def_of_pos hnR]

theorem eventually_coarse_depth_le_log (p : Parameters) :
    ∀ᶠ n : ℕ in atTop,
      ((paddingDepth (coarseCount p n)+1 : ℕ) : ℝ) ≤
        (1 / Real.log 2 + 2) * Real.log (n : ℝ) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop (1:ℕ)] with n hln hn
  change 1 ≤ Real.log (n:ℝ) at hln
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hcount : coarseCount p n ≤ n := min_le_right _ _
  have hcl : paddingDepth (coarseCount p n) ≤ Nat.clog 2 n := Nat.clog_mono_right 2 hcount
  have hlb : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hnR
  have hceil := (Nat.ceil_lt_add_one hlb)
  have hCeilEq : ⌈Real.logb (2:ℝ) (n:ℝ)⌉₊ = Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [hCeilEq] at hceil
  have hcast : (paddingDepth (coarseCount p n) : ℝ) ≤ (Nat.clog 2 n : ℝ) := by exact_mod_cast hcl
  simp only [Real.logb, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] at hceil ⊢
  nlinarith

theorem eventually_weighted_budget_le (C w : ℝ) (L : ℕ) (p : Parameters)
    (hw : w < 2*p.gamma) :
    ∀ᶠ n : ℕ in atTop,
      C*(n : ℝ)^(-2*p.gamma)*(Real.log (n : ℝ))^L ≤ (n : ℝ)^(-w) := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    LFine.eventually_log_power_mul_rpow_le C (-2*p.gamma) (-w) L (by linarith)

theorem eventually_weighted_remainder_le (C z : ℝ) (hC : 0 ≤ C) (L : ℕ) (p : Parameters)
    (hz : z < 2*p.gamma) :
    ∀ᶠ n : ℕ in atTop,
      200 * ((paddingDepth (coarseCount p n)+1 : ℕ) : ℝ) *
        (C*(n : ℝ)^(-2*p.gamma)*(Real.log (n : ℝ))^L) ≤ (n : ℝ)^(-z) := by
  filter_upwards [eventually_coarse_depth_le_log p,
    LFine.eventually_log_power_mul_rpow_le (200*(1/Real.log 2+2)*C)
      (-2*p.gamma) (-z) (L+1) (by linarith)] with n hD hbound
  have hlog := Real.log_natCast_nonneg n
  calc
    _ ≤ 200 * ((1/Real.log 2+2)*Real.log n) *
        (C*(n : ℝ)^(-2*p.gamma)*(Real.log (n : ℝ))^L) := by gcongr
    _ = 200*(1/Real.log 2+2)*C * (Real.log (n : ℝ))^(L+1) * (n : ℝ)^(-2*p.gamma) := by ring
    _ ≤ _ := hbound

theorem eventually_exp_rate_absorb (C κ e s M : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ)
    (he : 0 < e) (hse : s < e) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(κ*(n : ℝ)^e)) ≤ Real.exp (-(M*(n : ℝ)^s)) := by
  filter_upwards [constant_rpow_le_small_rpow s e M (κ/2) hse hM.le (by positivity),
    constant_rpow_le_small_rpow 0 e |Real.log (C+1)| (κ/2) he (abs_nonneg _) (by positivity)]
      with n h1 h2
  rw [Real.rpow_zero, mul_one] at h2
  have hkey : Real.log (C+1) - κ*(n : ℝ)^e ≤ -(M*(n : ℝ)^s) := by
    linarith [le_abs_self (Real.log (C+1))]
  calc
    _ ≤ (C+1) * Real.exp (-(κ*(n : ℝ)^e)) := by gcongr; linarith
    _ = Real.exp (Real.log (C+1) - κ*(n : ℝ)^e) := by
      rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := Real.exp_le_exp.mpr hkey

theorem eventually_four_failures (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop,
      4 * Real.exp (-(2*(n : ℝ)^s)) ≤ Real.exp (-((n : ℝ)^s)) := by
  filter_upwards [constant_rpow_le_small_rpow 0 s |Real.log 4| 1 hs (abs_nonneg _) (by norm_num)]
      with n hn
  rw [Real.rpow_zero, mul_one, one_mul] at hn
  calc
    _ = Real.exp (Real.log 4 - 2*(n : ℝ)^s) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<4), Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log 4)])

end SKConstants.Completion.N13A
