module

public import ComparisonActualHighOnlyConditionalFiniteBudgetJoin
public import ComparisonActualHighOnlyConditionalCanonicalOrdinaryConsumer
public import ComparisonActualHighOnlyConditionalSamplerBroadConsumer
public import ComparisonActualHighOnlyConditionalInitialCapLimit
public import ComparisonActualHighOnlyConditionalNearZeroError

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

def conditionalFinitePhysicalCoefficient (D:ℝ):ℝ:=4+6*(((1+Real.log (1+D^2))/Real.log 2)+2)

theorem conditionalFinitePhysicalCoefficient_ge_four (D:ℝ):4 ≤ conditionalFinitePhysicalCoefficient D := by
  have HL:0 ≤ Real.log (1+D^2):=Real.log_nonneg (by nlinarith only [sq_nonneg D])
  have H2:0 < Real.log (2:ℝ):=Real.log_pos (by norm_num)
  have HC:0 ≤ (1+Real.log (1+D^2))/Real.log 2:=div_nonneg (by linarith only [HL]) H2.le
  unfold conditionalFinitePhysicalCoefficient
  linarith only [HC]

theorem eventually_actual_conditional_finite_physical_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential),
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀F:Finset (ordConnectedSection P.negativeSet),
      a.errorMaskIntegral (Ioo (0:ℝ) 1∩((⋃t:F,Ioo (P.capFamily F t).left (P.capFamily F t).right)∪P.contactSet)) ≤
        4*(a.data.N^(3*delta)*a.data.E)+conditionalFinitePhysicalCoefficient D*Real.log a.data.N*
          (a.data.N^(7*delta)*a.data.E) := by
  have HR:=eventually_actual_conditional_near_zero_error_high_only Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=eventually_actual_conditional_finite_wall_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HI:=eventually_actual_conditional_small_initial_cap_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HO:=eventually_actual_conditional_canonical_ordinary_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HB:=eventually_actual_conditional_sampler_broad_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have HL:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [HR,HW,HI,HO,HB,HL,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnR hnW hnI hnO hnB hnL hnScalar
  intro a hs hsxs hd1 hxs hy P hclock F
  have hN:1 ≤ a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnL
  have hscalar:=hnScalar a hd1
  have hE:=a.data.hE
  have hNpos:=a.data.hN
  have hB0:0 ≤ a.data.N^(7*delta)*a.data.E:=by positivity
  have hR0:0 ≤ a.data.N^(3*delta)*a.data.E:=by positivity
  have H67:a.data.N^(6*delta)*a.data.E ≤ a.data.N^(7*delta)*a.data.E:=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hE.le
  have hRaw:=hnR a hd1 hs hsxs hxs
  have hWall:a.data.U ≤ a.data.s → a.errorMaskIntegral (P.conditionalWallSupport F) ≤ a.data.N^(7*delta)*a.data.E:=
    fun hUs=>hnW a hs hsxs hUs hd1 hxs hy P hclock F
  have hInit:a.data.U ≤ a.data.s → ∀t:F,(P.capFamily F t).left=0 → a.alpha.val.val (P.capFamily F t).right ≤ 16*a.data.s →
      a.errorMaskIntegral (Ioo (P.capFamily F t).left (P.capFamily F t).right) ≤ a.data.N^(7*delta)*a.data.E:=by
    intro hUs t hleft hupper
    have HE:=hnI a hs hsxs hUs hd1 hxs hy P (P.capFamily F t) hleft (P.capFamily_contacts F t).2 hupper
    dsimp only [errorMaskIntegral]
    rw [a.cap_error_integral_high_only P (P.capFamily F t),hleft,a.alpha.property.1]
    exact HE.trans H67
  have hOrd:∀j:ConditionalHighOrdinaryDyad a,
      a.errorMaskIntegral (P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val) ≤ a.data.N^(7*delta)*a.data.E:=by
    intro j
    let v:=a.data.U*(2:ℝ)^(j.val:ℕ)
    have hv:=(comparison_mass_dyadic_scale a.data.hU j.val)
    have hstart:a.data.s < v/2:=by dsimp only [v];linarith only [j.property]
    have Hgroup:=P.ordinaryGroup_eq_retainedSupport (P.capFamily F) (Ioo (0:ℝ) 1)
      (by norm_num : (1:ℝ) ≤ 16) j.val hv.2.2 hstart
    change P.ordinaryGroup (P.capFamily F) (Ioo (0:ℝ) 1) 16 j.val=P.canonicalOrdinarySupport F (Ioo (0:ℝ) 1) v at Hgroup
    dsimp only [errorMaskIntegral]
    rw [Hgroup]
    exact hnO a hs hsxs hd1 hxs hy P hclock F (Ioo (0:ℝ) 1) v hv.1 hv.2.2 hstart hv.2.1
  have hBroad:∀p:RelevantBroadSlice (P.capFamily F) (Ioo (0:ℝ) 1),
      a.errorMaskIntegral (actualBroadSlice (P.capFamily F) p.val) ≤ a.data.N^(7*delta)*a.data.E:=by
    intro p
    have HE:=hnB a hs hsxs hd1 hxs hy P (P.capFamily F p.val.1.val)
      (actualBroadCapSampler (P.capFamily F) p.val.1) p.val.2 (P.capFamily_contacts F p.val.1.val)
    exact HE.trans H67
  exact P.conditional_finite_error_le_log_high_only F hB0 hR0 hN hlog hscalar.2.2.2.2.1
    hRaw hWall hInit hOrd hBroad

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
