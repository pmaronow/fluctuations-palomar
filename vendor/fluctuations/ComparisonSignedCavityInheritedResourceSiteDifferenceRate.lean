module

public import ComparisonSignedCavityActualFrozenResourceSiteDifference
public import ComparisonSignedCavityInheritedRawResourcePairBudget
public import ComparisonSignedCavityActualMinimumOmittedSiteProduct
public import ComparisonSignedCavityContinuumMixedClock
public import ComparisonSignedCavityOriginalPhysicalClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_minimum_inherited_resource_site_deleted_rate
    (degree : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let center:=nativePhysicalResourceCenter n M.bf M.hf as
        ∀(U₀ U i star : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          P.resources.length ≤ degree → i ≤ star → star < as.length →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        ∀s t : T.Slot,
          |nativeOriginalResourceSiteDeletedDifference P 0
            (finitePhysicalCavitySquareVariance n U₀ as b h 1 1) 0 U b h K center s t| ≤
            C*|P.coefficient| *((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*
              nativeResourceScale x W 1 P.resources := by
  obtain ⟨A,hA1,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let B:=2*(A+2)
  have hA : 0 < A:=zero_lt_one.trans_le hA1
  have hB1 : 1 ≤ B:=by dsimp only [B];linarith
  let C:=3*B^degree
  have hC : 0 < C:=by dsimp only [C];positivity
  have Hcost:=eventually_actual_omitted_product_cubic_cost_saved
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 (degree+1:ℕ) (by positivity)
  have Hsite:=NativeOverlapMinimum.eventually_omitted_site_below_saved_scale
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    (saving:=0) hC0 (by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [HA,Hcost,Hsite] with n hn hnCost hnSite
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hsource hxs1 L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  have ho:=finiteCutMasses_ordered us hus k
  intro U₀ U i star T P hd hi hs x W hxsx hxW hmi hms s t
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hMxs:=M.hxs
  have hW : 0 < W:=hx.trans_le hxW
  let q₀:=finitePhysicalCavitySquareVariance n U₀ as b h 1 1
  have HP₀:=hk U₀ i star T P (by omega) (by omega) (by omega) x W hxsx hxW hmi hms
    1 1 (by constructor <;> norm_num) (by constructor <;> norm_num)
  have HP:=hk U i star T P (by omega) (by omega) (by omega) x W hxsx hxW hmi hms
    1 1 (by constructor <;> norm_num) (by constructor <;> norm_num)
  have HQ : cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K=
      finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n
      (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  have hsite : 1/(n+1:ℕ) ≤ x:=by
    simpa only [neg_zero,Real.rpow_zero,one_mul] using hnSite M x hxsx
  have Hraw:=native_original_resource_site_deleted_difference_abs_le T ho P 0 q₀ 0 U b h K center
    s t A x W hA hx hxW hi hs hsite HP₀ (by rw [HQ];exact HP.1)
  have hlen : P.live.factors.length ≤ degree:=by
    have H : P.live.factors.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map]
      omega
    omega
  let e:=((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)
  have he : 0 ≤ e:=by dsimp only [e];positivity
  have Hden : (P.live.factors.length:ℝ)/((n+1:ℕ)*x) ≤ e:=by
    apply le_trans _ (hnCost M W (hxsx.trans hxW))
    apply (div_le_div_of_nonneg_right (show (P.live.factors.length:ℝ) ≤ (degree+1:ℕ) by exact_mod_cast (show P.live.factors.length≤degree+1 by omega)) (by positivity)).trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hxsx (by positivity))
  have Hinv : (1:ℝ)/(n+1:ℕ) ≤ e:=by
    apply le_trans _ (hnCost M W (hxsx.trans hxW))
    calc
      _=1/(((n+1:ℕ):ℝ)*1):=by rw [mul_one]
      _≤1/(((n+1:ℕ):ℝ)*M.xs):=div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hxs1 (by positivity))
      _≤_:=div_le_div_of_nonneg_right
        (show (1:ℝ) ≤ (degree+1:ℕ) by exact_mod_cast (show 1≤degree+1 by omega))
        (by positivity)
  have HPB : B^P.resources.length ≤ B^degree:=pow_le_pow_right₀ hB1 hd
  have HPAB : A^P.resources.length ≤ B^degree:=
    (pow_le_pow_left₀ hA.le (by dsimp only [B];linarith) _).trans HPB
  have Hbracket : 2*((P.live.factors.length:ℝ)/((n+1:ℕ)*x))*(2*(A+2))^P.resources.length+
      A^P.resources.length/(n+1:ℕ) ≤ C*e:=by
    have Hfirst:=mul_le_mul (mul_le_mul_of_nonneg_left Hden (by norm_num : (0:ℝ)≤2))
      HPB (by positivity) (by positivity)
    have Hsecond:=mul_le_mul HPAB Hinv (by positivity) (by positivity)
    calc
      _≤2*e*B^degree+B^degree*e:=add_le_add Hfirst
        (by simpa only [one_mul,div_eq_mul_inv] using Hsecond)
      _=C*e:=by dsimp only [C];ring
  have Hfinal:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hbracket (abs_nonneg P.coefficient))
    (native_resource_raw_scale_pos P.resources hx hW).le
  exact Hraw.trans (Hfinal.trans_eq (by dsimp only [e];ring))

end OAI.SKFluctuations.Cavity
