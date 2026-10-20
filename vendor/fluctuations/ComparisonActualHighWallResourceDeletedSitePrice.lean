module

public import ComparisonActualHighWallOmittedSiteCubic
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonSignedCavityActualFrozenResourceSiteDifference

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_resource_deleted_site_cubic_price
    (degree : ℕ) (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let center:=nativePhysicalResourceCenter n M.bf M.hf as
        ∀(U₀ U i star : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          P.resources.length≤degree → i ≤ star → star<as.length →
          partitionPoint 0 as i≤Cmass*M.data.d → partitionPoint 0 as star≤Cmass*M.data.d →
        ∀s t : T.Slot,
          |nativeOriginalResourceSiteDeletedDifference P 0
            (finitePhysicalCavitySquareVariance n U₀ as b h 1 1) 0 U b h K center s t|≤
            C*|P.coefficient| *M.data.d^3*nativeResourceScale M.data.d M.data.d 1 P.resources := by
  obtain ⟨A,hA1,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA : 0<A:=zero_lt_one.trans_le hA1
  let B:=2*(A+2)
  have hB1 : 1≤B:=by dsimp only [B];linarith
  let C:=(2*(degree:ℝ)+1)*B^degree+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HA,eventually_actual_high_wall_omitted_product_cubic_cost (D:=D) (Bclock:=Bclock) hm hC0]
    with n hn hnCost
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let center:=nativePhysicalResourceCenter n M.bf M.hf as
  have ho:=finiteCutMasses_ordered us hus jGrid
  intro U₀ U i star T P hdegree hi hs hmi hms s t
  have hd:=M.data.hd
  have HC:=hnCost M hwork
  have hN : 0<((n+1:ℕ):ℝ):=by positivity
  have Hinv : (1:ℝ)/(n+1:ℕ)≤M.data.d^3:=by
    exact (div_le_div_of_nonneg_left zero_le_one (mul_pos hN M.data.hd)
      (by nlinarith only [M.data.hd1])).trans HC
  have hsite : (1:ℝ)/(n+1:ℕ)≤M.data.d:=Hinv.trans
    (by nlinarith only [M.data.hd.le,M.data.hd1,mul_nonneg M.data.hd.le (sub_nonneg.mpr M.data.hd1)])
  let q₀:=finitePhysicalCavitySquareVariance n U₀ as b h 1 1
  have HP₀:=hj U₀ i star T P (by omega) (hi.trans hs.le) hs.le hmi hms 1 1 (by norm_num) (by norm_num)
  have HP:=hj U i star T P (by omega) (hi.trans hs.le) hs.le hmi hms 1 1 (by norm_num) (by norm_num)
  have HQ : cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K=
      finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
      U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hraw:=native_original_resource_site_deleted_difference_abs_le T ho P 0 q₀ 0 U b h K center
    s t A M.data.d M.data.d hA M.data.hd le_rfl hi hs hsite HP₀ (by rw [HQ];exact HP.1)
  have hlen : P.live.factors.length≤degree:=by
    have H : P.live.factors.length≤P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map]
      omega
    omega
  have Hden : (P.live.factors.length:ℝ)/((n+1:ℕ)*M.data.d)≤(degree:ℝ)*M.data.d^3:=by
    have H:=mul_le_mul (show (P.live.factors.length:ℝ)≤degree by exact_mod_cast hlen) HC
      (by positivity) (Nat.cast_nonneg degree)
    simpa only [div_eq_mul_inv,one_mul] using H
  have HPB : B^P.resources.length≤B^degree:=pow_le_pow_right₀ hB1 hdegree
  have HPAB : A^P.resources.length≤B^degree:=
    (pow_le_pow_left₀ hA.le (by dsimp only [B];linarith) _).trans HPB
  have Hbracket : 2*((P.live.factors.length:ℝ)/((n+1:ℕ)*M.data.d))*(2*(A+2))^P.resources.length+
      A^P.resources.length/(n+1:ℕ)≤C*M.data.d^3:=by
    have Hfirst:=mul_le_mul (mul_le_mul_of_nonneg_left Hden (by norm_num : (0:ℝ)≤2))
      HPB (by positivity) (by positivity)
    have Hsecond:=mul_le_mul HPAB Hinv (by positivity) (by positivity)
    have Hbase:=add_le_add Hfirst (by simpa only [one_mul,div_eq_mul_inv] using Hsecond)
    have Hconst:=mul_le_mul_of_nonneg_right
      (show (2*(degree:ℝ)+1)*B^degree≤C by dsimp only [C];linarith) (pow_nonneg M.data.hd.le 3)
    apply Hbase.trans
    convert Hconst using 1; ring
  have Hfinal:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hbracket (abs_nonneg P.coefficient))
    (native_resource_raw_scale_pos P.resources M.data.hd M.data.hd).le
  exact Hraw.trans (Hfinal.trans_eq (by ring))

end OAI.SKFluctuations.Cavity
