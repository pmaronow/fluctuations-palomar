module

public import ComparisonActualHighWallStarPolynomialProducer
public import ComparisonActualHighWallRegularSlabAlong
public import ComparisonActualHighWallPolynomialStarCore
public import ComparisonSignedCavityActualStarPolynomialCompleteProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_polynomial_calibrated_star_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hT0 : 0< T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤ (M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0)) (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (hT : ∀n,T0≤ (M n).data.T) :
    ∀ᶠn in atTop,∃P : (M n).Potential,
      ∃u∈Ioo (starMassBandConstant cu Az*W n) (2*starMassBandConstant cu Az*W n),
        P.H ((M n).data.wallRadius (M n).alpha u)≤0 ∧
        orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2≤
          (M n).data.N^(-(actualMassSavingExponent m delta/4))*(W n)^2 ∧
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).data.wallRadius (M n).alpha u|≤
          (starMassBandConstant cu Az/cu)*W n/4 ∧
        (3*(starMassBandConstant cu Az/cu)/4)*W n≤ orderedPathS (dim n+1) (M n).bf (M n).hf u ∧
        orderedPathS (dim n+1) (M n).bf (M n).hf u≤
          (2*starMassBandConstant cu Az/cl+(starMassBandConstant cu Az/cu)/4)*W n ∧
        (3*(M n).data.T*(starMassBandConstant cu Az/cu)/8)*W n≤ actualMixedClock (dim n+1) (M n).bf (M n).hf u ∧
        |actualMixedClock (dim n+1) (M n).bf (M n).hf u-(M n).data.T*orderedPathS (dim n+1) (M n).bf (M n).hf u|≤
          ((starMassBandConstant cu Az/cu)/4)*(W n)^3 := by
  let A:=starMassBandConstant cu Az
  let c:=A/cu
  let eta:=actualMassSavingExponent m delta
  have hA : 0< A:=star_mass_band_constant_pos hcu hAz
  have hc : 0< c:=div_pos hA hcu
  have hgap : cu*Az< A:=by dsimp only [A,starMassBandConstant];linarith
  have hxs n : (M n).xs≤ W n:=(hxsd n).trans (hdW n)
  have HS:=eventually_actual_high_wall_regular_mass_slab_polynomial_along hm hdelta hroom
    hcl hcu hAz hC0 hCt hgap (show A<2*A by linarith) dim hdim M W hxsd hdW hWlim hsRatio
  have HP:=eventually_actual_high_wall_star_band_parameters_along hm hdelta hcl hcu hAz hC0 hgap
    dim hdim M W hxs hsRatio
  have HT:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_actual_high_wall_cap_travel_small (m:=m) (delta:=delta) (cl:=cl) (cu:=cu)
      (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=c/32) hC0
      (by linarith) (by positivity))
  have HF:=eventually_actual_high_wall_floor_mass_small (m:=m) (delta:=delta) (cl:=cl)
    (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=A/2)
    hC0 (by linarith) (by positivity)
  have HC:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=A/4) (q:=-(eta/4)) (r:=0)
      (by positivity) (by linarith [actualMassSavingExponent_pos hm hdelta]))
  have HZ:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=c^2/64) (q:=-(eta/4)) (r:=0)
      (by positivity) (by linarith [actualMassSavingExponent_pos hm hdelta]))
  have HB:=(hWlim.const_mul (2*A)).eventually (eventually_le_nhds (show (2*A)*(0:ℝ)<1 by simp))
  have HK:=(hWlim.pow 2).eventually (eventually_le_nhds (show (0:ℝ)^2<T0/2 by simpa using half_pos hT0))
  filter_upwards [HS,HP,HT,(hdim.eventually HF),HC,HZ,HB,HK] with n hs hp ht hf hcN hzN hb hk
  obtain ⟨P⟩:=(M n).exists_potential
  have hW : 0< W n:=(M n).data.hd.trans_le (hdW n)
  have htravel : (M n).cavityCapTravel≤ c*W n/32:=by
    exact (ht (M n)).1.trans (by
      simpa only [div_mul_eq_mul_div] using
        (mul_le_mul_of_nonneg_left (hxs n) (show 0≤ c/32 by positivity)))
  have hfloor : (M n).data.N^(-delta)*comparisonSmallMass (M n).data.N (M n).data.E≤ (A/2)*W n:=
    hf (M n) (W n) (hxs n)
  have hcoef : (M n).data.N^(-(eta/4))≤ A/4:=by
    simpa only [Function.comp_apply,ActualHighWallData.N,Real.rpow_zero,mul_one,one_mul] using hcN
  have hsize : (M n).data.N^(-(eta/4))≤ c^2/64:=by
    simpa only [Function.comp_apply,ActualHighWallData.N,Real.rpow_zero,mul_one,one_mul] using hzN
  have hband : ∀u∈Ioo (A*W n) (2*A*W n),c*W n≤ (M n).data.wallRadius (M n).alpha u ∧
      (M n).data.wallRadius (M n).alpha u≤ (2*A/cl)*W n:=by
    intro u hu
    exact (M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW (hxs n) le_rfl hb
      hp.1.le ⟨hu.1.le,hu.2.le⟩
  have haway : ∀u∈Ioo (A*W n) (2*A*W n),
      (M n).data.rmin+(M n).cavityCapTravel< (M n).data.wallRadius (M n).alpha u:=by
    intro u hu
    have HH:=hp.2.2.2.2.2.2
    have HE : (A/(2*cu))*W n=c*W n/2:=by dsimp only [c];ring
    rw [HE] at HH
    linarith only [HH,(hband u hu).1,mul_pos hc hW]
  let t:=(M n).data.N^(-(eta/4))*(W n)^2
  have htpos : 0< t:=by dsimp only [t];positivity
  have hpow : (M n).data.N^(-(eta/2))=((M n).data.N^(-(eta/4)))^2:=by
    rw [pow_two,←Real.rpow_add (M n).data.hN];congr 1;ring
  have hthermal : (∫u in Ioo (A*W n) (2*A*W n),orderedPathB (dim n+1) (M n).bf (M n).hf u-
      (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)<
      t*((2*A*W n-A*W n)-(M n).data.N^(-delta)*comparisonSmallMass (M n).data.N (M n).data.E):=by
    calc
      _≤ (M n).data.N^(-(eta/2))*(W n)^3:=hs
      _=t*((M n).data.N^(-(eta/4))*W n):=by rw [hpow];dsimp only [t];ring
      _≤ t*((A/4)*W n):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hW.le) htpos.le
      _< t*((A/2)*W n):=mul_lt_mul_of_pos_left (by nlinarith only [mul_pos hA hW]) htpos
      _≤_:=mul_le_mul_of_nonneg_left (by linarith only [hfloor]) htpos.le
  have HKclock : (W n)^2≤ (M n).data.T/2:=hk.trans (div_le_div_of_nonneg_right (hT n) (by norm_num))
  obtain ⟨u,hu,hrest⟩:=P.exists_polynomial_calibrated_star hp.1.le
    (show A*W n<2*A*W n by nlinarith only [mul_pos hA hW]) hb hc hW
    (hdW n) HKclock htravel hsize haway hband hthermal
  exact ⟨P,u,hu,hrest⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
