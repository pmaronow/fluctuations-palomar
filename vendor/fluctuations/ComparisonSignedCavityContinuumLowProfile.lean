module

public import ComparisonSignedCavityCanonicalLowFactor
public import ComparisonSignedCavityActualInitialPairMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_continuum_low_kernel_moment_le (n U order : ℕ) (horder : 0<order)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (law : ℕ→FullCoordinate n→ℝ)
    (b h S : ℕ→ℝ) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) (j : ℕ)
    {Ck Cb Cd natural : ℝ} (hCk : 0 ≤ Ck) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hnat : 0<natural)
    (hK : |h j+b j*S j| ≤ Ck*natural) (hb : |b j| ≤ Cb)
    (hdelta : (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^order) 0 ≤ (Cd*natural)^order) :
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^order) 0 ≤
      (2*(Ck+Cb*Cd+1)*natural)^order := by
  let R:=ClockTree.pairClock (S:=Spin n×Bool) as j
  let N:=(Ck+Cb*Cd+1)*natural
  have hN : 0<N:=by dsimp [N];positivity
  by_cases hj : j<U
  · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^order)=
        fun σ=>|rowCovarianceKernel n (fullVariance n 0 s (b j) (h j) (h j+b j*S j))
          (R.atSlot σ (ClockTree.pairLeftSlot as j)) (R.atSlot σ (ClockTree.pairRightSlot as j))|^order := by
      funext σ
      rw [coordinateProfile_eq_rowCovarianceKernel]
      simp only [cutLSlope,hj,ite_true,R,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
    rw [HE]
    simp only [R,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot]
    have HA:=actual_low_row_moment_le n order R ho 0 law 0
      (ClockTree.pairLeftSlot as j) (ClockTree.pairRightSlot as j) (b j) (h j) (S j) s
    simp only [R,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot] at HA
    have Hbeta : |s*b j| ≤ Cb := by
      rw [abs_mul,abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans hb
    have HKpow:=pow_le_pow_left₀ (abs_nonneg _) hK order
    have Hdelta0 : 0 ≤ R.disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
          (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^order) 0 := by
      unfold ClockTree.disorderExpect
      exact Finset.sum_nonneg fun σ _=>mul_nonneg
        ((R.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 law 0).1 σ)
        (pow_nonneg (abs_nonneg _) _)
    have HT:=mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) Hbeta order) hdelta Hdelta0 (pow_nonneg hCb _)
    have HKnat : Ck*natural ≤ N:=by
      dsimp [N]
      nlinarith [mul_nonneg (mul_nonneg hCb hCd) hnat.le]
    have Hdnat : Cb*Cd*natural ≤ N:=by
      dsimp [N]
      nlinarith [mul_nonneg hCk hnat.le]
    have Htot : |h j+b j*S j|^order+|s*b j|^order*
        R.disorderExpect (fullWeight n) (fullFeature n) 0 law
          (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
            (joinSpin (ClockTree.pairSpin as j σ).2)-S j|^order) 0 ≤ 2*N^order := by
      have H1:=HKpow.trans (pow_le_pow_left₀ (mul_nonneg hCk hnat.le) HKnat order)
      have H2:=pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Cb*Cd*natural) Hdnat order
      have H2':=HT.trans (by simpa only [mul_pow,mul_assoc] using H2)
      linarith
    apply HA.trans
    apply (mul_le_mul_of_nonneg_left Htot (by positivity : (0:ℝ) ≤ (2:ℝ)^(order-1))).trans_eq
    rw [←mul_assoc,←pow_succ,show order-1+1=order by omega,←mul_pow]
    congr 1
    dsimp [N]
    ring
  · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n U s b h (fun j=>h j+b j*S j)) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^order)=fun _=>0 := by
      funext σ
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hj,ite_false,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,abs_zero,zero_pow horder.ne']
    rw [HE]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    positivity

end OAI.SKFluctuations.Cavity
