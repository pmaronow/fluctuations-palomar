module

public import ComparisonSignedCavityLowAllocation
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRootMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeScalarTest {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (es : List T.Slot)
    (τ : T.cavityRight.Assignment) : ℝ :=
  T.cavityRight.slotProduct spinValue τ (es.map T.cavityRightSlot)

theorem nativeScalarTest_full {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (es : List T.Slot) (σ : T.Assignment) :
    nativeScalarTest T es (T.cavityAssignment σ).2=siteMonomial T σ es :=
  (siteMonomial_eq_scalar T σ es).symm

theorem nativeScalarTest_pair {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (a z : T.Slot) :
    nativeScalarTest T [a,z]=sitePair T a z := by
  funext τ
  simp only [nativeScalarTest,List.map_cons,List.map_nil,ClockTree.slotProduct,sitePair,mul_one]

theorem siteRestKernel_eq_scalar_low (n U : ℕ) (b h K : ℕ→ℝ) :
    siteRestKernel n (restLowKernel n U 0 K)=
      ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) := by
  funext j σ τ
  rw [coordinateProfile_eq_rowCovarianceKernel]
  by_cases hj : j<U
  · have he : fullVariance n 0 0 (b j) (h j) (K j)=rowInterpolationSlope n 0 0 (-K j) := by
      funext i
      rcases i with (i|i)|(i|i) <;> simp [fullVariance,rowInterpolationSlope]
    simp only [cutLSlope,hj,ite_true,he]
    rw [rowInterpolationSlope_covariance]
    simp only [siteRestKernel,restLowKernel,hj,ite_true,Pi.zero_apply,
      zero_mul,add_zero,zero_sub,neg_neg]
  · simp only [cutLSlope,hj,ite_false,siteRestKernel,restLowKernel,
      mul_zero,rowCovarianceKernel,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem actual_scalar_low_coefficient_eq_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (es : List T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (k : ℕ) :
    cutLowJet n q U b h K T (fun σ=>nativeScalarTest T es (T.cavityAssignment σ).2)
      0 k 0 0=
      retainedSignedJets n q U b h K (List.replicate k (restLowKernel n U 0 K))
        T (fun _=>1) es := by
  simp_rw [nativeScalarTest_full]
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0 hq0 hq hb hh hK hbm hhm hKm k
    (by norm_num) (by norm_num),←siteRestKernel_eq_scalar_low]
  have H:=actual_site_rest_jets_eq_retained n q U b h K
    (List.replicate k (restLowKernel n U 0 K)) T ho (fun _=>1) es
  simpa only [List.map_replicate,one_mul] using H

def nativeRetainedCenteredCoefficient (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) (k : Fin 4) (r : ℕ) : ℝ :=
  retainedSignedJets n q U b h K
    (List.replicate k.val (restLowKernel n U b h)++
      List.replicate r (restHighKernel n U b h K)) T P es-
  productJet3
    (fun i=>retainedSignedJets n q U b h K
      (List.replicate i.val (restLowKernel n U 0 K)) T (fun _=>1) es)
    (fun i=>retainedSignedJets n q U b h K
      (List.replicate i.val (restLowKernel n U b h)++
        List.replicate r (restHighKernel n U b h K)) T P []) k

theorem actual_frozen_centered_coefficient_eq_native_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (k : Fin 4) (r : ℕ) :
    cutFrozenCenteredJet n q U b h K T P (nativeScalarTest T es) 0 k r 0=
      nativeRetainedCenteredCoefficient n q U b h K T P es k r := by
  unfold cutFrozenCenteredJet nativeRetainedCenteredCoefficient
  simp only [map_zero]
  simp_rw [nativeScalarTest_full]
  rw [actual_frozen_coefficient_eq_retained n q U b h K T ho P es
    hq0 hq hb hh hK hbm hhm hKm]
  have hg (i : Fin 4) := actual_scalar_low_coefficient_eq_retained n q U b h K T ho es
    hq0 hq hb hh hK hbm hhm hKm i.val
  simp_rw [nativeScalarTest_full] at hg
  simp_rw [hg]
  have hf (i : Fin 4) : cutFrozenLowHighJet n q U b h K T
      (fun σ=>P (T.cavityAssignment σ).1) 0 i.val r 0=
      retainedSignedJets n q U b h K
        (List.replicate i.val (restLowKernel n U b h)++
          List.replicate r (restHighKernel n U b h K)) T P [] := by
    simpa only [siteMonomial,mul_one] using
      actual_frozen_coefficient_eq_retained n q U b h K T ho P []
        hq0 hq hb hh hK hbm hhm hKm i.val r
  simp_rw [hf]

def nativeActualTaylorRemainder (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  (∫ t in (0:ℝ)..1,(1-t)*cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 2 t)+
  (1/2:ℝ)*(∫ t in (0:ℝ)..1,cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 1 t)+
  (1/2:ℝ)*∫ l in (0:ℝ)..1,(1-l)^2*∫ t in (0:ℝ)..1,
    cutCenteredMixedJet n q U b h K T P (sitePair T a z) 0 3 l t

theorem actual_centered_pair_eq_full_retained_ledger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutCenteredJet n q U b h K T P (sitePair T a z) 0 0 1 1=
      nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 1 0+
      nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 1 1+
      (1/2:ℝ)*nativeRetainedCenteredCoefficient n q U b h K T P [a,z] 2 0+
      nativeActualTaylorRemainder n q U b h K T P a z := by
  rw [cutSitePair_frozen_decomposition n q U b h K T P 0 hq0 hq hb hh hK
    hbm hhm hKm ho a z hU haz (by intro i;rfl)]
  have H (k : Fin 4) (r : ℕ) :
      cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 k r 0=
      nativeRetainedCenteredCoefficient n q U b h K T P [a,z] k r := by
    rw [←nativeScalarTest_pair]
    exact actual_frozen_centered_coefficient_eq_native_retained n q U b h K T ho
      P [a,z] hq0 hq hb hh hK hbm hhm hKm k r
  rw [H 1 0,H 1 1,H 2 0]
  unfold nativeActualTaylorRemainder
  ring

theorem actual_first_low_centered_eq_defect_insertion (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 0 0=
      retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z] := by
  rw [←nativeScalarTest_pair,
    actual_frozen_centered_coefficient_eq_native_retained n q U b h K T ho P [a,z]
      hq0 hq hb hh hK hbm hhm hKm]
  simp only [nativeRetainedCenteredCoefficient,productJet3,List.replicate_one,
    List.replicate_zero,List.append_nil,Fin.val_one,Fin.val_zero,retainedSignedJets]
  have HZ : fullScalarCutMoment T U K [a,z]=0 :=
    fullScalarCutGamma_cross_zero T ho U K a z hU haz
  rw [HZ]
  simp only [mul_zero,zero_mul,zero_add,fullScalarCutMoment_nil T ho,mul_one]
  have H:=native_retained_one_low_centering n q U b h K S hKS T ho P [a,z]
  simp only [retainedSignedJets] at H
  convert H using 1 <;> ring

end OAI.SKFluctuations.Cavity
