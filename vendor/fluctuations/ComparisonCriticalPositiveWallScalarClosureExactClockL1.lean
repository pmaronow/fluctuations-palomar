module

public import ComparisonScalarClosureCombinedBare

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 12000000

theorem comparison_scalar_closure_of_exact_clock_radius_L1
    (Gamma : ℕ→ℝ→ℝ) (e s : ℕ→ℝ→ℝ) (x : ℕ→ℝ)
    (g shape sl : ℝ→ℝ) {T a b : ℝ} {A : Set ℝ}
    (hT : 0 < T) (hx0 : ∀n,0 < x n) (hx : Tendsto x atTop (𝓝 0))
    (he : ∀t∈Icc a b,Tendsto (fun n=>e n t/(x n)^2) atTop (𝓝 (shape t)))
    (hs : ∀t∈Icc a b,Tendsto (fun n=>s n t/x n) atTop (𝓝 (sl t)))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n))
      g atTop A)
    (hgc : ∀t∈Icc a b,ContinuousWithinAt g A (sl t))
    (hK : ∀ᶠn in atTop,∀t∈Icc a b,
      comparisonNativeScalarClock 0 T (e n t) (x n*t) (s n t)/(T*x n)∈A)
    (hi : ∀ᶠn in atTop,Integrable (fun t=>(s n t-
      Gamma n (comparisonNativeScalarClock 0 T (e n t) (x n*t) (s n t)))/(x n)^3)
      (volume.restrict (Icc a b)))
    (hL1 : Tendsto (fun n=>∫t in Icc a b,
      |(s n t-Gamma n (comparisonNativeScalarClock 0 T (e n t) (x n*t)
        (s n t)))/(x n)^3|) atTop (𝓝 0)) :
    ∀ᵐt∂volume.restrict (Icc a b),
      g (sl t)=shape t/T*(sl t-t) := by
  let rho := fun n t=>(s n t-Gamma n
    (comparisonNativeScalarClock 0 T (e n t) (x n*t) (s n t)))/(x n)^3
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hi
  let rho' := fun n t=>rho (n+N) t
  obtain ⟨phi,hphi,Hrho⟩ := comparison_L1_zero_exists_ae_subsequence
    (volume.restrict (Icc a b)) rho'
      (fun n=>hN (n+N) (by omega))
      (by simpa only [rho',rho,Function.comp_def] using
        hL1.comp (tendsto_add_atTop_nat N))
  let psi := fun n=>phi n+N
  have hpsi : StrictMono psi := by
    intro i j hij
    exact Nat.add_lt_add_right (hphi hij) N
  filter_upwards [Hrho,ae_restrict_mem measurableSet_Icc] with t hrhot ht
  apply comparison_scalar_closure_identification_combined_bare
    (fun n=>Gamma (psi n)) (fun _=>(0:ℝ)) (fun _=>T)
    (fun n=>e (psi n) t) (fun n=>s (psi n) t)
    (fun n=>x (psi n)) g hT.ne'
    (fun n=>(hx0 (psi n)).ne') (hx.comp hpsi.tendsto_atTop)
    ((he t ht).comp hpsi.tendsto_atTop)
    ((hs t ht).comp hpsi.tendsto_atTop)
    (by simpa only [sub_self,zero_mul,zero_add,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))
    (hG.seq_tendstoUniformlyOn psi hpsi.tendsto_atTop) (hgc t ht)
  · filter_upwards [hpsi.tendsto_atTop.eventually hK] with n hn
    exact hn t ht
  · simpa only [rho',rho,psi] using hrhot

end OAI.SKFluctuations.LaplaceWindowFormalization
