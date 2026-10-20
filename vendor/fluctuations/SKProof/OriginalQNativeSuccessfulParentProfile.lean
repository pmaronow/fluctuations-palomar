module

public import SKProof.OriginalQNativeSuccessfulChildProfile
public import ComparisonNativeActualSuccessfulChildMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem exists_successful_child_strict_parent_profile_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroomdelta : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQNativeRootHistory M T c0)
    (a : (n : ℕ) → NativeChildBarrierCall (dim n+1) delta)
    (x : ℕ → ℝ) (hxs : ∀n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n, (a n).context.E = (M n).context.E ∧
      (a n).context.d = (M n).context.d ∧
      (a n).lam = (M n).lam ∧ (a n).R = (M n).R)
    (hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (x n))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta
        (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hroom : ∀n, (M n).lam+(c0*x n)^2 ≤ (M n).b 0)
    (beta : (n : ℕ) →
      ((M n).context.toChildBarrierParameters.actualChild (M n).hlam
        hc0 ((M n).hxs.trans_le (hxs n))).Profile)
    (hZ : ∀n, (a n).Z =
      ((M n).context.toChildBarrierParameters.actualChild (M n).hlam
        hc0 ((M n).hxs.trans_le (hxs n))).R (beta n))
    (hattained : ∀n,
      let child := (M n).context.toChildBarrierParameters.actualChild
        (M n).hlam hc0 ((M n).hxs.trans_le (hxs n))
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc
        child.hm child.hM (dim n+1)
        (fun u => (M n).b u-
          laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
        (fun u => (M n).h u+
          laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
            (M n).R u)
        (c0*x n) ((c0*x n)^2) (beta n) =
      variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc
        child.hm child.hM (dim n+1)
        (fun u => (M n).b u-
          laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
        (fun u => (M n).h u+
          laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
            (M n).R u)
        (c0*x n) ((c0*x n)^2)) :
    ∃sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ᶠn in atTop,
      cl*x (sigma n) < (M (sigma n)).alpha.val.val (x (sigma n)) ∧
      (M (sigma n)).alpha.val.val (x (sigma n)) < cu*x (sigma n) := by
  classical
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨C0band,hC0band,Hband⟩ :=
    actual_minimum_successful_child_outer_radius_bounds
      hm hdelta hcl hcu hAz hC0 hc0
      (fun n => dim n+1) ((tendsto_add_atTop_nat 1).comp hdim)
      M a x hxs hxlim hparent hchild hweak
  let C := max C0band (cl*Az/4)
  have hC : 1 ≤ C := hC0band.trans (le_max_left _ _)
  have hAzC : Az ≤ 4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    nlinarith [le_max_right C0band (cl*Az/4)]
  have hband : ∀ᶠn in atTop, ∀u∈Icc (C*x n) 1,
      u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
    filter_upwards [Hband] with n hn u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _)
      (hx n).le).trans hu.1,hu.2⟩
  have hparam := eventually_actual_successful_child_minimum_parameters
    hm hdelta hC0 hc0 hc01 hmargin dim hdim M x hx htarget hweak
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp
    (hparam.and (hband.and
      (G.total_root_original_q.and (hxlim.eventually
        (eventually_le_nhds zero_lt_one)))))
  let phi := fun n : ℕ => n+n0
  have hphi : StrictMono phi :=
    fun i j hij => Nat.add_lt_add_right hij n0
  have HP n := Hn0 (phi n) (Nat.le_add_left n0 n)
  have hdunit n : c0*x (phi n) ≤ 1 := by
    calc
      c0*x (phi n) ≤ 1*x (phi n) :=
        mul_le_mul_of_nonneg_right hc01 (hx (phi n)).le
      _ ≤ 1 := by simpa only [one_mul] using (HP n).2.2.2
  let Q : (n : ℕ) → NativeOverlapMinimum (dim (phi n)+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0
        (max Ct 1) (max D 1) (max Bclock T) := fun n =>
    ((M (phi n)).actualSuccessfulChildMinimum (Dchild := max D 1) hc0 hc01
      (hx (phi n)) hcl hcu (zero_lt_one.trans_le hC).le
      (beta (phi n)) (hroom (phi n)) (hattained (phi n))
      ((hdunit n).trans (le_max_right D 1))
      (HP n).1.2.1 (HP n).2.2.1.1 (by
        intro u hu
        rw [←hZ (phi n)]
        exact (HP n).2.1 u hu)).weakenConstants
          le_rfl le_rfl le_rfl (le_max_right Ct 1)
          le_rfl (le_max_right Bclock T)
  have hQxs n : (Q n).xs = x (phi n) := rfl
  have hQR n : (Q n).R = (a (phi n)).Z := (hZ (phi n)).symm
  have hQd n : (Q n).context.d = c0*x (phi n) := rfl
  have hQlam n : (Q n).lam = (c0*x (phi n))^2 := rfl
  obtain ⟨GQ⟩ := (G.comp_original_q phi hphi).successful_child_comparable_context_original_q
    hm hdelta hcl hcu hAz hC0 hc0 hc01 (zero_lt_one.trans_le hC).le hAzC
    hmargin hcapmargin hgapmargin (hdim.comp hphi.tendsto_atTop)
    Q (fun n => x (phi n)) (fun n => hxs (phi n))
    (hxlim.comp hphi.tendsto_atTop)
    (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop)
    (Eventually.of_forall hQd) (Eventually.of_forall (fun _ => rfl))
    (Eventually.of_forall (fun _ _ => rfl))
    (Eventually.of_forall (fun _ _ => rfl)) hQxs
  obtain ⟨psi,hpsi,Hstrict⟩ :=
    successful_native_child_comparable_profile_transfers_to_parent_original_q
      hm hdelta hroomdelta hcl hcu hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin hclmargin hcumargin
      (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) (fun n => a (phi n))
      (fun n => x (phi n)) (fun n => hxs (phi n))
      (hxlim.comp hphi.tendsto_atTop)
      (fun n => hparent (phi n))
      (hphi.tendsto_atTop.eventually hchild)
      (hweak.comp hphi.tendsto_atTop)
      Q GQ hQxs hQR hQd hQlam
  let sigma := phi ∘ psi
  exact ⟨sigma,hphi.comp hpsi,Hstrict⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
