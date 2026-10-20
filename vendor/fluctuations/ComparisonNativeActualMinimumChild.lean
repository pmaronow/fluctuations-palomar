module

public import ComparisonNativeActualChildConstruction
public import ComparisonNativeActualChildAgreement
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 8000000

def NativeOverlapContext.toChildBarrierParameters {n : ℕ} {delta : ℝ}
    (c : NativeOverlapContext n delta) : NativeChildBarrierParameters n delta where
  E:=c.E
  d:=c.d
  hn:=c.hn
  hE:=c.hE
  hd:=c.hd

theorem native_child_radius_eq_of_parent_fields {n : ℕ} {delta : ℝ}
    (a : NativeChildBarrierCall n delta) (c : NativeChildBarrierParameters n delta)
    (α : c.Profile) (hcontext : a.context=c) (halpha : HEq a.alpha α) : a.R=c.R α := by
  cases a
  cases hcontext
  cases halpha
  rfl

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem exists_actual_child {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x)
    (hroom : M.lam+(c0*x)^2 ≤ M.b 0) (hq : 2 ≤ (n:ℝ)^delta) :
    let c:=M.context.toChildBarrierParameters
    let child:=c.actualChild M.hlam hc0 hx
    ∃β : child.Profile,∃a : NativeChildBarrierCall n delta,
      a.context=c ∧ a.lam=M.lam ∧ HEq a.alpha M.alpha ∧ a.R=M.R ∧ a.b=M.b ∧ a.h=M.h ∧
      a.childRadius=c0*x ∧ a.childLam=(c0*x)^2 ∧ a.Z=child.R β ∧
      a.err=variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          child.d ((c0*x)^2) ∧ a.err∈Icc (0:ℝ) ((c0*x)^2) := by
  dsimp only
  let c:=M.context.toChildBarrierParameters
  let child:=c.actualChild M.hlam hc0 hx
  obtain ⟨β,a,hcontext,hlam,halpha,hb,hh,hd,hl,hZ,he,herr,_⟩:=
    native_actual_child_call_exists c child M.alpha M.b M.h M.hlam (sq_pos_of_pos (mul_pos hc0 hx))
      M.hb M.hh M.hh0 hroom M.minimum hq
  have hR : a.R=M.R := native_child_radius_eq_of_parent_fields a c M.alpha hcontext halpha
  exact ⟨β,a,hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr⟩

theorem actual_minimum_successful_child_agreement
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {c0 : ℝ} (hc0 : 0 < c0)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→NativeChildBarrierCall (N n) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧ (a n).R=(M n).R)
    (hchild : ∀ᶠ n in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (M n).context.d (M n).lam (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) :
    ∀left right eps theta : ℝ,0 < left → left < right → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop,
      volume (physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (x n*left) (x n*right) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hdata : ∀ᶠ n in atTop,
      (a n).context.d ≤ D ∧
      Real.sqrt (N n:ℝ)*(a n).context.E ≤ (a n).context.d^2 ∧
      (1/C0)*(N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E ∧
      comparisonLowerScale (N n) (a n).context.E (a n).context.d ≤ x n ∧
      (a n).lam ≤ (a n).context.d^2 ∧
      (a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (a n).context.d (a n).lam (x n) := by
    filter_upwards [hchild] with n hn
    rcases hparent n with ⟨he,hd,hl,_⟩
    rw [he,hd,hl]
    have hlo : (1/C0)*(N n:ℝ)^(-(2:ℝ)/3+m)*(M n).context.d ≤ (M n).context.E := by
      have hh:=mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
      simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using hh
    exact ⟨(M n).hdD,(M n).hupper,hlo,(M n).hscale.trans (hxs n),(M n).hld,hn⟩
  have hweak' : Tendsto (fun n=>(a n).e (x n)/(x n)^2) atTop (𝓝 0) := by
    convert hweak using 1
    ext n
    simp only [NativeChildBarrierCall.e,(hparent n).2.1,(hparent n).2.2.1]
  have hcap : ∀b : ℝ,0 < b → ∃C : ℝ,0 < C ∧ ∀ᶠ n in atTop,
      ∀u∈Icc (0:ℝ) (x n*b),(a n).R u ≤ C*x n := by
    intro b hb
    refine ⟨(Az+1/cl)*(1+b),by positivity,?_⟩
    have ht : Tendsto (fun n=>x n*b) atTop (𝓝 0) := by simpa using hxlim.mul_const b
    filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n hn
    intro u hu
    rw [(hparent n).2.2.2]
    have hR:=(M n).inverse_radius_le_source_mass hcl hAz ⟨hu.1,hu.2.trans hn.le⟩
    have hh:=mul_le_mul_of_nonneg_left (show (M n).xs+u ≤ (1+b)*x n by nlinarith [hxs n,hu.2])
      (show 0 ≤ Az+1/cl by positivity)
    exact hR.trans (by nlinarith)
  have Hagree:=native_actual_successful_child_agreement hdelta (show 0 < 1/C0 by positivity)
    hm hc0 N hN a x hx hxlim hdata hweak' hcap
  intro left right eps theta hleft hlr heps htheta
  simpa only [(hparent _).2.2.2] using Hagree left right eps theta hleft hlr heps htheta

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
