module

public import ComparisonNativeAbsoluteDisagreementMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 9000000

theorem native_actual_successful_child_agreement
    {delta gamma Dbound m c0 : ℝ}
    (hdelta : 0 < delta) (hgamma : 0 < gamma) (hm : 0 < m) (hc0 : 0 < c0)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (a : (n : ℕ)→NativeChildBarrierCall (N n) delta)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hdata : ∀ᶠ n in atTop,
      (a n).context.d ≤ Dbound ∧
      Real.sqrt (N n:ℝ)*(a n).context.E ≤ (a n).context.d^2 ∧
      gamma*(N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E ∧
      comparisonLowerScale (N n) (a n).context.E (a n).context.d ≤ x n ∧
      (a n).lam ≤ (a n).context.d^2 ∧
      (a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (a n).context.d (a n).lam (x n))
    (hweak : Tendsto (fun n=>(a n).e (x n)/(x n)^2) atTop (𝓝 0))
    (hcap : ∀b : ℝ,0 < b → ∃C : ℝ,0 < C ∧ ∀ᶠ n in atTop,
      ∀u∈Icc (0:ℝ) (x n*b),(a n).R u ≤ C*x n) :
    ∀left right eps theta : ℝ,0 < left → left < right → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop,
      volume (physicalPropagationDisagreementMassSet (a n).R (a n).Z
        (x n*left) (x n*right) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
  intro left right eps theta hleft hlr heps htheta
  obtain ⟨C,hC,Hcap⟩:=hcap right (hleft.trans hlr)
  have hstep : 0 < eps/3 := by positivity
  obtain ⟨J,hJ⟩:=exists_nat_gt (C/(eps/3))
  have hCJ : C ≤ (J:ℝ)*(eps/3) := ((div_lt_iff₀ hstep).mp hJ).le
  let ell:=theta/(4*((J:ℝ)+1))
  have hell : 0 < ell := by dsimp [ell];positivity
  obtain ⟨eta,heta,_heta1,Hmass⟩:=eventually_native_absolute_disagreement_mass_le
    (Dbound:=Dbound) J hdelta hgamma hm hc0 hstep hell
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  have Hunit:=hxlim.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have Hright : ∀ᶠ n in atTop,x n*right < 1 := by
    have ht : Tendsto (fun n=>x n*right) atTop (𝓝 0) := by simpa using hxlim.mul_const right
    exact ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hN.eventually Hmass,Hweak,Hunit,Hright,Hcap,hdata] with n hn hwe hxu hru hcu hd
  have hweakn : (a n).e (x n) ≤ eta^3*(x n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hwe.le
  have hRupper : ∀u∈Icc (x n*left) (x n*right),(a n).R u ≤ (J:ℝ)*((eps/3)*x n) := by
    intro u hu
    have h := hcu u ⟨(mul_nonneg (hx n).le hleft.le).trans hu.1,hu.2⟩
    have hh:=mul_le_mul_of_nonneg_right hCJ (hx n).le
    exact h.trans (by nlinarith)
  have hmassn:=hn (a n) (x n) (x n*left) (x n*right)
    hd.1 hd.2.1 hd.2.2.1 ⟨hx n,hxu.le⟩ hd.2.2.2.1 hd.2.2.2.2.1 hweakn
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
    (mul_nonneg (hx n).le hleft.le) hru.le hRupper
  have hset : physicalPropagationDisagreementMassSet (a n).R (a n).Z
      (x n*left) (x n*right) (eps*x n) ⊆
      {u | u∈Icc (x n*left) (x n*right) ∧ 3*((eps/3)*x n) ≤ |(a n).Z u-(a n).R u|} := by
    intro u hu
    refine ⟨hu.1,?_⟩
    have he : 3*((eps/3)*x n)=eps*x n := by ring
    rw [he]
    exact hu.2.le
  have hrhs : 2*(J+1:ℝ≥0∞)*ENNReal.ofReal (ell*x n)=ENNReal.ofReal (theta*x n/2) := by
    calc
      _ = ENNReal.ofReal (2*((J:ℝ)+1))*ENNReal.ofReal (ell*x n) := by
        norm_num [ENNReal.ofReal_mul,ENNReal.ofReal_add]
      _ = ENNReal.ofReal (2*((J:ℝ)+1)*(ell*x n)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := by congr 1;dsimp [ell];field_simp;ring
  have hfinal : ENNReal.ofReal (theta*x n/2) < ENNReal.ofReal (theta*x n) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos htheta (hx n))).mpr (by nlinarith [mul_pos htheta (hx n)])
  exact ((measure_mono hset).trans (hmassn.trans_eq hrhs)).trans_lt hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization
