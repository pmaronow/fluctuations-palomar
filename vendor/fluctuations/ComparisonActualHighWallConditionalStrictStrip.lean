module

public import ComparisonActualHighWallConditionalDirectProfile
public import ComparisonNativeInverseProfileLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option maxHeartbeats 12000000

namespace ActualHighWallLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0<T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T}

theorem original_inverse_cdf_locally_uniform_of_linear_profile
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hkappa : 0<kappa)
    (hlinear : ∀t>0,d.V.mass t=kappa*t) :
    TendstoLocallyUniformlyOn
      (fun n t=>(M n).alpha.val.val ((M n).xs*t)/(M n).xs)
      (fun t=>kappa*t) atTop (Ioi (0:ℝ)) := by
  have H := comparison_monotone_linear_limit_locally_uniform
    (fun n t=>(M n).alpha.val.val ((M n).xs*t)/(M n).xs)
    (show 0<1/kappa by positivity)
    (fun n u hu v hv huv=>
      div_le_div_of_nonneg_right
        ((M n).alpha.val.property.2 (mul_le_mul_of_nonneg_left huv (M n).hxs.le))
        (M n).hxs.le)
    (fun t ht=>by
      convert d.radius_inverse_cdf_limit t using 1
      rw [hlinear t ht]
      field_simp [hkappa.ne'])
  convert H using 1
  funext t
  field_simp [hkappa.ne']

theorem eventually_original_inverse_strict_on_fixed_strip
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hcl0 : 0<cl) (hcl : cl<kappa) (hcu : kappa<cu)
    (hlinear : ∀t>0,d.V.mass t=kappa*t)
    {K : ℝ} (_hK : 1≤K) :
    ∀ᶠn in atTop,∀r∈Icc (M n).xs (K*(M n).xs),
      cl*r<(M n).alpha.val.val r ∧ (M n).alpha.val.val r<cu*r := by
  let eps:=min ((kappa-cl)/2) ((cu-kappa)/2)
  have heps : 0<eps:=lt_min (by linarith) (by linarith)
  have Hlocal:=d.original_inverse_cdf_locally_uniform_of_linear_profile
    (hcl0.trans hcl) hlinear
  have Hcompact : TendstoUniformlyOn
      (fun n t=>(M n).alpha.val.val ((M n).xs*t)/(M n).xs)
      (fun t=>kappa*t) atTop (Icc (1:ℝ) K) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      (Hlocal.mono (fun _ ht=>zero_lt_one.trans_le ht.1))
  have H := Metric.tendstoUniformlyOn_iff.mp Hcompact eps heps
  filter_upwards [H] with n hn r hr
  let t:=r/(M n).xs
  have ht : t∈Icc (1:ℝ) K := by
    constructor
    · exact (le_div_iff₀ (M n).hxs).mpr (by simpa only [one_mul,t] using hr.1)
    · exact (div_le_iff₀ (M n).hxs).mpr (by simpa only [mul_comm,t] using hr.2)
  have hrt : (M n).xs*t=r := by dsimp [t];field_simp [(M n).hxs.ne']
  have hbound : |(M n).alpha.val.val r/(M n).xs-kappa*t|<eps := by
    have HH:=hn t ht
    rw [Real.dist_eq,abs_sub_comm] at HH
    simpa only [hrt] using HH
  have hlow : kappa*t-eps<(M n).alpha.val.val r/(M n).xs := by
    have HH := (abs_lt.mp hbound).1
    linarith
  have hup : (M n).alpha.val.val r/(M n).xs<kappa*t+eps := by
    linarith [(abs_lt.mp hbound).2]
  have hmargin1 : eps≤(kappa-cl)/2:=min_le_left _ _
  have hmargin2 : eps≤(cu-kappa)/2:=min_le_right _ _
  have Hstrict : cl*t<(M n).alpha.val.val r/(M n).xs ∧
      (M n).alpha.val.val r/(M n).xs<cu*t := by
    constructor <;> nlinarith only [hlow,hup,hmargin1,hmargin2,ht.1,hcl,hcu]
  constructor
  · have HH:=(lt_div_iff₀ (M n).hxs).mp Hstrict.1
    calc
      cl*r=cl*t*(M n).xs := by rw [←hrt];ring
      _<(M n).alpha.val.val r := HH
  · have HH:=(div_lt_iff₀ (M n).hxs).mp Hstrict.2
    calc
      (M n).alpha.val.val r<cu*t*(M n).xs := HH
      _=cu*r := by rw [←hrt];ring

end ActualHighWallLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
