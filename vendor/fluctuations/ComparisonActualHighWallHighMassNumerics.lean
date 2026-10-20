module

public import ComparisonActualHighWallInnovation
public import ComparisonNativeActualHighMassNoiseRates
public import ComparisonNativeActualHighMassReverseRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem high_radius_le_threshold_add_mass (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    a.data.wallRadius a.alpha u ≤ a.z+u/cl := by
  let r:=a.data.wallRadius a.alpha u
  by_cases hr : r ≤ a.z
  · exact hr.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))
  · have hreg:=(a.regular r ⟨(le_of_not_ge hr), (a.data.wallRadius_bounds a.alpha u).2⟩).1
    have hhigh:=a.data.wallRadius_high_mass a.alpha (a.hz.1.trans_lt (lt_of_not_ge hr))
    rw [a.data.wallRadius_spec a.alpha ⟨hhigh.le,hu.2⟩] at hreg
    have H : r ≤ u/cl:=(le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using hreg)
    exact H.trans (le_add_of_nonneg_left (a.data.hrbounds.1.le.trans a.hz.1))

def highMassPower (width v : ℝ) : ℝ :=
  a.data.N*a.data.g (a.data.wallRadius a.alpha (min (width*v) 1))

def highMassHeight (width v : ℝ) : ℝ:=a.xs+min (width*v) 1

def highMassEndpointConstant (width c : ℝ) : ℝ:=max (1/c) (Az/c+width/cl)

theorem highMassPower_pos (width v : ℝ) : 0 < a.highMassPower width v:=
  mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) _)

theorem highMassHeight_nonneg {width v : ℝ} (hw : 0 ≤ width) (hv : 0 ≤ v) :
    0 ≤ a.highMassHeight width v:=add_nonneg a.hxs.le (le_min (mul_nonneg hw hv) zero_le_one)

theorem highMassHeight_le {width c v : ℝ} (hc : 0 < c) (hxsD : a.xs ≤ a.data.d)
    (hvlo : c*a.data.d ≤ v) : a.highMassHeight width v ≤ (1/c+width)*v := by
  have HD : a.data.d ≤ v/c:=(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  have HE : v/c=(1/c)*v:=by ring_nf
  rw [HE] at HD
  unfold highMassHeight
  nlinarith [min_le_left (width*v) (1:ℝ)]

theorem highMassPower_lower (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {width c v : ℝ} (hw : 0 ≤ width) (hc : 0 < c) (hxsD : a.xs ≤ a.data.d)
    (hvlo : c*a.data.d ≤ v) :
    a.data.N*a.data.d^3 ≤ highMassEndpointConstant (Az:=Az) (cl:=cl) width c*a.highMassPower width v*v := by
  let C:=highMassEndpointConstant (Az:=Az) (cl:=cl) width c
  let r:=a.data.wallRadius a.alpha (min (width*v) 1)
  have hv : 0 < v:=(mul_pos hc a.data.hd).trans_le hvlo
  have hC : 0 < C:=(one_div_pos.mpr hc).trans_le (le_max_left _ _)
  have hu : min (width*v) 1∈Icc (0:ℝ) 1:=⟨le_min (mul_nonneg hw hv.le) zero_le_one,min_le_right _ _⟩
  have Hrad:=a.high_radius_le_threshold_add_mass hcl hu
  have Hd : a.data.d ≤ C*v:=by
    have HH : a.data.d ≤ v/c:=(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
    have HC:=mul_le_mul_of_nonneg_right (le_max_left (1/c) (Az/c+width/cl)) hv.le
    dsimp only [C,highMassEndpointConstant]
    have HH' : a.data.d ≤ (1/c)*v:=by simpa only [div_eq_mul_inv,one_div,mul_comm,mul_one] using HH
    exact HH'.trans HC
  have Hr : r ≤ C*v:=by
    have Hxs:=mul_le_mul_of_nonneg_left hxsD hAz
    have Hd' : a.data.d ≤ v/c:=(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
    have Hz:=a.hzxs.trans Hxs
    have Hzd:=mul_le_mul_of_nonneg_left Hd' hAz
    have Hu:=div_le_div_of_nonneg_right (min_le_left (width*v) (1:ℝ)) hcl.le
    have HC:=mul_le_mul_of_nonneg_right (le_max_right (1/c) (Az/c+width/cl)) hv.le
    have Hzd' : Az*a.data.d ≤ (Az/c)*v:=by convert Hzd using 1 <;> ring_nf
    have Hu' : min (width*v) 1/cl ≤ (width/cl)*v:=by convert Hu using 1 <;> ring_nf
    calc
      r ≤ a.z+min (width*v) 1/cl := Hrad
      _ ≤ Az*a.data.d+(width/cl)*v := add_le_add Hz Hu'
      _ ≤ (Az/c+width/cl)*v := by nlinarith only [Hzd']
      _ ≤ C*v := HC
  have hr : 0 < r:=a.data.hrbounds.1.trans_le (a.data.wallRadius_bounds a.alpha _).1
  have HG : a.data.d^3/(C*v) ≤ a.data.g r:=by
    apply le_trans _ (laplaceComparisonStrength_lower a.data.hd (sq_pos_of_pos a.data.hd) hr)
    apply le_min
    · apply (div_le_iff₀ (mul_pos hC hv)).mpr
      nlinarith [mul_le_mul_of_nonneg_left Hd (sq_nonneg a.data.d)]
    · exact div_le_div_of_nonneg_left (pow_nonneg a.data.hd.le 3) hr Hr
  have H:=mul_le_mul_of_nonneg_left ((div_le_iff₀ (mul_pos hC hv)).mp HG) a.data.hN.le
  dsimp only [highMassPower,C,r]
  nlinarith only [H]

theorem high_mass_scale_critical_lower
    (hC0 : 0 < C0) :
    (1/C0)*a.data.N^(-(1:ℝ)/6+m) ≤ a.xs := by
  have Hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd Hlower Hupper).2.2.trans a.hscale

theorem high_mass_inverse_power (hC0 : 0 < C0) (k : ℕ) :
    1/(a.data.N^((k:ℝ)/6)*a.xs^k) ≤ C0^k*a.data.N^(-(k:ℝ)*m):=
  mass_critical_inverse_power a.data.hN a.hxs hC0 (a.high_mass_scale_critical_lower hC0) k

theorem high_mass_critical_ratio
    (hC0 : 0 < C0) :
    a.data.d^3/(a.data.N^2*a.data.E^3) ≤ C0^3*a.data.N^(-3*m) := by
  have hN0 := a.data.hN
  have hE0 := a.data.hE
  have hd0 := a.data.hd
  have Hlo : a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ C0*a.data.E:=by
    simpa only [mul_comm] using a.hlower
  have Hcube:=pow_le_pow_left₀ (by positivity : 0 ≤ a.data.N^(-(2:ℝ)/3+m)*a.data.d) Hlo 3
  have HE : (a.data.N^(-(2:ℝ)/3+m)*a.data.d)^3=
      a.data.N^(-2+3*m)*a.data.d^3:=by
    rw [mul_pow,←Real.rpow_mul_natCast a.data.hN.le]
    congr 1; congr 1; ring_nf
  rw [HE,mul_pow] at Hcube
  have H:=mul_le_mul_of_nonneg_left Hcube
    (show 0 ≤ a.data.N^(-3*m)/(a.data.E^3) by positivity)
  have HEleft : (a.data.N^(-3*m)/a.data.E^3)*
      (a.data.N^(-2+3*m)*a.data.d^3)=a.data.d^3/(a.data.N^2*a.data.E^3):=by
    rw [div_mul_eq_mul_div,←mul_assoc,←Real.rpow_add a.data.hN,
      show -3*m+(-2+3*m)=(-2:ℝ) by ring_nf,Real.rpow_neg a.data.hN.le,Real.rpow_two]
    field_simp
  rw [HEleft] at H
  convert H using 1; field_simp [a.data.hE.ne']

theorem high_mass_cap_strong_rate (hC0 : 0 < C0) :
    (a.data.E/a.data.d^3)*(a.data.d^2/a.xs^4) ≤ C0^3*a.data.N^(-3*m) := by
  have H:=mass_cap_strong_normalization a.data.hN a.data.hE a.data.hd a.hxs
    a.data.hd.le (by norm_num : (0:ℝ) ≤ 1) a.hscale (by simp : a.data.d ≤ 1*a.data.d)
  have HH : (a.data.E/a.data.d^3)*(a.data.d^2/a.xs^4) ≤ a.data.d^3/(a.data.N^2*a.data.E^3):=by
    simpa only [one_pow,one_mul] using H
  exact HH.trans (a.high_mass_critical_ratio hC0)

theorem high_mass_small_ratio
    (hC0 : 0<C0) :
    comparisonSmallMass a.data.N a.data.E/a.xs ≤ C0^3*a.data.N^(-3*m) := by
  have hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H : (a.data.N^(-(2:ℝ)/3+m)*a.data.d)/C0 ≤ a.data.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have H:=comparison_radius_small_mass_ratio a.data.hN (one_div_pos.mpr hC0)
    a.data.hd hlower hupper a.hscale
  simpa only [one_div_div,one_pow,div_pow,div_one,ActualHighWallData.N] using H

theorem high_mass_noise_bounds
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {width c v Q : ℝ} (hw : 16 ≤ width) (hc : 0 < c) (hxsD : a.xs ≤ a.data.d)
    (hvlo : c*a.data.d ≤ v) :
    (((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)*
        (a.data.d^2/a.xs^4) ≤
      (Q^2*(1/c+width)*highMassEndpointConstant (Az:=Az) (cl:=cl) width c/256)^((2:ℝ)/3)*
        C0^4*a.data.N^(-4*m)) ∧
    ((a.data.d^2/a.xs^4)/(a.highMassPower width v*(width*v)^2) ≤
      (highMassEndpointConstant (Az:=Az) (cl:=cl) width c/(256*c))*C0^6*a.data.N^(-6*m)) := by
  let C:=highMassEndpointConstant (Az:=Az) (cl:=cl) width c
  let Cy:=1/c+width
  let P:=a.highMassPower width v
  let y:=a.highMassHeight width v
  have hv : 0 < v:=(mul_pos hc a.data.hd).trans_le hvlo
  have hP : 0 < P:=a.highMassPower_pos width v
  have hC : 0 ≤ C:=(one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have hCy : 0 ≤ Cy:=by dsimp [Cy];positivity
  have Hy:=a.highMassHeight_le (width:=width) hc hxsD hvlo
  have hy : 0 ≤ y:=a.highMassHeight_nonneg (by linarith) hv.le
  have HP:=a.highMassPower_lower (width:=width) hcl hAz (by linarith) hc hxsD hvlo
  have Hinv4:=a.high_mass_inverse_power hC0 4
  have Hinv6:=a.high_mass_inverse_power hC0 6
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at Hinv4
  simp only [Nat.cast_ofNat,show (6:ℝ)/6=1 by norm_num,Real.rpow_one] at Hinv6
  have Hvar:=mass_high_variance_noise_le (Q:=Q) a.data.hN hP a.data.hd hv a.hxs
    hy hCy hC Hy HP
  have HvarInv:=mul_le_mul_of_nonneg_left Hinv4
    (show 0 ≤ (Q^2*Cy*C/256)^((2:ℝ)/3) from Real.rpow_nonneg (by positivity) _)
  have Hwidth : (16*v)^2 ≤ (width*v)^2:=pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right hw hv.le) 2
  have HvarWidth : ((Q^2*y)/(P*(width*v)^2))^((2:ℝ)/3)*(a.data.d^2/a.xs^4) ≤
      ((Q^2*y)/(P*(16*v)^2))^((2:ℝ)/3)*(a.data.d^2/a.xs^4):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 2/3)
    exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg Q) hy) (by positivity)
      (mul_le_mul_of_nonneg_left Hwidth hP.le)
  have HvarFinal : ((Q^2*y)/(P*(width*v)^2))^((2:ℝ)/3)*(a.data.d^2/a.xs^4) ≤
      (Q^2*Cy*C/256)^((2:ℝ)/3)*C0^4*a.data.N^(-4*m):=by
    apply HvarWidth.trans (Hvar.trans _)
    convert HvarInv using 1 <;> ring_nf
  have Hsecond:=mass_high_inverse_noise_le a.data.hN hP a.data.hd hv a.hxs hC hc hxsD hvlo HP
  have HsecondInv:=mul_le_mul_of_nonneg_left Hinv6 (show 0 ≤ C/(256*c) from by positivity)
  have HsecondWidth : (a.data.d^2/a.xs^4)/(P*(width*v)^2) ≤
      (a.data.d^2/a.xs^4)/(P*(16*v)^2):=div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left Hwidth hP.le)
  have HsecondFinal : (a.data.d^2/a.xs^4)/(P*(width*v)^2) ≤
      (C/(256*c))*C0^6*a.data.N^(-6*m):=by
    apply HsecondWidth.trans
    have Hsecond' : (a.data.d^2/a.xs^4)/(P*(16*v)^2) ≤ (C/(256*c))*(1/(a.data.N*a.xs^6)):=by
      convert Hsecond using 1 <;> ring_nf
    exact Hsecond'.trans (by simpa only [mul_assoc] using HsecondInv)
  exact ⟨HvarFinal,HsecondFinal⟩

def highMassDiameter (Cdiam v : ℝ) : ℝ:=
  Cdiam*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v)

def highMassReverse (ell : ℕ) (Q width v diam : ℝ) : ℝ:=
  diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*(a.highMassHeight width v)^ell)^(1/((ell:ℝ)-1))

theorem highMassDiameter_pos {Cdiam v : ℝ} (hCdiam : 0 < Cdiam)
    (hlog : 0 < Real.log a.data.N) (hv : 0 < v) : 0 < a.highMassDiameter Cdiam v:=
  div_pos (mul_pos (mul_pos hCdiam hlog) a.data.hE)
    (mul_pos (mul_pos (Real.rpow_pos_of_pos a.data.hN _) (pow_pos a.data.hd _)) hv)

theorem highMassDiameter_lower
        (hC0 : 0 < C0) (hxs1 : a.xs ≤ 1) {Cdiam v : ℝ} (hCdiam : 0 < Cdiam)
    (hlog : 1 ≤ Real.log a.data.N) (hv : 0 < v) (hv1 : v ≤ 1) :
    (Cdiam/(C0*D^2))*a.data.N^(-delta-(2:ℝ)/3+m) ≤
      a.highMassDiameter Cdiam v := by
  have hD : 0 < D:=a.data.hd.trans_le a.hdD
  have hN:=a.data.hN
  have hE:=a.data.hE
  have hd:=a.data.hd
  have Hlo : a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ C0*a.data.E:=by
    simpa only [mul_comm] using a.hlower
  have HdD : a.data.d ≤ D:=a.hdD
  have HD:=pow_le_pow_left₀ hd.le HdD 2
  have Henergy : a.data.N^(-(2:ℝ)/3+m)/(C0*D^2) ≤ a.data.E/a.data.d^3:=by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have H1:=mul_le_mul_of_nonneg_right Hlo (sq_nonneg a.data.d)
    have H2:=mul_le_mul_of_nonneg_left HD (show 0 ≤ C0*a.data.E by positivity)
    nlinarith only [H1,H2]
  have Hy : (1:ℝ) ≤ Real.log a.data.N/v:=
    (le_div_iff₀ hv).mpr (by linarith)
  have Hfactor:=mul_le_mul_of_nonneg_left Hy
    (show 0 ≤ Cdiam*a.data.N^(-delta)*(a.data.E/a.data.d^3) by positivity)
  have Hbase:=mul_le_mul_of_nonneg_left Henergy
    (show 0 ≤ Cdiam*a.data.N^(-delta) by positivity)
  have HE : Cdiam*a.data.N^(-delta)*(a.data.N^(-(2:ℝ)/3+m)/(C0*D^2))=
      (Cdiam/(C0*D^2))*a.data.N^(-delta-(2:ℝ)/3+m):=by
    calc
      _ = (Cdiam/(C0*D^2))*(a.data.N^(-delta)*a.data.N^(-(2:ℝ)/3+m)):=by ring_nf
      _ = _:=by rw [←Real.rpow_add hN];congr 1;ring_nf
  have HE2 : Cdiam*a.data.N^(-delta)*(a.data.E/a.data.d^3)*(Real.log a.data.N/v)=
      a.highMassDiameter Cdiam v:=by
    unfold highMassDiameter
    rw [Real.rpow_neg hN.le]
    ring_nf
  rw [HE] at Hbase
  apply Hbase.trans
  simpa only [mul_one,HE2] using Hfactor

theorem eventually_highMassDiameter_polynomial_lower
    {m delta cl cu Az C0 Ct D Bclock Cdiam : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hD : 0 < D) (hCdiam : 0 < Cdiam) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → 1 ≤ Real.log a.data.N → ∀v : ℝ,0 < v → v ≤ 1 →
          a.data.N^(-(delta+2)) ≤ a.highMassDiameter Cdiam v := by
  let K:=Cdiam/(C0*D^2)
  have hK : 0 < K:=by dsimp [K];positivity
  have Hlarge:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-delta-2) (eps:=-delta-(2:ℝ)/3+m)
      (by linarith) (1/K))
  filter_upwards [Hlarge] with n hn
  intro a hxs1 hlog v hv hv1
  have H:=mul_le_mul_of_nonneg_left hn hK.le
  have HE : K*((1/K)*a.data.N^(-delta-2))=a.data.N^(-(delta+2)):=by
    field_simp;congr 1;ring_nf
  rw [HE] at H
  exact H.trans (a.highMassDiameter_lower hC0 hxs1 hCdiam hlog hv hv1)

theorem exists_high_mass_reverse_polynomial_order
    {m delta cl cu Az C0 Ct D Bclock c Cdiam width : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hD : 0 < D)
    (hwidth : 0 ≤ width) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ,2 < ell ∧ ∀Q : ℝ,1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ a.data.d →
          ∀v : ℝ,0 < v → v ≤ 1 → c*a.data.d ≤ v →
            a.highMassReverse ell Q width v (a.highMassDiameter Cdiam v)*
                (a.data.d^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  let eps0:=delta/64
  let eps:=delta/4
  let k:=delta+2
  obtain ⟨ell,hEll,hgap⟩:=exists_high_mass_reverse_order
    (show 0 ≤ k by dsimp [k];linarith) (show 0 ≤ eps0 by dsimp [eps0];positivity)
    (show 0 < eps by dsimp [eps];positivity) (by dsimp [eps0,eps];linarith)
  refine ⟨ell,hEll,?_⟩
  intro Q hQ
  let e:=2*(ell:ℝ)*eps0/((ell:ℝ)-1)+(1+k)/((ell:ℝ)-1)
  let Cpow:=(2:ℝ)^(2*(ell:ℝ)/((ell:ℝ)-1))
  let Cy:=1/c+width
  let Ctotal:=Cpow*Cy*Cdiam*C0^3
  let eta:=actualMassSavingExponent m delta
  have hEta:=actualMassSavingExponent_bounds m delta
  have hCy : 0 ≤ Cy:=by dsimp [Cy];positivity
  have htotal : 0 ≤ Ctotal:=by dsimp [Ctotal,Cpow];positivity
  have hsave : 32*eta < 3*m+delta-e:=by
    change e < eps at hgap
    dsimp only [eps] at hgap
    dsimp only [eta]
    nlinarith [hEta.2.2]
  have Hraw:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=0) (eps:=eps0) (by dsimp [eps0];positivity) Q)
  have Hdiam:=eventually_highMassDiameter_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hC0 hD hCdiam
  have Hdecay:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay hsave 1 Ctotal)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hraw,Hdiam,Hdecay,Hlog,eventually_ge_atTop (1:ℕ)] with n hnraw hndiam hnrate hnlog hn
  intro a hxsD v hv hv1 hvlo
  have hxs1 : a.xs ≤ 1:=hxsD.trans a.data.hd1
  let W:=a.data.d
  let diam:=a.highMassDiameter Cdiam v
  let y:=a.highMassHeight width v
  have hN:=a.data.hN
  have hxs:=a.hxs
  have hW : 0 < W:=a.data.hd
  have hN2 : (2:ℝ) ≤ a.data.N:=by
    dsimp [ActualHighWallData.N]
    exact_mod_cast (by omega : 2 ≤ n+1)
  have hlog : 1 ≤ Real.log a.data.N:=hnlog
  have hdiam : 0 < diam:=a.highMassDiameter_pos hCdiam (by linarith) hv
  have hy : 0 < y:=by
    dsimp [y,highMassHeight]
    have hu : 0 ≤ min (width*v) 1:=le_min (by positivity) zero_le_one
    positivity
  have hyN : y ≤ a.data.N:=by
    have Hy : y ≤ 2:=by dsimp [y,highMassHeight];linarith only [min_le_right (width*v) (1:ℝ),hxs1]
    exact Hy.trans hN2
  have hraw : Q ≤ a.data.N^eps0:=by simpa only [Real.rpow_zero,mul_one] using hnraw
  have hdiamN : a.data.N^(-k) ≤ diam:=hndiam a hxs1 hlog v hv hv1
  have Hreverse:=mass_reverse_power_extraction (p:=(ell:ℝ)) (a:=1) (k:=k) (eps0:=eps0)
    hN hdiam (zero_lt_one.trans_le hQ) hy
    (by exact_mod_cast hEll) hraw (by simpa only [Real.rpow_one] using hyN) hdiamN
  have Hactual : a.highMassReverse ell Q width v diam ≤ Cpow*a.data.N^e*y*diam:=by
    unfold highMassReverse
    have Hpow : (2*Q)^((2:ℝ)*(ell:ℝ))=(2*Q)^(2*ell):=by
      rw [show 2*(ell:ℝ)=((2*ell:ℕ):ℝ) by push_cast;ring_nf,Real.rpow_natCast]
    rw [Hpow,Real.rpow_natCast] at Hreverse
    simpa only [y,Cpow,e] using Hreverse
  have Hy:=a.highMassHeight_le (width:=width) hc hxsD hvlo
  have Hnorm:=mul_le_mul_of_nonneg_right Hactual (show 0 ≤ W^2/a.xs^4 by positivity)
  have HyNorm:=mul_le_mul_of_nonneg_right Hy
    (show 0 ≤ Cpow*a.data.N^e*diam*(W^2/a.xs^4) by dsimp [Cpow];positivity)
  have Hcap:=a.high_mass_cap_strong_rate hC0
  have HcapMul:=mul_le_mul_of_nonneg_left Hcap
    (show 0 ≤ Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta) by dsimp [Cpow];positivity)
  have HE : Cpow*a.data.N^e*(Cy*v)*diam*(W^2/a.xs^4)=
      (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
        ((a.data.E/a.data.d^3)*(W^2/a.xs^4)):=by
    dsimp [diam,highMassDiameter]
    rw [Real.rpow_neg hN.le]
    field_simp
  have HE2 : (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
      (C0^3*a.data.N^(-3*m))=
      Ctotal*(Real.log a.data.N)^1*a.data.N^(-(3*m+delta-e)):=by
    dsimp [Ctotal]
    rw [show (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
      (C0^3*a.data.N^(-3*m))=
      (Cpow*Cy*Cdiam*C0^3)*Real.log a.data.N*
        ((a.data.N^e*a.data.N^(-delta))*a.data.N^(-3*m)) by ring_nf,
      ←Real.rpow_add hN,←Real.rpow_add hN]
    rw [show e + -delta + -3*m=-(3*m+delta-e) by ring_nf,pow_one]
  have Hfinal : a.highMassReverse ell Q width v diam*(W^2/a.xs^4) ≤
      Ctotal*(Real.log a.data.N)^1*a.data.N^(-(3*m+delta-e)):=by
    apply Hnorm.trans
    have Hyn : Cpow*a.data.N^e*y*diam*(W^2/a.xs^4) ≤
        Cpow*a.data.N^e*(Cy*v)*diam*(W^2/a.xs^4):=by nlinarith only [HyNorm]
    apply Hyn.trans
    rw [HE]
    exact HcapMul.trans_eq HE2
  exact Hfinal.trans hnrate

theorem eventually_high_mass_noise_polynomial
    (Q width c : ℝ) (hwidth : 16 ≤ width) (hc : 0 < c)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs ≤ a.data.d → ∀v : ℝ,c*a.data.d ≤ v →
        (((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)*
          (a.data.d^2/a.xs^4) ≤ a.data.N^(-(32*actualMassSavingExponent m delta))) ∧
        ((a.data.d^2/a.xs^4)/(a.highMassPower width v*(width*v)^2) ≤
          a.data.N^(-(32*actualMassSavingExponent m delta))) := by
  let eta:=actualMassSavingExponent m delta
  let C:=highMassEndpointConstant (Az:=Az) (cl:=cl) width c
  let Cvar:=(Q^2*(1/c+width)*C/256)^((2:ℝ)/3)*C0^4
  let Cinv:=(C/(256*c))*C0^6
  have HE:=actualMassSavingExponent_bounds m delta
  have H1:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-4*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [HE.2.1]) Cvar)
  have H2:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-6*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [HE.2.1]) Cinv)
  filter_upwards [H1,H2] with n hn1 hn2
  intro a hxsD v hvlo
  have H:=a.high_mass_noise_bounds (Q:=Q) hcl hAz hC0 hwidth hc hxsD hvlo
  exact ⟨H.1.trans hn1,H.2.trans hn2⟩

theorem high_mass_energy_cubic_le_test
        (hN : 1 ≤ a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1) :
    a.data.E/a.data.d^3 ≤ Ct*(1+Real.log a.data.N)*a.xs*(comparisonSmallMass a.data.N a.data.E) := by
  have hE := a.data.hE
  have hd := a.data.hd
  have hN0 := a.data.hN
  have HG := laplaceComparisonStrength_le_log_cubic hN a.data.hd hnd (sq_pos_of_pos a.data.hd) (le_rfl : a.data.d^2 ≤ a.data.d^2) a.hxs hxs1
  have H := a.htest.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HG hCt) (sq_nonneg a.xs))
  have HE : a.data.N*a.data.E^2 ≤ Ct*(1+Real.log a.data.N)*a.data.d^3*a.xs := by
    convert H using 1
    field_simp
  have Hmul := mul_le_mul_of_nonneg_right HE
    (show 0 ≤ 1/(a.data.N*a.data.E) by positivity)
  apply (div_le_iff₀ (pow_pos a.data.hd 3)).mpr
  change a.data.E ≤ Ct*(1+Real.log a.data.N)*a.xs*
    (1/(a.data.N*a.data.E))*a.data.d^3
  convert Hmul using 1 <;> field_simp [hN0.ne',hE.ne']

theorem highMassDiameter_source_power_le
        (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v) :
    A*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v) ≤
      (2*A*Ct*C0^3)*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) := by
  have hN0 := a.data.hN
  have hd := a.data.hd
  have hx := a.hxs
  have hL : 0 ≤ Real.log a.data.N := zero_le_one.trans hlog
  have HE := a.high_mass_energy_cubic_le_test hN hnd hCt hxs1
  have HU := a.high_mass_small_ratio hC0
  have HL : Real.log a.data.N*(1+Real.log a.data.N) ≤ 2*(Real.log a.data.N)^2 := by nlinarith
  have HP : a.data.N^(-3*m)/a.data.N^delta=a.data.N^(-(3*m+delta)) := by
    rw [div_eq_mul_inv,←Real.rpow_neg hN0.le,←Real.rpow_add hN0]
    congr 1
    ring_nf
  calc
    _ = (A*Real.log a.data.N/(a.data.N^delta*v))*(a.data.E/a.data.d^3) := by field_simp
    _ ≤ (A*Real.log a.data.N/(a.data.N^delta*v))*(Ct*(1+Real.log a.data.N)*a.xs*(comparisonSmallMass a.data.N a.data.E)) :=
      mul_le_mul_of_nonneg_left HE (by positivity)
    _ = (A*Ct*(Real.log a.data.N*(1+Real.log a.data.N)))*((comparisonSmallMass a.data.N a.data.E)/a.xs)*(a.xs^2/v)/a.data.N^delta := by
      field_simp
    _ ≤ (A*Ct*(2*(Real.log a.data.N)^2))*(C0^3*a.data.N^(-3*m))*(a.xs^2/v)/a.data.N^delta := by
      gcongr
      exact div_nonneg a.data.hU.le hx.le
    _ = (2*A*Ct*C0^3)*(Real.log a.data.N)^2*(a.xs^2/v)*(a.data.N^(-3*m)/a.data.N^delta) := by ring_nf
    _ = _ := by rw [HP]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
