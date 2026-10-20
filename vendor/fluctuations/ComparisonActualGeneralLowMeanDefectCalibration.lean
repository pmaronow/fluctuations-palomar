module

public import ComparisonActualGeneralDefectBootstrap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter LaplaceWindowFormalization
open scoped Topology
set_option maxHeartbeats 16000000

 theorem scalar_low_factor_lower_of_high_defect
    {B T epsilon d Cd bstar blow chi : ℝ}
    (hB : 0 < B) (hT : T ≤ B) (heps : 0 < epsilon) (_hCd : 0 ≤ Cd)
    (hchi : chi∈Icc (0:ℝ) 1)
    (hbstar : 0 ≤ T-bstar) (hgap : T-bstar ≤ d^2)
    (hlow : blow ≤ T-epsilon)
    (Hdefect : |1-bstar*chi^2| ≤ Cd*d^2)
    (Hsmall : (Cd+1)*d^2 ≤ 1/2)
    (Hroom : 4*B*(Cd+1)*d^2 ≤ epsilon) :
    epsilon/(4*B) ≤ 1-blow*chi^2 := by
  have Hchi2 : chi^2 ≤ 1:=by nlinarith only [hchi.1,hchi.2]
  have HE : 1-T*chi^2=(1-bstar*chi^2)-(T-bstar)*chi^2:=by ring
  have Hprod : |(T-bstar)*chi^2| ≤ d^2:=by
    rw [abs_of_nonneg (mul_nonneg hbstar (sq_nonneg chi))]
    exact (mul_le_of_le_one_right hbstar Hchi2).trans hgap
  have Hcal : |1-T*chi^2| ≤ (Cd+1)*d^2:=by
    rw [HE]
    apply (abs_sub _ _).trans
    nlinarith only [Hdefect,Hprod]
  have HTlower : 1/2 ≤ T*chi^2:=by
    nlinarith only [le_abs_self (1-T*chi^2),Hcal,Hsmall]
  have HBprod:=mul_le_mul_of_nonneg_right hT (sq_nonneg chi)
  have Hchilower : 1/(2*B) ≤ chi^2:=by
    apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
    nlinarith only [HTlower,HBprod]
  have Hlowprod:=mul_le_mul_of_nonneg_right hlow (sq_nonneg chi)
  have Hepsprod:=mul_le_mul_of_nonneg_left Hchilower heps.le
  have Hroom' : (Cd+1)*d^2 ≤ epsilon/(4*B):=
    (le_div_iff₀ (by positivity : 0 < 4*B)).mpr (by nlinarith only [Hroom])
  have Hlowercal : -(Cd+1)*d^2 ≤ 1-T*chi^2:=by
    simpa only [neg_mul] using (neg_le_neg Hcal).trans (neg_abs_le (1-T*chi^2))
  have Hfractions : epsilon*(1/(2*B))=2*(epsilon/(4*B)):=by field_simp;norm_num
  nlinarith only [Hlowercal,Hlowprod,Hepsprod,Hroom',Hfractions]

 theorem original_low_mean_suppression_of_same_scalar_errors
    {B epsilon d S K h b chi Cgap Cr Ch : ℝ}
    (hB : 0 < B) (heps : 0 < epsilon) (hS : 0 ≤ S) (hh : 0 ≤ h)
    (hchi : chi∈Icc (0:ℝ) 1) (hK : K=h+b*S)
    (Hfactor : epsilon/(4*B) ≤ 1-b*chi^2)
    (Hfield : h ≤ Ch*d^3) (G : ℝ)
    (Hmean : |S-G| ≤ Cgap*d^3) (Hscalar : |G-chi^2*K| ≤ Cr*d^3) :
    S ≤ (4*B*(Cgap+Cr+Ch))*d^3/epsilon := by
  have Hchi2 : chi^2 ≤ 1:=by nlinarith only [hchi.1,hchi.2]
  have Herror : |S-chi^2*K| ≤ (Cgap+Cr)*d^3:=by
    have HE : S-chi^2*K=(S-G)+(G-chi^2*K):=by ring
    rw [HE]
    exact (abs_add_le _ _).trans (by nlinarith only [Hmean,Hscalar])
  have Hfield' : chi^2*h ≤ Ch*d^3:=
    (mul_le_of_le_one_left hh Hchi2).trans Hfield
  have HE : (1-b*chi^2)*S=(S-chi^2*K)+chi^2*h:=by rw [hK];ring
  have Hupper : (1-b*chi^2)*S ≤ (Cgap+Cr+Ch)*d^3:=by
    rw [HE]
    nlinarith only [le_abs_self (S-chi^2*K),Herror,Hfield']
  have Hlower:=mul_le_mul_of_nonneg_right Hfactor hS
  have Hpos : 0 < epsilon/(4*B):=by positivity
  have HH : S ≤ ((Cgap+Cr+Ch)*d^3)/(epsilon/(4*B)):=
    (le_div_iff₀ Hpos).mpr (by nlinarith only [Hlower,Hupper])
  convert HH using 1
  field_simp

end OAI.SKFluctuations.Cavity
