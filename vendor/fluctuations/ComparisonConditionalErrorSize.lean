module

public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 4800000

def comparisonConditionalScale (N delta E lam : ℝ) : ℝ :=
  N^delta*Real.sqrt N*E/Real.sqrt lam

theorem comparison_conditional_scale_pos {N delta E lam : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam) :
    0<comparisonConditionalScale N delta E lam := by
  unfold comparisonConditionalScale
  positivity

theorem comparison_conditional_scale_square {N delta E lam : ℝ}
    (hN : 0<N) (hlam : 0<lam) :
    lam*(comparisonConditionalScale N delta E lam)^2=N^(2*delta)*N*E^2 := by
  have hsN := Real.sq_sqrt hN.le
  have hsL := Real.sq_sqrt hlam.le
  have hp : (N^delta)^2=N^(2*delta) := by
    rw [←Real.rpow_mul_natCast hN.le]
    congr 1
    norm_num
    ring
  unfold comparisonConditionalScale
  rw [div_pow,mul_pow,mul_pow,hp,hsN,hsL]
  field_simp

theorem comparison_conditional_small_mass_cost {N delta E lam : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam) :
    lam*(comparisonConditionalScale N delta E lam)^2*comparisonSmallMass N E=N^(2*delta)*E := by
  rw [comparison_conditional_scale_square hN hlam]
  unfold comparisonSmallMass
  field_simp

theorem comparison_conditional_floor_mass_cost {N delta E lam : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam) :
    lam*(comparisonConditionalScale N delta E lam)^2*N^(-delta)*comparisonSmallMass N E=N^delta*E := by
  calc
    _=N^(-delta)*(lam*(comparisonConditionalScale N delta E lam)^2*comparisonSmallMass N E) := by ring
    _=N^(-delta)*(N^(2*delta)*E) := by rw [comparison_conditional_small_mass_cost hN hE hlam]
    _=N^delta*E := by rw [←mul_assoc,←Real.rpow_add hN];congr 2;ring

theorem comparison_conditional_inner_length_cost {N delta E lam v L C : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam) (hC : 0≤C)
    (hv : 0≤v) (hvA : v≤C*comparisonConditionalScale N delta E lam)
    (hL : 0≤L) (hLU : L≤comparisonSmallMass N E) :
    lam*v*comparisonConditionalScale N delta E lam*L≤C*N^(2*delta)*E := by
  have hA := comparison_conditional_scale_pos (delta:=delta) hN hE hlam
  have hh := mul_le_mul hvA hLU hL (mul_nonneg hC hA.le)
  have hs := mul_le_mul_of_nonneg_left hh (mul_nonneg hlam.le hA.le)
  have he := comparison_conditional_small_mass_cost (delta:=delta) hN hE hlam
  nlinarith

theorem comparison_conditional_broad_trace_cost {N delta E lam e v : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam)
    (he : N^(-delta)*lam≤e) (hv : comparisonSmallMass N E≤v) :
    lam*(1+v/comparisonSmallMass N E)/(N*e*v)≤2*N^delta*E := by
  have hU : 0<comparisonSmallMass N E := comparisonSmallMass_pos hN hE
  have hvp : 0<v := hU.trans_le hv
  have hep : 0<e := (mul_pos (Real.rpow_pos_of_pos hN _) hlam).trans_le he
  have hp : N^delta*N^(-delta)=1 := by rw [←Real.rpow_add hN];simp
  have hstrength : lam/e≤N^delta := by
    apply (div_le_iff₀ hep).mpr
    have hh := mul_le_mul_of_nonneg_left he (Real.rpow_pos_of_pos hN delta).le
    simpa only [←mul_assoc,hp,one_mul] using hh
  have hNv : 1/(N*v)≤E := by
    have hh := one_div_le_one_div_of_le (mul_pos hN hU) (mul_le_mul_of_nonneg_left hv hN.le)
    have heq : 1/(N*comparisonSmallMass N E)=E := by unfold comparisonSmallMass;field_simp
    exact hh.trans_eq heq
  have heq : lam*(1+v/comparisonSmallMass N E)/(N*e*v)=
      (lam/e)*(1/(N*v)+E) := by
    unfold comparisonSmallMass
    field_simp
    <;> ring
  rw [heq]
  have hh := mul_le_mul hstrength (show 1/(N*v)+E≤2*E by linarith)
    (show 0≤1/(N*v)+E by positivity) (Real.rpow_pos_of_pos hN delta).le
  nlinarith

theorem comparison_conditional_inverse_trace_cost {N delta E lam e v : ℝ}
    (hN : 0<N) (hE : 0<E) (hlam : 0<lam)
    (he : N^(-delta)*lam≤e) (hv : comparisonSmallMass N E≤v) :
    lam/(N*e*v)≤N^delta*E := by
  have hU := comparisonSmallMass_pos hN hE
  have hvp : 0<v := hU.trans_le hv
  have hep : 0<e := (mul_pos (Real.rpow_pos_of_pos hN _) hlam).trans_le he
  have hp : N^delta*N^(-delta)=1 := by rw [←Real.rpow_add hN];simp
  have hs := mul_le_mul_of_nonneg_left he (Real.rpow_pos_of_pos hN delta).le
  have hs' : lam≤N^delta*e := by simpa only [←mul_assoc,hp,one_mul] using hs
  have hm := mul_le_mul_of_nonneg_left hv (mul_pos hN hE).le
  have hm' : 1≤N*E*v := by
    have heq : (N*E)*comparisonSmallMass N E=1 := by unfold comparisonSmallMass;field_simp
    rw [heq] at hm
    simpa only [mul_assoc] using hm
  apply (div_le_iff₀ (mul_pos (mul_pos hN hep) hvp)).mpr
  have ht := mul_le_mul_of_nonneg_left hm' (mul_nonneg (Real.rpow_pos_of_pos hN delta).le hep.le)
  nlinarith

theorem comparison_conditional_outer_floor_cost {N delta m gamma d E : ℝ}
    (hN : 0<N) (hgamma : 0<gamma) (hd : 0<d) (hE : 0<E)
    (hlower : gamma*N^(-(2:ℝ)/3+m)*d≤E) :
    d^3*N^delta*(comparisonSmallMass N E)^2≤(1/gamma^3)*N^(delta-3*m)*E := by
  have hc := pow_le_pow_left₀ (show 0≤gamma*N^(-(2:ℝ)/3+m)*d by positivity) hlower 3
  have hcN := mul_le_mul_of_nonneg_left hc (sq_nonneg N)
  have he : N^2*(gamma*N^(-(2:ℝ)/3+m)*d)^3=gamma^3*N^(3*m)*d^3 := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hN.le,←Real.rpow_natCast N 2]
    calc
      _=gamma^3*(N^(2:ℝ)*N^((-(2:ℝ)/3+m)*(3:ℝ)))*d^3 := by ring
      _=_ := by rw [←Real.rpow_add hN];congr 2;ring
  rw [he] at hcN
  have hp : (1/gamma^3)*N^(-3*m)*(gamma^3*N^(3*m)*d^3)=d^3 := by
    have hn : N^(-3*m)*N^(3*m)=1 := by rw [←Real.rpow_add hN];simp
    calc
      _=((1/gamma^3)*gamma^3)*(N^(-3*m)*N^(3*m))*d^3 := by ring
      _=_ := by rw [hn];field_simp
  have hr : d^3/(N^2*E^3)≤(1/gamma^3)*N^(-3*m) := by
    apply (div_le_iff₀ (by positivity : 0<N^2*E^3)).mpr
    have hh := mul_le_mul_of_nonneg_left hcN (show 0≤(1/gamma^3)*N^(-3*m) by positivity)
    rwa [hp] at hh
  have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg (Real.rpow_pos_of_pos hN delta).le hE.le)
  have hl : d^3/(N^2*E^3)*(N^delta*E)=d^3*N^delta*(comparisonSmallMass N E)^2 := by
    unfold comparisonSmallMass
    field_simp
  have hright : ((1/gamma^3)*N^(-3*m))*(N^delta*E)=(1/gamma^3)*N^(delta-3*m)*E := by
    calc
      _=(1/gamma^3)*(N^(-3*m)*N^delta)*E := by ring
      _=_ := by rw [←Real.rpow_add hN];congr 2;ring
  simpa only [hl,hright] using hh

end OAI.SKFluctuations.LaplaceWindowFormalization
