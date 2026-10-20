module

public import ComparisonNativeActualMinimumBroadBudget
public import ComparisonNativeDyadicContactCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def CommonBandGeometry.canonicalDyadicFamily
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {p : a.Potential} (g : a.CommonBandGeometry p)
    (ell : ℕ) (hell : 2 < ell+1) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) :
    NativeDyadicBandFamily
      ((g.canonical 1 zero_lt_one le_rfl (ell+1) hell Q Lside hQ hLside).toModel
        dphys e hlog hnd) where
  model := fun j =>
    (g.canonical (a.context.U*(2:ℝ)^(j:ℕ))
      (comparison_mass_dyadic_scale a.context.hU j).1
      (comparison_mass_dyadic_scale a.context.hU j).2.2
      (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd
  quantile := fun _ => rfl
  potential := fun _ => rfl
  error := fun _ => rfl
  left := fun _ => rfl
  right := fun _ => rfl

end NativeOverlapMinimum

theorem eventually_actual_minimum_constant_clock_dyadic_producer
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(T H : ℝ) (hb : ∀u, a.b u = T) (hh : ∀u, a.h u = H),
      ∃(p : a.Potential) (hlog : 1 ≤ Real.log a.context.N)
        (hnd : 1/a.context.N ≤ a.context.d),
        ∀(Lside : ℝ) (hLside : 0 ≤ Lside),
        let family := (p.constantClockGeometry hb hh).canonicalDyadicFamily
          ell hell Q Lside hQ hLside (Fintype.card (FeatureIndex (n+1))-1)
          (cavityCanonicalFeatureEquiv n) hlog hnd
        ∀j, NativeBandRawMaster (family.model j) := by
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw (D:=D) ell hell
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hgeom := NativeOverlapMinimum.eventually_exists_actual_common_geometry_constant
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have hlog : ∀ᶠn : ℕ in atTop, 1 ≤ Real.log (n+1 : ℝ) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp
        (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop 1)
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hraw,hgeom,hdepth,hlog] with n hnraw hngeom hndepth hnlog
  intro a T H hb hh
  obtain ⟨p,_⟩ := hngeom a T H hb hh
  have hnd : 1/a.context.N ≤ a.context.d := by
    have hd := hndepth a.context.E a.context.d a.context.hE a.context.hd a.hlower
    have hs : comparisonLowerScale (n+1 : ℕ) a.context.E a.context.d ≤ a.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.context.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hd.trans hs
  have hlg : 1 ≤ Real.log a.context.N := by
    simpa only [NativeOverlapContext.N,Nat.cast_add,Nat.cast_one] using hnlog
  refine ⟨p,hlg,hnd,?_⟩
  intro Lside hLside
  dsimp only
  intro j
  exact hnraw a p (p.constantClockGeometry hb hh) (a.context.U*(2:ℝ)^(j:ℕ))
    (comparison_mass_dyadic_scale a.context.hU j).1
    (comparison_mass_dyadic_scale a.context.hU j).2.2
    Lside hLside (Fintype.card (FeatureIndex (n+1))-1) (cavityCanonicalFeatureEquiv n) hlg hnd

end OAI.SKFluctuations.LaplaceWindowFormalization
