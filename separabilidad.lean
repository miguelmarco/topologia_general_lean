import .bases
import .interior
import data.rat.denumerable
import tactic

open topologicos topologicos.espacio_topologico set

/-
# Separabilidad

## Definición 4.1.1.

Sea X un espacio topológico; diremos que X es separable si posee un subconjunto denso y contable.
-/
def separable (X : Type) [espacio_topologico X] := ∃ (S : set X), (denso S ∧ set.countable S)

variables (X : Type) [espacio_topologico X]

example [countable X] : separable X :=
begin
  use univ,
  split,
  {
    rw denso_sii_todo_abierto_interseca,
    simp only [univ_inter, imp_self, implies_true_iff],
  },
  {
    apply countable_univ,
  }
end

lemma abierto_de_separable_es_separable (h : separable X) (U : set X) (hU: abierto U) : separable U :=
begin
  cases h with D hD,
  cases hD with hDd hDc,
  use (D ↓∩ U),
  split,
  {
    rw denso_sii_todo_abierto_interseca at ⊢ hDd,
    intros V hVab hV0,
    cases hVab with W hW,
    cases hW with hWab hWV,
    specialize hDd (W ∩ U) _ _,
    {
      apply abierto_interseccion,
      repeat {assumption},
    },
    {
      rw no_vacio_sii_existe_elemento at hV0 ⊢,
      cases hV0 with x hx,
      use ↑x,
      rw ← hWV at hx,
      simp only [pert_restringe_def] at hx,
      simp only [and_true, subtype.coe_prop, set.mem_inter_iff,hx],
    },
    {
      rw ← hWV,
      rw no_vacio_sii_existe_elemento at ⊢ hDd,
      cases hDd with x hx,
      cases hx with hxD hxWU,
      cases hxWU with hxW hxU,
      use ⟨x,hxU⟩,
      simp only [hxW, hxD, pert_restringe_def, and_self, set.mem_inter_iff, subtype.coe_mk],
    },
  },
  {
    refine maps_to.countable_of_inj_on _ _ hDc,
    {
      intro x,
      exact ↑x,
    },
    {
      intros x hx,
      exact hx,
    },
    {
      intros x hx y hy,
      simp only [coe_injec, imp_self],
    }
  },
end

/- 
# Primer axioma de numerabilidad.

## Definición 4.2.1. 

Diremos que un e.t. `X` es primero numerable (en notación IAN) si todo x ∈ X posee una base contable de entornos. 
-/


def  IAN (X : Type) [espacio_topologico X] := ∀ x : X, ∃ 𝓑ₓ, base_de_entornos x 𝓑ₓ ∧ set.countable 𝓑ₓ 

example : @IAN X (discreta X) := 
begin
  intro x,
  use {{x}},
  split,
  {
    revert x,
    rw ← discreto_sii_puntos_son_base_entornos,
  },
  simp only [set.countable_singleton],
end

section metricosIAN
open metricos metricos.espacio_metrico

theorem metrico_IAN (X : Type) [espacio_metrico X] : IAN X :=
begin
  intro x,
  use {(bola x (1/ (↑n + 1))) | n : ℕ },
  split,
  {
    split,
    {
      intros B hB,
      cases hB with n hn,
      rw ← hn,
      use B,
      rw ← hn,
      split,
      {
        apply bola_abierta,
        simp only [one_div, gt_iff_lt, inv_pos],
        norm_cast,
        linarith,
      },
      split,
      {
        simp only [metricos.bola_carac, one_div, metricos.distancia_cero, inv_pos],
        norm_cast,
        linarith,
      },
      {
        tauto,
      },
    },
    {
      intros V hV,
      cases hV with U hU,
      cases hU with hUab hU2,
      cases hU2 with hxU hUV,
      specialize hUab x hxU,
      cases hUab with ε hε,
      cases hε with hε0 hbol,
      have haux : ∃ n : ℕ , 1 / ε < n,
      {
        exact exists_nat_gt (1 / ε),
      },
      cases haux with n hn,
      have han : 0 < (n : ℝ),
      {

        simp only [one_div, gt_iff_lt] at hε0 hn,
        rw ← inv_pos at hε0,
        linarith,
      },
      use bola x (1 / (↑n + 1)),
      use n,
      intros y hy,
      apply hUV,
      apply hbol,
      simp only [metricos.bola_carac,  gt_iff_lt] at *,
      simp at hn hy,
      rw inv_lt hε0 han at hn,
      calc 
        d x y < (↑n + 1)⁻¹ : by {assumption,}
        ...   < (↑n)⁻¹      : by {rw inv_lt_inv, norm_cast, exact lt_add_one n,linarith, exact han,}
        ...   <  ε         : by {assumption,}
    },
  },
  {
    apply countable_range,
  },
end

end metricosIAN

open function 

theorem IAN_continua_abierta_sobre (X Y: Type) [espacio_topologico X] [espacio_topologico Y] (h : IAN X) 
    (f : X → Y) (hc : continua f) (ha : abierta f) (hs : surjective f) : IAN Y :=
begin
  intro y,
  specialize hs y,
  cases hs with x hx,
  specialize h x,
  cases h with B hB,
  cases hB with hBen hBcon,
  use (set.image f) '' B,
  split,
  split,
  {
    intros E hE,
    cases hE with F hF,
    cases hF with hFB hFE,
    cases hBen with hBN hB,
    specialize hBN hFB,
    cases hBN with V hV,
    cases hV with hVab hV2,
    cases  hV2 with hxV hVF,
    use f '' V,
    split,
    {
      apply ha,
      exact hVab,
    },
    split,
    {
      use x,
      tauto,
    },
    {
      rw ← hFE,
      intros a ha,
      cases ha with b hb,
      cases hb with hb1 hb2,
      use b,
      split,
      {
        apply hVF,
        exact hb1,
      },
        exact hb2,
    },
  },
  {
    intros V hV,
    cases hV with U hU,
    cases hU with hUab hU2,
    cases hU2 with hyU hUV,
    specialize hc U hUab,
    cases hBen with hB1 hB2,
    specialize hB2 (f  ⁻¹' U) _,
    {
      use f ⁻¹' U,
      simp only [hc, hx, hyU, abierto_def, mem_preimage, true_and],
    },
    cases hB2 with W hW,
    cases hW with hWB hWU,
    use (f '' W),
    split,
    {
      use W,
      simp only [eq_self_iff_true, and_self, hWB],
    },
    simp only [set.image_subset_iff],
    intros z hz,
    apply hUV,
    apply hWU,
    exact hz,
  },
  apply countable.image,
  exact hBcon,
end

/-
## Lemma 4.2.4

La propiedad ser IAN es hereditaria.
-/

lemma IAN_hereditaria  (X : Type) [espacio_topologico X] (h : IAN X) (A : set X) : IAN A :=
begin
  intro x,
  cases x with x hx,
  specialize h x,
  cases h with B hB,
  cases hB with hBb hBc,
  cases hBb with hBN hBB,
  use { (U ↓∩ A) | U ∈ B},
  split,
  split,
  {
    intros U hU,
    simp only [𝓝def, entornos_subespacio] ,
    cases hU with U' hU',
    cases hU' with hU' hU'U,
    use U',
    specialize hBN hU',
    rw 𝓝def at hBN,
    split,
      exact hBN,
      rw hU'U,
  },
  {
    intros V hV,
    rw 𝓝def at hV,
    rw entornos_subespacio at hV,
    simp only [exists_prop, mem_set_of_eq, exists_exists_and_eq_and],
    cases hV with V' hV',
    cases hV' with hV'N hV'V,
    rw ← 𝓝def at hV'N,
    specialize hBB V' hV'N,
    cases hBB with U hU,
    cases hU with hUB hUV',
    use U,
    split,
      exact hUB,
    {
      rw hV'V,
      simp [hUV'],
      apply subset_trans _ hUV',
      simp only [set.inter_subset_left],
    },
  },
  {
    refine countable_iff_exists_subset_range.mpr _,
    rw countable_iff_exists_subset_range at hBc,
    cases hBc with f hf,
    use λ n, (f n ) ↓∩ A,
    intros U hU,
    cases hU with U' hU',
    cases hU' with hU'B hU'U,
    specialize hf hU'B,
    cases hf with n hn,
    use n,
    simp only [eq_self_iff_true, hU'U, hn],
  },
end

/-
## Segundo axioma de numerabilidad

Diremos que un e.t. X es segundo numerable (en notación IIAN) si posee una base contable de abiertos.
-/
def  IIAN (X : Type) [espacio_topologico X] := ∃ 𝓑 : set (set X), base 𝓑  ∧ set.countable 𝓑 

lemma IIAN_implica_IAN (X : Type) [espacio_topologico X] (h : IIAN X) : IAN X :=
begin
  cases h with B hB,
  cases hB with hBbas hBc,
  cases hBbas with hBab hB,
  intro x,
  use {U ∈ B | x ∈ U},
  split,
  split,
  {
    intros U hU,
    cases hU with hUB hxU,
    specialize hBab hUB,
    use U,
    split,
      exact hBab,
    split,
      exact hxU,
      tauto,
  },
  {
    intros V hV,
    cases hV with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUV,
    specialize hB U hUab,
    cases hB with F hF,
    cases hF with hFB hFU,
    rw hFU at hxU,
    cases hxU with U' hU',
    cases hU' with hU'F hxU',
    use U',
    split,
    split,
    {
      apply hFB,
      exact hU'F,
    },
    {
      exact hxU',
    },
    {
      apply subset_trans _ hUV,
      rw hFU,
      exact subset_sUnion_of_mem hU'F,
    },
  },
  {
    apply countable.mono _ hBc,
    simp only [set.sep_subset],
  }
end


lemma IIAN_implica_separable (X : Type) [espacio_topologico X] (h : IIAN X) : separable X  :=
begin
  cases h with B hB,
  cases hB with hBbase hBc,
  let A := B \ {∅},
  have hA : ∀ a : A, ∃ x : X, x ∈ a.1,
  {
    intro a,
    cases a with a ha,
    cases ha with hab hne,
    change a ≠ ∅ at hne,
    rw no_vacio_sii_existe_elemento at hne,
    exact hne,
  },
  choose f hf using hA,
  use range f,
  split,
  {
    rw denso_sii_todo_abierto_interseca,
    intros U hUab hUnv,
    rw no_vacio_sii_existe_elemento at ⊢  hUnv,
    rw caracterizacion_base at hBbase,
    cases hUnv with  x hx,
    {
      specialize hBbase U hUab x hx,
      cases hBbase with V hV,
      cases hV with hVB hV2,
      cases hV2 with hVU hxV,
      have haux : V ≠ ∅, 
      {
        rw no_vacio_sii_existe_elemento,
        use x,
        exact hxV,
      },
      use f ⟨V,⟨hVB,haux⟩⟩,
      simp only [true_and, set.mem_range_self, set.mem_inter_iff],
      apply hVU,
      apply hf,
    },
    exact hBbase.1,
  },
  {
    apply @countable_range _ _ _,
    refine countable.to_subtype _,
    apply countable.mono _ hBc,
    simp only [set.diff_singleton_subset_iff, set.subset_insert],
  },
end

open metricos metricos.espacio_metrico
lemma metrico_y_separable_implica_IIAN (X : Type) [espacio_metrico X] (h : separable X) : IIAN X :=
begin
  cases h with D hD,
  cases hD with hDdenso hDcontable,
  let F := { U : set X | ∃ x ∈ D, ∃ r : ℚ , r > 0 ∧ U = bola x ↑r },
  use F,
  split,
  rw caracterizacion_base,
  {
    intros U hU x hx,
    rw denso_sii_todo_abierto_interseca at hDdenso,
    specialize hU x hx,
    rcases hU with ⟨r, ⟨hr,hrbol⟩⟩ ,
    have haux : ∃ q : ℚ , 0 < q ∧ ↑q < r,
    {
      exact exists_pos_rat_lt hr,
    },
    rcases haux with ⟨q,⟨hq0,hqr⟩⟩,
    specialize hDdenso (bola x (q / 2)) _ _,
    {
      apply bola_abierta,
      norm_cast,
      linarith,
    },
    {
      rw no_vacio_sii_existe_elemento,
      use x,
      simp only [metricos.bola_carac, rat.cast_pos, metricos.distancia_cero],
      norm_cast,
      linarith,
    },
    rw no_vacio_sii_existe_elemento at hDdenso,
    rcases hDdenso with ⟨y,⟨hyD,hybola⟩⟩,
    use bola y (q / 2),
    split,
    {
      use y,
      split, exact hyD,
      use q /2,
      split, linarith,
      norm_cast,
    },
    split,
    {
      intros z hz,
      apply hrbol,
      simp only [bola_carac, gt_iff_lt] at *,
      have haux := d4 x y z,
      linarith,
    },
    {
      simp only [bola_carac, gt_iff_lt] at *,
      rw d3,
      exact hybola,
    },
  },
  {
    intros U hU,
    rcases hU with ⟨x,⟨hx,⟨r,⟨hr,hbola⟩⟩⟩⟩,
    rw hbola,
    apply bola_abierta,
    norm_cast,
    exact hr,
  },
  {
    let Q := {q : ℚ // q > 0},
    let f : ↥D × Q → set X := λ ⟨⟨d,hd⟩,⟨q,hq⟩⟩ , bola d ↑q,
    have haux : F = range f,
    {
      ext B,
      split,
      {
        intro h,
        rcases h with ⟨x,⟨hx,⟨q,⟨hq0,hq⟩⟩⟩⟩,
        use ⟨⟨x,hx⟩,⟨q,hq0⟩⟩,
        rw hq,
      },
      {
        intro h,
        rcases h with ⟨⟨⟨x,hx⟩,⟨q,hq0⟩⟩,h⟩,
        use x,
        split,
          exact hx,
        use q,
        split,
          exact hq0,
        rw ← h,
      },
    },
    rw haux,
    apply @countable_range _ _ _,
    apply @prod.countable _ _ _,
    apply countable.to_subtype,
    exact hDcontable,
  }
end

