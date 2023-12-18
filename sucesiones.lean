import .separabilidad
import order.filter.at_top_bot

open topologicos topologicos.espacio_topologico

/-
# Sucesiones


## Definición 4.4.2.

Sea (X, T ) e.t. y S := {xₙ} una sucesión en X. Diremos que x es `límite` de S 
(o que S converge a x, en notación xₙ  → x) si ∀ V entorno de x en X existe n₀ ∈ N tal que ∀n ≥ n₀
 se tiene xₙ ∈ V.
-/
variables {X : Type} [espacio_topologico X]

def converge (s : ℕ → X) (x : X) := ∀ U ∈ 𝓝 X x, ∃ n₀ : ℕ, ∀ n > n₀, s n ∈ U

def Lim (s : ℕ → X)  := { x : X | converge s x}

def punto_de_aglomeracion (s : ℕ → X) (x : X) := ∀ U ∈ 𝓝 X x, ∀ n₀ : ℕ, ∃ n > n₀ , s n ∈ U

def Agl (s : ℕ → X)  := { x : X | punto_de_aglomeracion s x}

lemma limite_en_aglomeracion  (s : ℕ → X) : Lim s ⊆ Agl s :=
begin
  intros x hx,
  intros E hE n₀,
  specialize hx E hE,
  cases hx with n₁ hn₁,
  use max (n₀ + 1) (n₁ + 1),
  split,
    simp only [gt_iff_lt, lt_add_iff_pos_right, lt_max_iff, true_or, eq_self_iff_true, nat.lt_one_iff],
  apply hn₁,
    simp only [gt_iff_lt, lt_add_iff_pos_right, lt_max_iff, eq_self_iff_true, or_true, nat.lt_one_iff],
end

/-
## Observación 4.4.4.
Observa que en las definiciones de límite y punto de
aglomeración podemos cambiar la palabra entorno por abierto que contenga a x.
-/

lemma caracterizacion_limite_abiertos  (s : ℕ → X) (x : X) : converge s x ↔ ∀ U : set X, abierto U →  x ∈ U →  ∃ n₀ : ℕ, ∀ n > n₀, s n ∈ U :=
begin
  split,
  {
    intro h,
    intros U hUab hxU,
    apply h,
    use U,
    tauto,
  },
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize h U hUab hxU,
    cases h with n₀ hn₀,
    use n₀,
    intros n hn,
    specialize hn₀ n hn,
    apply hUE,
    exact hn₀,
  }
end

lemma caracterizacion_aglomeracion_abiertos  (s : ℕ → X) (x : X) : punto_de_aglomeracion s x ↔ ∀ U : set X, abierto U →  x ∈ U →  ∀  n₀ : ℕ, ∃  n > n₀, s n ∈ U :=
begin
  split,
  {
    intro h,
    intros U hU hxU,
    apply h,
    use U,
    tauto,
  },
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize h U hUab hxU,
    intros n₀,
    specialize h n₀,
    cases h with n hn,
    cases hn with hnn₀ hsnU,
    use n,
    split,
      assumption,
      apply hUE,
      exact hsnU,
  }
end

/-
## Observación 4.4.5.
Con los mismos criterios que en la Observación 4.4.4, podemos sustituir entorno o entorno abierto por entorno básico 
una vez fijada una base de entornos del punto candidato a ser límite o punto de aglomeración. 
-/


lemma caracterizacion_limite_entornos_basicos  (s : ℕ → X) (x : X) (B : set (set X)) 
    (hB : base_de_entornos x B) : converge s x ↔ ∀ U  ∈ B,  ∃ n₀ : ℕ, ∀ n > n₀, s n ∈ U :=
begin
  split,
  {
    intro h,
    intros U hU,
    apply h,
    cases hB with hB1 hB2,
    apply hB1,
    exact hU,
  },
  {
    intro h,
    intros E hE,
    cases hB with hB1 hB2,
    specialize hB2 E hE,
    cases hB2 with U hU,
    cases hU with hUB hUE,
    specialize h U hUB,
    cases h with n₀ hn₀,
    use n₀,
    intros n hn,
    specialize hn₀ n hn,
    apply hUE,
    exact hn₀,
  }
end

lemma caracterizacion_aglomeracion_entornos_basicos  (s : ℕ → X) (x : X) (B : set (set X)) 
    (hB : base_de_entornos x B) :  punto_de_aglomeracion s x ↔  ∀ U  ∈ B,  ∀ n₀ : ℕ, ∃ n > n₀, s n ∈ U :=
begin
  split,
  {
    intro h,
    intros U hU,
    apply h,
    apply hB.1,
    exact hU,
  },
  {
    intro h,
    intros E hE,
    cases hB with hB1 hB2,
    specialize hB2 E hE,
    cases hB2 with U hU,
    cases hU with hUB hUE,
    specialize h U hUB,
    intro n₀,
    specialize h n₀,
    cases h with n hn,
    cases hn with hn1 hn2,
    use n,
    split,
      exact hn1,
    {
      apply hUE,
      exact hn2,
    },
  },
end


/-
Una sucesión `t` es una *subsucesión* de otra sucesión `t` si existe una sucesión creciente de números naturales `k` tal que
`s = t ∘ k`
-/
def creciente (k : ℕ → ℕ ) := ∀ a b : ℕ , a < b → k a < k b
/-
Nos será útil esta propiedad de sucesiones crecientes:
-/
lemma creciente_mayor_identidad {k : ℕ → ℕ} (hk : creciente k) (a : ℕ )  : a ≤ k a :=
begin
  induction a with n hind,
  {
    simp only [nat.nat_zero_eq_zero, zero_le'],
  },
  {
    specialize hk n n.succ (lt_add_one n),
    rw nat.succ_le_iff,
    linarith,
  }
end


def subsucesion  (t : ℕ → X) (s : ℕ → X) := ∃ (k : ℕ → ℕ ), creciente k ∧ t = s ∘ k
/-
Unos lemas que nos serán útiles para construir subsuscesiones que cumplen cierta propiedad
-/
lemma existe_subsucesion_cumpliendo_propiedad  (P : Π (n : ℕ ), Prop) (h : ∀ n₀ ,∃  (n >  n₀) , P n) : ∃ k : ℕ → ℕ, creciente k ∧ ∀ n, P (k n) :=
begin
  exact filter.extraction_of_frequently_at_top' h,
end

lemma existe_subsucesion_cumpliendo_propiedad_relativa (P : Π (n m : ℕ ), Prop) (h : ∀ (a : ℕ ), ∃ (b : ℕ ) (H : b ≥ a), P a b) (h2 : ∀ a b c, a < b → P b c → P a c):
   ∃ k : ℕ → ℕ, creciente k ∧ ∀ n, P n (k n) :=
begin
  change ∃ (k : ℕ → ℕ), strict_mono k ∧ ∀ (n : ℕ), P n (k n),
  apply filter.extraction_forall_of_frequently,
  intro n,
  rw  filter.frequently_at_top,
  intro a,
  specialize h (a + n + 1),
  cases h with b hb,
  cases hb with hbn hPb,
  use b,
  split,
    linarith,
  {
    apply h2 _ (a + n + 1),
      linarith,
      exact hPb,
  }
end



/-
Una sucesión `t` es *truncada* de otra sucesión `s` si hay un `m ∈ ℕ` tal que `s(n) = t(n + m)`
-/
def truncada  (t : ℕ → X) (s : ℕ → X) := ∃ (m : ℕ), ∀ a : ℕ, t a = s (a + m)

/-
Dos sucesiones son *asintóticas* si hay una truncación común.
-/
def asintotica  (s : ℕ → X) (t : ℕ → X) := ∃ (r : ℕ → X), truncada r s ∧ truncada r t


def constante  (s : ℕ → X) (x : X ) :=  ∀ (a : ℕ ), s a = x
/-
Una sucesión es *casiconstante* si tiene una truncación constante
-/
def casiconstante  (s : ℕ → X) (x : X) := ∃ t : (ℕ → X), constante t x ∧ truncada t s

/-
Es claro que en un espacio topológico, una sucesión casiconstante converge a la constante.

Será útil este lema:

`nat.sub_add_cancel : ∀ {n m : ℕ}, m ≤ n → n - m + m = n`

(se puede usar para reescribir, pero notar que, como la resta de números naturales no es una operación interna, requiere
demostrar que el sustraendo no es mayor que el minuendo)
-/
lemma casiconstante_converge (s : ℕ → X) (x : X) (hs : casiconstante s x) : x ∈ Lim s :=
begin
  cases hs with t ht,
  cases ht with ht1 ht2,
  cases ht2 with m hm,
  intros U hU,
  use m + 1,
  intros n hn,
  specialize hm (n - m),
  rw ht1 at hm,
  rw nat.sub_add_cancel at hm,
  {
    rw ← hm,
    cases hU with V hV,
    tauto,
  },
  linarith,
end

/-
Otra forma de decir que `x ∈ X` es límite de la sucesión S ⊂ X es que todo entorno de x contiene una subsucesión truncada de S.
-/
lemma converge_carac_truncada  (s : ℕ → X) (x : X) : 
    converge s x ↔ ∀ U ∈ 𝓝 X x, ∃ t : ℕ → X, truncada t s ∧  ∀ n : ℕ, t n ∈ U :=
begin
  split,
  {
    intro h,
    intros U hU,
    specialize h U hU,
    cases h with n₀ hn₀,
    use λ n, s (n + n₀ +1),
    split,
    {
      use n₀ +1,
      ring_nf,
      simp only [eq_self_iff_true, forall_const],
    },
    intro n,
    apply hn₀,
    linarith,
  },
  {
    intro h,
    intros U hU,
    specialize h U hU,
    cases h with t ht,
    cases ht with ht1 ht2,
    cases ht1 with n₀ hn₀,
    use n₀,
    intros n hn,
    specialize hn₀ (n - n₀),
    rw nat.sub_add_cancel at hn₀,
    {
      rw ← hn₀,
      apply ht2,
    },
    linarith,
  },
end

/-
## Propiedades 4.4.10

Sea `s′` subsucesión de `s`, entonces `Limₓ s ⊂ Lımₓ s′ ⊂ Aglₓ s`.
-/
lemma lim_subsusc_contenido (s : ℕ → X) (s' : ℕ → X) (h : subsucesion s' s) : Lim s ⊆ Lim s' :=
begin
  intros x hx,
  intros E hE,
  specialize hx E hE,
  cases hx with n₀ hn₀,
  cases h with k hk,
  cases hk with hkcr hkcss',
  use (n₀),
  intros n hn,
  rw hkcss',
  simp only [function.comp_app],
  apply hn₀,
  have haux := creciente_mayor_identidad hkcr n,
  linarith,
end

lemma lim_subsusc_contenido_agl (s : ℕ → X) (s' : ℕ → X) (h : subsucesion s' s) : Lim s' ⊆ Agl s  :=
begin
  intros x hx E hE n₀,
  cases h with k hk,
  cases hk with hkcr hkcomp,
  specialize hx E hE,
  cases hx with n₁ hn₁,
  rw hkcomp at hn₁,
  specialize hn₁ (max n₀ n₁  + 1) _,
  {
    have haux := le_max_right n₀ n₁,
    linarith,
  },
  use k (max n₀ n₁ + 1),
  split,
  {
    have hm := creciente_mayor_identidad hkcr (max n₀ n₁ + 1),
    have haux := le_max_left n₀ n₁,
    linarith,
  },
  {
    exact hn₁,
  },
end

/-
Sea sₜ subsucesión truncada de s, entonces Lim sₜ = Lim s.
-/
lemma limite_subsucesion_truncada (s sₜ: ℕ → X) (h : truncada sₜ s) : Lim sₜ = Lim s :=
begin
  ext x,
  split,
  {
    intro hx,
    intros E hE,
    specialize hx E hE,
    cases h with k hk,
    cases hx with n₀ hn₀,
    use n₀ + k,
    intros n hn,
    specialize hn₀ (n - k) _,
    simp at *,
    have haux : n = n₀ + k + (n - (n₀ + k)),
    {
      rw add_comm,
      rw nat.sub_add_cancel,
      linarith,
    },
    rw haux,
    rw add_comm,
    rw ← add_assoc,
    rw nat.add_sub_cancel,
    linarith,
    rw hk at hn₀,
    have haux : n - k + k = n,
    {
      apply nat.sub_add_cancel,
      linarith,
    },
    rw haux at hn₀,
    exact hn₀,
  },
  {
    intro h,
    intros E hE,
    specialize h E hE,
    cases h with n₀ hn₀,
    use n₀,
    intros n hn,
    cases h with k hk,
    rw hk,
    apply hn₀,
    linarith,
  }
end

/-
Sea sₐ una sucesión asintótica a s, entonces Lim sₐ = Lim s.
-/
lemma limite_sucesion_asintotica (s sₐ : ℕ → X) (h : asintotica sₐ s) : Lim sₐ = Lim s :=
begin
  cases h with t ht,
  cases ht with hsₐ hs,
  rw ← limite_subsucesion_truncada s t hs,
  rw limite_subsucesion_truncada sₐ t hsₐ,
end

/-
Si s ⊂ A ⊂ X entonces Lim s ⊂ Agl s ⊂ clausura A.
-/
lemma aglomeracion_contenida_clausura_imagen (s : ℕ → X) (A : set X) (h : set.range s ⊆ A) : Agl s ⊆ clausura A :=
begin
  intros x hx,
  rw clausura_caracterizacion_entorno,
  intros V hV,
  specialize hx V hV,
  specialize hx 0,
  cases hx with n hn,
  cases hn with hn0 hsn,
  rw no_vacio_sii_existe_elemento,
  use s n,
  split,
  {
    apply h,
    simp only [set.mem_range_self],
  },
  {
    exact hsn,
  }
end

/-
Sea Y espacio topológico y sea f : X → Y continua, entonces f (Lim S) ⊂
Lim f (S), es decir, si xₙ → x entonces f (xₙ) → f (x). 
-/
lemma imagen_continua_limite_contenida_limite_composicion {Y : Type} [espacio_topologico Y] (f : X → Y) (hf : continua f) (s : ℕ → X) :
f '' (Lim s ) ⊆ Lim (f ∘ s) :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hxl hfxy,
  simp only [Lim, set.mem_set_of_eq] at ⊢ hxl,
  rw caracterizacion_limite_abiertos at ⊢ hxl,
  intros U hU hyU,
  specialize hf U hU,
  specialize hxl _ hf _,
  {
    simp only [set.mem_preimage, hfxy],
    exact hyU,
  },
  exact hxl,
end

/-
Lo mismo ocurre para la aglomeración.
-/
lemma imagen_continua_aglomeracion_contenida_aglomeracion_composicion {Y : Type} [espacio_topologico Y] (f : X → Y) (hf : continua f) (s : ℕ → X) :
f '' (Agl s ) ⊆ Agl (f ∘ s) :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hxl hfxy,
  simp only [Agl, set.mem_set_of_eq] at ⊢ hxl,
  rw caracterizacion_aglomeracion_abiertos at ⊢ hxl,
  intros U hU hyU,
  specialize hf U hU,
  specialize hxl _ hf _,
  {
    simp only [set.mem_preimage, hfxy],
    exact hyU,
  },
  exact hxl,
end

def hausdorff (X : Type) [espacio_topologico X] := ∀ x y : X, x ≠ y →  ∃ U V : set X, abierto U ∧ abierto V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅ 

/-
El límite de sucesiones convergentes en espacios topológicos Hausdorff es
único.
-/
lemma limite_unico_en_hasudorff (hX : hausdorff X) (s : ℕ → X) (x y : X) (hx : converge s x) (hy : converge s y) : x = y :=
begin
  rw caracterizacion_limite_abiertos at hx hy,
  by_contradiction hn,
  specialize hX x y hn,
  rcases hX with ⟨U,⟨V,⟨hU,⟨hV,⟨hxU,⟨hyV,hUV⟩⟩⟩⟩⟩⟩,
  specialize hx U hU hxU,
  specialize hy V hV hyV,
  cases hx with nx hnx,
  cases hy with ny hny,
  specialize hnx (nx + ny + 1) (by linarith),
  specialize hny (nx + ny + 1) (by linarith),
  have haux : s (nx + ny + 1) ∈ U ∩ V,
  {
    split,
    repeat {assumption},
  },
  rw hUV at haux,
  apply haux,
end

/-
Agl s = ⋂ m ∈ N Sm, donde Sm := {xn | m ≤ n}.
-/
def SM (s : ℕ → X) (m : ℕ ) := { (s n) | n ≥ m}

lemma agl_inter_clausura_colas (s : ℕ → X) : Agl s = ⋂ m : ℕ, clausura (SM s m) :=
begin
  ext x,
  split,
  {
    intro h,
    intros C hC,
    cases hC with m hm,
    simp only [] at hm,
    rw ← hm,
    rw clausura_caracterizacion_entorno,
    intros V hV,
    rw no_vacio_sii_existe_elemento,
    specialize h V hV m,
    cases h with n hn,
    cases hn with hnm hsn,
    use s n,
    split,
    {
      use n,
      split,
        linarith,
        refl,
    },
    {
      exact hsn,
    },
  },
  {
    intro h,
    intros V hV n₀,
    simp only [set.mem_Inter] at h,
    specialize h (n₀ + 1),
    rw clausura_caracterizacion_entorno at h,
    specialize h V hV,
    rw no_vacio_sii_existe_elemento at h,
    cases h with y hy,
    cases hy with hy1 hy2,
    cases hy1 with m hm,
    cases hm with hm1 hm2,
    use m,
    split,
      linarith,
    {
      rw hm2,
      exact hy2,
    }
  }
end

/-
Lema auxiliar
-/
lemma IAN_sii_existe_base_encajada : IAN X ↔ ∀ x : X, ∃ f : ℕ → set X, base_de_entornos x (set.range f) ∧ ∀ n : ℕ, f n ⊆ ⋂₀ { (f j) | j < n} :=
begin
  split,
  {
    intro h,
    intro x,
    specialize h x,
    cases h with B hB,
    cases hB with hBbas hBcont,
    rw set.countable_iff_exists_surjective at hBcont,
    cases hBcont with f hf,
    {
      fconstructor,
      {
        intro n,
        exact ⋂₀ { (↑ (f j)) | j < n},
      },
      split,
      {
        split,
        {
          intros S hS,
          simp only [set.mem_range] at hS,
          cases hS with n hn,
          rw ← hn,
          clear hn,
          induction n with n hind,
          {
            simp only [nat.not_lt_zero, is_empty.exists_iff, exists_false, set.set_of_false, set.sInter_empty],
            split,
            split,
            {
              apply abierto_total,
            },
            simp only [set.mem_univ, set.subset_univ, and_self],
          },
          {
            have haux : {_x : set X | ∃ (j : ℕ) (H : j < n.succ), ↑(f j) = _x} = {_x : set X | ∃ (j : ℕ) (H : j < n), ↑(f j) = _x} ∪ { f n} ,
            {
              ext V,
              simp only [set.mem_insert_iff, set.mem_set_of_eq, set.union_singleton],
              split,
              {
                intro h,
                cases h with j hj,
                cases hj with hjn hfj,
                by_cases hje : j < n,
                {
                  right,
                  use j,
                  tauto,
                },
                {
                  have haux : j = n,
                  {
                    rw nat.lt_succ_iff at hjn,
                    linarith,
                  },
                  left,
                  cases haux,
                  rw hfj,
                },
              },
              {
                intro h,
                cases h,
                {
                  use n,
                  split,
                    apply nat.lt_succ_self,
                    rw h,
                },
                {
                  cases h with j hj,
                  cases hj with hjn hjV,
                  use j,
                  split,
                    apply lt_trans hjn (nat.lt_succ_self n),
                    rw hjV,
                },
              },
            },
            rw haux,
            simp only [set.sInter_insert, set.union_singleton],
            apply entornos_N3,
            {
              apply hBbas.1,
              simp only [subtype.coe_prop],
            },
            {
              exact hind,
            },
          },
        },
        {
          intros V hV,
          have haux := hBbas.2 V hV,
          cases haux with U hU,
          cases hU with hUB hUV,
          specialize hf ⟨U,hUB⟩,
          cases hf with n hn,
          use ⋂₀ {_x : set X | ∃ (j : ℕ) (H : j < n + 1), ↑(f j) = _x},
          split,
          {
            use n + 1,
          },
          {
            intros A hA,
            apply hUV,
            apply hA,
            use n,
            rw hn,
            simp only [lt_add_iff_pos_right, eq_self_iff_true, and_self, nat.lt_one_iff, subtype.coe_mk],
          },
        },
      },
      {
        simp only [exists_prop, set.subset_sInter_iff, set.mem_set_of_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
        intros n a hna j hja,
        intros x hx,
        apply hx,
        use j,
        split,
          linarith,
          refl,
      },
    },
    {
      have haux := hBbas.2 set.univ _,
      {
        cases haux with U hU,
        use U,
        cases hU with hUB hU2,
        exact hUB,
      },
      {
        use set.univ,
        simp only [set.subset_univ, abierto_def, set.mem_univ,abierto_total, and_self],
      }
    }
  },
  {
    intro h,
    intro x,
    specialize h x,
    cases h with f hf,
    use set.range f,
    cases hf with hf1 hf2,
    split,
      exact hf1,
      apply set.countable_range,
  }
end



/-
## Proposición 4.4.12.
Sea X e.t. IAN, S = {xn} una sucesión de X y x
un punto de X. Entonces se tiene que:

(1) x ∈ Agl s si y sólo si x ∈ Lim s′ para cierta s′ subsucesión de S
-/


lemma prop_4_4_12_1 (hIAN : IAN X) (s : ℕ → X) (x : X) : x ∈ Agl s ↔ ∃ s' : ℕ → X, subsucesion s' s ∧ x ∈ Lim s' :=
begin
  rw IAN_sii_existe_base_encajada at hIAN,
  specialize hIAN x,
  cases hIAN with f hf,
  cases hf with hfbas hf,
  split,
  {
    intro h,
    suffices haux2 : ∃ (φ : ℕ → ℕ), creciente φ ∧ ∀ (n : ℕ), s (φ n) ∈ f n,
    {
      cases haux2 with k hk,
      use s ∘ k,
      cases hk with hk1 hk2,
      split,
      {
        use k,
        simp only [and_true, eq_self_iff_true],
        exact hk1,
      },
      {
        intros U hU,
        have hE := hfbas.2 U hU,
        cases hE with E hE,
        cases hE with hE1 hE2,
        cases hE1 with n hn,
        use n,
        intros n1 hn1,
        apply hE2,
        rw ← hn,
        specialize hf n1,
        specialize hk2 n1,
        specialize hf hk2,
        apply hf,
        use n,
        tauto,
      },
    },
    let P : ℕ → ℕ → Prop := λ a b , s (b) ∈ f a,
    change ∃ (φ : ℕ → ℕ), creciente φ ∧ ∀ (n : ℕ), P n (φ n),
    apply existe_subsucesion_cumpliendo_propiedad_relativa,
    {
      simp [P], clear P,
      intro n,
      have haux : ∀ n, ∃ n0, n < n0 ∧ s n0 ∈ f n,
      {
        intro n,
        specialize h (f n) _,
        {
          apply hfbas.1,
          simp only [set.mem_range_self],
        },
        specialize h n,
        cases h with n0 hn0,
        use n0,
        cases hn0 with hn0m hsn0,
        split,
          assumption,
          assumption,
      },
      specialize haux n,
      cases haux with b hb,
      use b,
      cases hb with hbn hbP,
      split,
        linarith,
        exact hbP,
    },
    {
      simp [P], clear P,
      intros a b c hab hsc,
      specialize hf b hsc,
      apply hf,
      use a,
      tauto,
    }
  },
  {
    intro h,
    cases h with s' hs',
    cases hs' with hsub hs'lim,
    intros U hU,
    intro n₀,
    specialize hs'lim U hU,
    cases hs'lim with n₁ hn₁,
    cases hsub with k hk,
    cases hk with hk1 hk2,
    use (k (n₀ + n₁ + 1)),
    split,
    {
      have kn₀ := creciente_mayor_identidad hk1 (n₀ + n₁ + 1),
      linarith,
    },
    {
      rw hk2 at hn₁,
      apply hn₁,
      linarith,
    },
  },
end

/-
(2)  Si A ⊂ X, entonces x ∈ clausura A si y sólo si x ∈ Lim S para cierta sucesión S ⊂ A.
-/

lemma prop_4_4_12_2 (hIAN : IAN X) (A : set X) (x : X) : x ∈ clausura A ↔ ∃ s : ℕ → X, set.range s ⊆ A ∧ x ∈ Lim s :=
begin
  split,
  {
    intro h,
    rw clausura_caracterizacion_entorno at h,
    rw IAN_sii_existe_base_encajada at hIAN,
    specialize hIAN x,
    cases hIAN with f hf,
    cases hf with hfbas hfenc,
    cases hfbas with hfent hfbas,
    have haux : ∀ n ,∃ y, y  ∈ A ∩ f n,
    {
      intro n,
      specialize h (f n) _,
      {
        apply hfent,
        simp only [set.mem_range_self],
      },
      rw ← no_vacio_sii_existe_elemento,
      exact h,
    },
    choose s hs using haux,
    use s,
    split,
    {
      intros y hy,
      cases hy with n hn,
      specialize hs n,
      rw ← hn,
      exact hs.1,
    },
    {
      intros U hU,
      specialize hfbas U hU,
      cases hfbas with V hV,
      cases hV with hVf hVU,
      cases  hVf with n hn,
      use n,
      intros n1 hn1,
      apply hVU,
      rw ← hn,
      simp only [set.subset_sInter_iff, set.mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff₂] at hfenc,
      specialize hfenc n1 n hn1,
      apply hfenc,
      specialize hs n1,
      exact hs.2,
    },
  },
  {
    intro h,
    cases h with s hs,
    apply aglomeracion_contenida_clausura_imagen s _ hs.1,
    {
      apply limite_en_aglomeracion,
      exact hs.2,
    },
  }
end

/-
Si Y es un e.t. cualquiera y f : X → Y una aplicación. Entonces f es
continua si y sólo si para toda sucesión {xn} y ∀x ∈ X tal que xn → x
se tiene f (xn) → f (x).
-/

lemma prop_4_4_12_3 (hIAN : IAN X) (Y : Type) [espacio_topologico Y] (f : X → Y) : continua f ↔ ∀ (x : X) (s : ℕ  → X), converge s x → converge (f ∘ s) (f x) :=
begin
  split,
  {
    intro h,
    intros x s hs,
    rw continua_sii_preimagen_entorno_entorno at h,
    intros E hE,
    specialize h x E hE,
    specialize hs (f ⁻¹' E) h,
    exact hs,
  },
  {
    intro h,
    rw IAN_sii_existe_base_encajada at hIAN,
    rw continua_sii_preimagen_entorno_entorno,
    intros x V hV,
    specialize hIAN x,
    cases hIAN with  B hB,
    cases hB with hBBas hBcon,
    simp only [set.subset_sInter_iff, set.mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff₂] at hBcon,
    by_contradiction hn,
    cases hBBas with hBent hBbas,
    have haux : ∀ n : ℕ , ∃ (xn : X), xn  ∈ (B n) ∧ ¬ xn ∈  (f ⁻¹' V),
    {
      by_contra hneg',
      apply hn,
      push_neg at hneg',
      cases hneg' with nx hnx,
      have haux : entorno x (B nx),
      {
        apply hBent,
        simp only [set.mem_range_self],
      },
      cases haux with U hU,
      cases hU with hU1 hU2,
      cases hU2 with hxU hUB,
      use U,
      split,
        assumption,
      split,
        assumption,
      {
        calc
          U   ⊆  B nx : by {exact hUB,}
          ... ⊆  f ⁻¹' V : by {exact hnx,}
      },
    },
    choose s hs using haux,
    specialize h x s _,
    {
      intros E hE,
      specialize hBbas E hE,
      cases hBbas with U hU,
      cases hU with hUB hUE,
      cases hUB with n hn,
      use n,
      intros n1 hn1,
      apply hUE,
      specialize hs n1,
      rw  ← hn,
      specialize hBcon n1 n hn1,
      apply hBcon,
      exact hs.1,
    },
    specialize h V hV,
    cases h with n₀ hn₀,
    specialize hs (n₀ + 1),
    apply hs.2,
    apply hn₀,
    linarith,
  },
end

/-
(4) X es Hausdorff si y sólo si las sucesiones convergentes tienen límite único.
-/
lemma prop_4_4_12_4 (hIAN : IAN X) : hausdorff X ↔ ∀ (x y : X) (s : ℕ → X) , converge s x → converge s y → x = y :=
begin
  split,
  intro h,
  {
    intros x y s hsx hsy,
    by_contra hneg,
    specialize h x y hneg,
    rcases h with ⟨U,⟨V,⟨hU,⟨hV,⟨hxU,⟨hyV,hUV⟩⟩⟩⟩⟩⟩,
    specialize hsx U _,
    {
      use U,
      simp only [hU, hxU, true_and],
    },
    specialize hsy V _,
    {
      use V,
      simp only [hV,hyV,true_and],
    },
    cases hsx with nx hnx,
    cases hsy with ny hny,
    specialize hnx (nx + ny + 1) _,
    {
      linarith,
    },
    specialize hny (nx + ny + 1) _,
    {
      linarith,
    },
    have haux : s (nx + ny + 1) ∈ U ∩ V := ⟨hnx,hny⟩,
    rw hUV at haux,
    cases haux,
  },
  {
    intro h,
    intros x y hxy,
    rw IAN_sii_existe_base_encajada at hIAN,
    have hIANx := hIAN x,
    specialize hIAN y,
    cases hIAN with fy hfy,
    cases hfy with hBy hBy2,
    cases hIANx with fx hfx,
    cases hfx with hBx hBx2,
    by_contra hneg,
    push_neg at hneg,
    have haux : ∀ n, ∃ zn , zn ∈ (fx n) ∩ (fy n) ,
    {
      intro n ,
      cases hBx with hBxent hBx,
      cases hBy with hByent hBy,
      have hUx : entorno x (fx n),
      {
        apply hBxent,
        simp,
      },
      have hVy : entorno y (fy n),
      {
        apply hByent,
        simp,
      },
      cases hUx with U hU,
      cases hVy with V hV,
      specialize hneg U V hU.1 hV.1 hU.2.1 hV.2.1,
      rw no_vacio_sii_existe_elemento at hneg,
      cases hneg with z hz,
      use z,
      split,
      {
        apply hU.2.2,
        exact hz.1,
      },
      {
        apply hV.2.2,
        exact hz.2,
      },
    },
    choose z hz using haux,
    specialize h x y z _ _,
    {
      intros E hE,
      have hE2 := hBx.2 E hE,
      cases hE2 with UE hUE,
      cases hUE with hUEf hUEE,
      cases hUEf with n hn,
      use n,
      intros n1 hn1,
      apply hUEE,
      rw ← hn,
      simp at hBx2,
      specialize hBx2 n1 n hn1,
      apply hBx2,
      specialize hz n1,
      exact hz.1,
    },
    {
      intros E hE,
      have hE2 := hBy.2 E hE,
      cases hE2 with UE hUE,
      cases hUE with hUEf hUEE,
      cases hUEf with n hn,
      use n,
      intros n1 hn1,
      apply hUEE,
      rw ← hn,
      simp at hBy2,
      specialize hBy2 n1 n hn1,
      apply hBy2,
      specialize hz n1,
      exact hz.2,
    },
    exact hxy h,
  }
end

/-
## Proposición 4.4.13.
Sea (X, d) un espacio seudométrico y sea {xn} una sucesión. Entonces, x ∈ Lim xn ⇔ lim d(x, xn) = 0
-/
open metricos metricos.espacio_metrico
lemma prop_4_4_14 (X : Type) [espacio_metrico X] (s : ℕ  → X) (x : X) : x ∈ Lim s ↔ (0 : ℝ ) ∈ Lim (λ n, d x (s n)) :=
begin
  split,
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    rcases hU with ⟨hUab,⟨hxU,hUE⟩⟩,
    specialize hUab 0 hxU,
    cases hUab with ε hε,
    cases hε with hε0 hbolε,
    specialize h (bola x ε) _,
    {
      use bola x ε,
      split,
      {
        apply bola_abierta,
        exact hε0,
      },
      split,
      {
        simp,
        assumption,
      },
      triv,
    },
    cases h with n hn,
    use n,
    intros n1 hn1,
    simp,
    apply hUE,
    apply hbolε,
    specialize hn n1 hn1,
    simp at hn ⊢ ,
    simp [d],
    rw abs_of_nonneg,
    {
      exact hn,
    },
    apply espacio_metrico.d1,
  },
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize hUab x hxU,
    cases hUab with ε hε,
    cases hε with hε0 hεbol,
    specialize h (bola 0 ε ) _ ,
    {
      use bola 0 ε,
      split,
      {
        apply bola_abierta,
        exact hε0,
      },
      split,
      {
        simp,
        exact hε0,
      },
      {
        triv,
      },
    },
    cases h with n hn,
    use n,
    intros n1 hn1,
    specialize hn n1 hn1,
    simp [d] at hn,
    apply hUE,
    apply hεbol,
    simp,
    calc
      d x (s n1)  ≤ | d x (s n1) | : by {apply le_abs_self,}
      ...         < ε               : by {exact hn,}
  }
end
