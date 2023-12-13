import .separabilidad

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