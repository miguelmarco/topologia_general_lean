import .topologicos
import tactic

open set
open function
open topologicos
open topologicos.espacio_topologico


/-
En este archivo `X` denotará un espacio topológico
-/

variables {X : Type} [espacio_topologico X]  

/-
Un conjunto es cerrado si su complementario es abierto.
Definimos también el conjunto de los cerrados.
-/

def cerrado (C  : set X) := abierto Cᶜ 
def cerrados : set (set X):= cerrado 

/-
Declaramos la definición de cerrado como lema para usarlo en el simplificador
-/
@[simp]
lemma cerrado_def (C : set X) : cerrado C ↔ abierto Cᶜ :=
begin
  refl,
end

@[simp]
lemma cerrados_def  (C : set X) : C ∈ (cerrados : set (set X)) ↔ abierto Cᶜ :=
begin
  refl,
end


/-
Una aplicación es contínua si y sólo si la preimagen de cualquier cerrado es cerrado
-/

lemma continua_sii_preimagen_cerrado {X Y : Type} [τX : espacio_topologico X] [τY : espacio_topologico Y]
(f : X → Y) : continua f ↔ ∀ (C : set Y), cerrado C → cerrado  (f ⁻¹' C) :=
begin
  split,     -- por doble implicación
  {
    intro h,    -- asumimos que `f` es contínua
    intros C hC,  -- tomamos un conjunto `C` y asumimos que es cerrado
    specialize h Cᶜ,  -- como `f` es contínua, la preimagen de `Cᶜ` es abierto si `Cᶜ`es abierto
    apply h,  
    exact hC,
  },
  {
    intro h,  -- ahora supongamos que la preimagen de un cerrado es cerrado
    intros U hU,  -- tomamos un abierto `U`
    specialize h Uᶜ,  -- aplicamos la hipótesis a `Uᶜ`
    unfold cerrado at h,
    simp at h,   -- simplificamos
    apply h,
    exact hU,
  }
end


lemma cerrado_univ : cerrado (univ : set X) :=
begin
  simp only [cerrado,set.compl_univ],
  exact abierto_vacio,
end

lemma cerrado_vacio  : cerrado (∅  : set X) :=
begin
  simp only [cerrado,set.compl_empty],
  exact abierto_total,
end

/-
La intersección de una familia de cerrados es cerrado
-/
lemma cerrado_inter  (ℱ : set (set X)) (hf : ℱ ⊆ cerrados) :
cerrado ⋂₀ ℱ :=
begin
  simp only [cerrado.equations._eqn_1],
  have haux : (⋂₀ ℱ)ᶜ = ⋃₀ (compl '' ℱ),
  {
    ext,
    simp only [set.mem_sInter, set.mem_Union, set.sUnion_image, iff_self, set.mem_compl_iff, not_forall],
  },
  rw haux,
  apply abierto_union,
  intros U hU,
  cases hU with V hV,
  cases hV with hV1 hV2,
  specialize hf hV1,
  simp only [cerrados_def, abierto_def] at hf,
  rw hV2 at hf,
  exact hf,
end

/-
La unión de dos cerrados es cerrado
-/
lemma cerrado_union {X : Type} [espacio_topologico X] (C D : set X) : cerrado C → cerrado D → cerrado (C ∪ D ) :=
begin
  unfold cerrado,
  simp only [compl_union],
  apply abierto_interseccion,
end

/-
La unión de una familia finita de cerrados es cerrado
-/
lemma cerrado_union_finita  {X : Type} [espacio_topologico X] (ℱ : set (set X)) (hf : ℱ ⊆ cerrados)  (hfin : set.finite ℱ):
cerrado ⋃₀ ℱ :=
begin
  apply set.finite.induction_on' hfin,  -- por inducción en la familia
  {
    simp,    -- veamos que si no tenemos ningún elemento, se cumple
    exact abierto_total,
  },
  {
    intros a S ha hS haS hind, --ahora supongamos que se cumple para un subconjunto `S`,
    --                       y veamos que se cumple también si le añadimos un elemento más
    simp only [sUnion_insert],  
    apply cerrado_union,
    {
      apply hf,  -- `a` es cerrado por estar en `ℱ`
      exact ha,
    },
    apply hind, -- `S` es cerrado por hipótesis de inducción
  }
end

/-
Hemos visto que la familia de cerrados cumple estas tres propiedades
-/
def C1 (𝒞 : set (set X)) := ∅ ∈ 𝒞 ∧ univ ∈ 𝒞
def C2 (𝒞 : set (set X)) := ∀ ℱ  ⊆ 𝒞, ⋂₀ ℱ ∈ 𝒞
def C3 (𝒞 : set (set X)) := ∀ (A B : set X), A ∈ 𝒞 → B ∈ 𝒞 → A ∪ B ∈ 𝒞

lemma CerC1 : C1 (cerrados : set (set X)) := 
begin
  split,
  exact cerrado_vacio,
  exact cerrado_univ,
end

lemma CerC2 : C2 (cerrados : set (set X)) := 
begin
  exact cerrado_inter,
end

lemma CerC3 : C3 (cerrados : set (set X)) :=
begin
  exact cerrado_union,
end

/-
Si una familia de subconjuntos cumple estas propiedades, hay una topología que
la tiene como cerrados.

Construyamos primero la topología, que llamaremos `topologia_por_cerrados`
-/
def topologia_por_cerrados (𝒞 : set (set X)) (h1 : C1 𝒞) (h2 : C2 𝒞) (h3 : C3 𝒞) :
espacio_topologico X :=
{ abiertos := {(Cᶜ ) | C ∈ 𝒞},  -- los abiertos de esta topología son los complementarios de los elemento de la familia
  abierto_total := 
  begin
    cases h1 with hvacio htotal,
    simp,
    exact hvacio,
  end,
  abierto_vacio := 
  begin
    cases h1 with hvacio htotal,
    simp,
    exact htotal,
  end,
  abierto_union := 
  begin
    intros ℱ hℱ,
    let 𝒟 := {(U ᶜ ) | U ∈ ℱ},
    specialize h2 𝒟,
    specialize h2 _,
    {
      intros C hC,
      cases hC with U hU,
      cases hU with hUℱ hUC,
      specialize hℱ hUℱ,
      simp at hℱ,
      cases hℱ with C' hC',
      cases hC' with hC'𝒞 hC'U,
      rw ← hC'U at hUC,
      simp at hUC,
      rw ← hUC,
      exact hC'𝒞,
    },
    have h𝒟ℱ :  ⋃₀ ℱ = (⋂₀ 𝒟)ᶜ ,
    {
      dsimp [𝒟],
      ext,
      simp,
    },
    rw h𝒟ℱ,
    simp [h2],
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    cases hU with Uc hUC,
    cases hUC with hUc𝒞 hUcU,
    cases hV with Vc hVc,
    cases hVc with hVc𝒞 hVcV,
    specialize h3 Uc Vc hUc𝒞 hVc𝒞,
    rw ← hUcU ,
    rw ← hVcV,
    use Uc ∪ Vc,
    simp [h3],
  end }

/-
Ahora veamos que los cerrados de esta topología son exactamente 
la familia con la que hemos empezado.
-/
lemma cerrados_topologia_cerrados (𝒞 : set (set X)) (h1 : C1 𝒞) (h2 : C2 𝒞) (h3 : C3 𝒞) :
@cerrados X (topologia_por_cerrados 𝒞 h1 h2 h3) = 𝒞 :=
begin
  ext C,  -- tomemos un conjunto, y veamos que está en una familia sii está en la otra
  split,
  {
    intro hC,   -- supongamos que está en la familia de cerrados
    cases hC with K hK,  -- ser un cerrado es ser el complementario de un abierto
    cases hK with hK𝒞 hKC, 
    simp at hKC,
    rw ← hKC,
    exact hK𝒞,
  },
  {
    intro hC, -- ahora supongamos que está en la familia inicial
    simp only [cerrados_def], -- para ver que es un cerrado, hay que ver que su complementario es abierto
    use C, -- pero los abiertos están definidos como los complementarios de elementos de `𝒞`
    split, 
      exact hC,
      refl,
  }
end

/-
Por último, veamos que dos topologías cuyos cerrados coincidan, son iguales
-/
lemma cerrados_determinan_topologia (τ1 : espacio_topologico X) (τ2 : espacio_topologico X) (h : @cerrados X τ1 = @cerrados X τ2) :
τ1 = τ2 :=
begin
  ext U, -- tomemos un conjuntl, veamos que es abierto en una si y sólo si lo es en la otra
  split,
  {
    intro hU,  -- supongamos que es abierto en la primera
    have hC : Uᶜ ∈ @cerrados X τ1,  -- veamos que su complemetario está en los cerrados de la primera
    {
      simp,
      exact hU,
    },
    rw h at hC, -- como los cerrados de una coinciden con los de la otra
    simp at hC,  -- tenemos lo buscado
    exact hC,
  },
  {
    intro hU,
    have hC : Uᶜ ∈ @cerrados X τ2,
    {
      simp,
      exact hU,
    },
    rw ← h at hC,
    simp at hC,
    exact hC,
  }
end

/-
# Ejercicios
-/

lemma ejer_2_4_1 : ∀ S : set X, S ∈ @cerrados X (discreta X) :=
begin
  sorry,
end

section ejercicios_metricos
open metricos
open metricos.espacio_metrico

lemma ejer_2_4_4 (X : Type) [espacio_metrico X] (x : X) (ε : ℝ ) (hε : ε > 0) :
cerrado (disco x ε) :=
begin
  sorry,
end


/-
puede ser util este lema:

`nt.lt_of_le : x ≠ y → ?x ≤ y → x < y`
-/

lemma ejer_2_4_4_2 (X : Type) [espacio_metrico X] (x : X) (ε : ℝ ) (hε : ε > 0) :
cerrado (esfera x ε) :=
begin
  sorry,
end

end ejercicios_metricos
