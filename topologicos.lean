import .metricos
import .funciones
import data.set.basic
import tactic



open set
open function



/-
# Espacios topológicos

Un espacio topológico es un conjunto (que en Lean representaremos como un tipo)
con una estructura añadida.

Esta estructura está formada por
- Una familia de subconjuntos, llamados *abiertos*
- Una serie de propiedades (en Lean, demostraciones de ciertas proposiciones):
  - `abierto_total` : el total forma parte de los abiertos
  - `abierto_vacio` : el vacio forma parte de los abiertos
  - `abierto_union` : la unión de una familia de abiertos es un abierto
  - `abierto_interseccion`: la intersección de una familia finita de abiertos es un abierto

La forma de representar este tipo de estructuras es mediante una **clase**:
-/

namespace topologicos

@[ext]
class espacio_topologico (X : Type) :=
( abiertos : set (set X))
( abierto_total : (univ : set X) ∈ abiertos)
( abierto_vacio : ∅ ∈ abiertos)
( abierto_union : ∀ ℱ : set (set X), (ℱ ⊆ abiertos → ⋃₀ ℱ ∈ abiertos ) )
( abierto_interseccion :  ∀ (U V : set X), U ∈ abiertos → V ∈ abiertos → U ∩ V ∈ abiertos)

open espacio_topologico -- así podemos  escribir `abiertos` en lugar de `espacio_topologico.abiertos`

-- lo que caracteriza a la estructura de espacio topológico es el conjunto de abiertos
lemma igualdad_topologias {X : Type} (τ1 : espacio_topologico X) (τ2 : espacio_topologico X) :
τ1 = τ2 ↔ τ1.abiertos = τ2.abiertos :=
begin
  split,
  {
    intro h,
    rw h,
  },
  {
    intro h,
    ext,
    rw h,
  }
end

-- por comodidad, definimos la propiedad de ser abierto como pertenecer al conjunto de abiertos
-- (internamente, Lean los trata igual)
def abierto {X : Type} [𝒯:espacio_topologico X] (U : set X) := U ∈ 𝒯.abiertos


-- y demostrar este lema trivial permite al simplificador aplicar la equivalencia automáticamente
@[simp]
lemma abierto_def  {X : Type} [𝒯:espacio_topologico X] (U : set X) : abierto U ↔ U ∈ 𝒯.abiertos:=
begin
  refl,
end

-- es fácil ver quela unión de dos abiertos también es abierto
-- para demostrarlo, simplemente vemos que es un caso particulares de familias (de dos conjuntos)
lemma union_2_eq {X : Type} (U V : set X) : U ∪ V  = ⋃₀ {U,V} :=
begin
  simp,
end

-- análogamente, vemos que ocurre lo mismo para la intersección
lemma interseccion_2_eq {X : Type}  ( U V : set X) : U ∩ V = ⋂₀ {U,V} :=
begin
  simp,
end

-- veamos pues que la unión de dos abiertos es abierto
lemma abierto_union_2 {X : Type} [espacio_topologico X] (U V : set X) (hU :abierto U) (hV : abierto V) :
abierto (U ∪ V) :=
begin
  rw union_2_eq,  -- lo escribimos como unión de una familia
  apply abierto_union,
  intros S hS,
  simp at hS,
  cases hS,
  repeat {rw hS, assumption,},
end

-- ahora veamos que la intersección de una cantidad finita de abiertos es abierto
lemma abierto_interseccion_finita {X : Type} [espacio_topologico X]  (ℱ : set (set X)) (hab: ℱ ⊆ abiertos) (hfin : set.finite ℱ) :
abierto ⋂₀ ℱ :=
begin
  -- vamos a hacerlo por inducción, para ello, necesitamos que la propiedad de ser abiertos
  -- forme parte de la hipótesis de inducción
  -- para ello, usamos la táctica `revert`, que hace lo contrario que `intro`
  revert hab,
  apply finite.induction_on hfin,
  {  -- caso de familia vacía
    simp only [empty_subset, sInter_empty, abierto_def, forall_true_left],
    exact abierto_total,
  },
  {  -- paso de inducción: suponiendo que es cierto para una familia, 
     -- lo demostramos para el resultado de añadirle un elemento más
     -- `insert a S` es el conjunto resultante de añadir `a`al conjunto `S`
    intros A S hAS hSfin hSab hASab,
    simp only [sInter_insert, abierto_def],
    apply abierto_interseccion,
    {
      apply hASab,
      left,
      refl,
    },
    {
      apply hSab,
      intros U hU,
      apply hASab,
      right,
      exact hU,
    }
  }
end



/-
Se puede definir una topología a partir de una estructura de espacio métrico

Ejercicio: completar las demostraciones de que cumple los axiomas de topología
(es decir, sustituye los `sorry` por las demostraciones correspondientes)
-/
instance topologia_metrico {X : Type} [metricos.espacio_metrico X] : espacio_topologico X :=
{ abiertos := {U : set X | ∀ x ∈ U, metricos.entorno x U},
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}




/-
Demostramos un resultado trivial para poder usarlo más adelante
-/
@[simp]
lemma topologia_metrico_def {X : Type} [metricos.espacio_metrico X] : abiertos = {U : set X | ∀ x ∈ U, metricos.entorno x U} :=
begin
  refl,
end



/-
Ahora definimos topologías concretas

Igual que antes, demostrar que cumplen las propiedades se deja como ejercicio
-/

def discreta (X : Type) : espacio_topologico X :=
{ abiertos := univ,
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}

/-
Como antes, demostramos un lema trivial para usarlo con el simplificador
-/
@[simp]
lemma discreta_sii (X : Type) (U : set X) : U ∈ @abiertos X (discreta X) ↔ true :=
begin
  refl,
end

@[simp]
lemma abiertos_discreta_def (X : Type) : @abiertos X (discreta X) = (univ : set (set X)) :=
begin
  refl,
end 

def indiscreta (X : Type) : espacio_topologico X :=
{ abiertos := {∅ , univ },
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}


@[simp]
lemma abiertos_indiscreta_def (X : Type) : @abiertos X (indiscreta X) = {∅ , univ} :=
begin
  refl,
end


def punto_incluido (X : Type) (x : X) : espacio_topologico X :=
{ abiertos := {U : set X | x ∈ U} ∪ {∅},
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end, 
}


@[simp]
lemma abiertos_punto_incluido_def (X : Type) (x : X) : 
@abiertos X (punto_incluido X x) = {U  | x ∈ U} ∪ {∅}:=
begin
  refl,
end


-- para demostrar este ejercicio, puede ser útil usar la táctica `choose`
-- y el lema 
-- `finite.dependent_image : F.finite →  ∀ (g : Π (x : X), x ∈ F → Y), {y : Y | ∃ (x : X) (hx : x ∈ F), y = F x hx}.finite`
def imagen_inversa {X Y : Type} [τY : espacio_topologico Y] (f : X → Y) : espacio_topologico X :=
{ abiertos := {(f ⁻¹' V) | V ∈ τY.abiertos},
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}



@[simp]
lemma abiertos_imagen_inversa_def (X Y : Type) [Ty : espacio_topologico Y] (f : X → Y) : 
@abiertos X (imagen_inversa f) = {(f ⁻¹' V) | V ∈ Ty.abiertos}:=
begin
  refl,
end

def imagen_directa {X Y: Type} [τX :espacio_topologico X] (f : X → Y): espacio_topologico Y :=
{ abiertos := {V : set Y | f ⁻¹' V ∈ τX.abiertos},
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}


@[simp]
lemma abiertos_imagen_directa_def (X Y : Type) [Tx : espacio_topologico X] (f : X → Y) : 
@abiertos Y (imagen_directa f) =  {V : set Y | f ⁻¹' V ∈ Tx.abiertos}:=
begin
  refl,
end

def cofinita (X : Type) : espacio_topologico X :=
{ abiertos := {U : set X | set.finite Uᶜ } ∪ {∅},
  abierto_total := 
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end }

@[simp]
lemma abiertos_cofinita_def  {X : Type}:
(@abiertos  X (cofinita X)) =  {U : set X | set.finite Uᶜ } ∪ {∅} :=
begin
  refl,
end

/-
Para demostrar que la topología conumerable es una topología, 
usamos la noción de conjunto contable, que en Lean se ha definido como
`countable`


pueden ser útiles estos resultados:

`countable.mono : A ⊆ B → B.countable → A.countable`
`sInter_eq_compl_sUnion_compl : ∀ (S : set (set X)), ⋂₀ S = (⋃₀ (compl '' S))ᶜ`
`countable.bUnion : F.countable → (∀ (a : set X) (H : a ∈ F), (f a H).countable) → (⋃ (a : set X) (H : a ∈ F), f a H).countable `
`finite.countable : A.finite → A.countable`
`countable.sUnion : F.countable → (∀ (a : set X), a ∈ F → a.countable) → (⋃₀ F).countable`
-/


def conumerable (X : Type) : espacio_topologico X :=
{ abiertos := {U : set X | set.countable Uᶜ } ∪ {∅},
  abierto_total :=
  begin
    sorry,
  end,
  abierto_vacio := 
  begin
    sorry,
  end,
  abierto_union := 
  begin
    sorry,
  end,
  abierto_interseccion := 
  begin
    sorry,
  end
}

@[simp]
lemma abiertos_conumerable_def {X : Type}  :
@abiertos X (conumerable X) = {U | set.countable Uᶜ} ∪ {∅}  :=
begin
  refl,
end

-- A partir de ahora, vamos a fijar que `X, Y, Z` denotarán conjuntos con 
-- estructura de espacio topológico
variables {X Y Z : Type} [ espacio_topologico X] [espacio_topologico Y] [espacio_topologico Z]



/-
## Continuidad

definimos la noción de aplicación contínua
-/

def continua {X Y : Type} [τX : espacio_topologico X] [τY : espacio_topologico Y] (f : X → Y) :=
∀ U : set Y,  U ∈ τY.abiertos → (f ⁻¹' U) ∈ τX.abiertos


-- si queremos decir que una aplicación es contínua en una topología concreta, hay que escribir
-- `@continua` y dar explícitamente los espacios de partida y llegada y sus respectivas topologías
-- si ponemos `_` en lugar de alguno de estos datos, Lean lo intenta calcular automáticamente 
example (X Y : Type) [espacio_topologico Y] (f : X → Y) : @continua X Y (discreta X) _ f:=
begin
  tauto,  -- es una tautología que un conjunto de X sea un conjunto de X
end

-- Ejercicio 2_1_5 (a)
example (X Y : Type) [espacio_topologico X] (f : X → Y) : @continua _ _ _ (indiscreta Y) f:=
begin
  sorry,
end



-- la composición de aplicaciones contínuas es contínua
lemma composicion_continuas (f : X → Y) (g : Y → Z): continua f → continua g → continua (g ∘ f) :=
begin
  intro hf,
  intro hg,
  intro W,
  intro hW,
  specialize hg  W hW,
  specialize hf _ hg,
  exact hf,
end

-- Ejercicio 2.1.4
lemma identidad_continua : continua (identidad : X → X) :=
begin
  sorry,
end

def homeomorfismo  (f : X → Y) :=
continua f ∧ ∃ g : Y → X, continua g ∧ inversas f g

lemma identidad_homeo : homeomorfismo (identidad : X → X) :=
begin
  split,
  {
    exact identidad_continua,
  },
  split,
  split,
  exact identidad_continua,
  split,
  {
    refl,
  },
  refl,
end

lemma inversa_homeo_es_homeo (f : X → Y)  (g : Y → X) (hom : homeomorfismo f) (hfg : inversas f g)
:
homeomorfismo g :=
begin
  split,
  {
    cases hom with hf hg',
    cases hg' with g' hg',
    cases hg' with hgcont hginv,
    have geqg' : g = g',
    {
      apply inversa_unica f,
      exact hfg,
      exact hginv,
    },
    rw geqg',
    exact hgcont,
  },
  {
    use f,
    cases hom with hfcont hhom,
    rw inversas_sii,
    tauto,
  }
end

lemma composicion_homeos (f : X → Y) (g : Y → Z) (homf : homeomorfismo f) (homg : homeomorfismo g)
:
homeomorfismo (g ∘ f) :=
begin
  cases homf with contf hf,
  cases homg with contg hg,
  split,
  {
    apply composicion_continuas,
    exact contf,
    exact contg,
  },
  {
    cases hf with finv hfinv,
    cases hfinv with hfinvcont hfinv,
    cases hg with ginv hginv,
    cases hginv with hginvcont hginv,
    use finv ∘ ginv,
    split,
    {
      apply composicion_continuas,
      exact hginvcont,
      exact hfinvcont,
    },
    {
      cases hfinv with hfinv1 hfinv2,
      cases hginv with hginv1 hginv2,
      split,
      {
        change (finv ∘ (ginv ∘ g) ∘ f) = identidad,
        rw hginv1,
        ext,
        simp [identidad, hfinv1],
      },
      {
        change (g ∘ (f ∘ finv) ∘ ginv) = identidad,
        rw hfinv2,
        ext x,
        simp [identidad, hginv2],
      },
    }
  }
end

lemma H4ab (f : X → Y) (hbi: bijective f): homeomorfismo f ↔ ∀ (V : set Y), abierto V ↔ abierto (f ⁻¹' V) :=
begin
  split,
  {
    intro h,
    cases h with hfcont hfinv,
    cases hfinv with g hg,
    cases hg with hgcont hinv,
    intro V,
    split,
    {
      intro hV,
      apply hfcont,
      exact hV,
    },
    {
      intro hV,
      cases hinv with hfinvg hginvf,
      specialize hgcont (f ⁻¹' V) hV,
      have haux : V = (g ⁻¹' ( f ⁻¹' V)),
      {
        ext y,
        change y ∈ V ↔ (f ∘ g) y ∈ V,
        simp [hginvf, identidad],
      },
      {
        rw haux,
        exact hgcont,
      },
    },
  },
  {
    intro h,
    split,
    {
      intros V hV,
      specialize h V,
      unfold abierto at *,
      rw ← h,
      exact hV,
    },
    {
      let g := inversa f hbi,
      use g,
      split,
      {
        intros U hU,
        specialize h (g ⁻¹' U),
        simp [abierto] at h,
        rw h,
        have haux :f ⁻¹' (g ⁻¹' U) = U,
        {
          change (g ∘ f) ⁻¹' U = U,
          have hinv := inversa_es_inversa_izquierda f hbi,
          rw hinv,
          simp [identidad],
        },
        rw haux,
        exact hU,
      },
      split,
      {
        apply inversa_es_inversa_izquierda,
      },
      {
        apply inversa_es_inversa_derecha,
      }
    }
  }
end

lemma H4bc (f : X → Y) (hbi: bijective f): (∀ (V : set Y), abierto V ↔ abierto (f ⁻¹' V)) ↔ (∀ (U : set X), abierto U ↔ abierto (f '' U )):=
begin
  cases hbi with hinj hsup,
  split,
  {
    intro h,
    intro U,
    specialize h (f '' U),
    simp [hinj] at h,
    unfold abierto,
    rw h,
  },
  {
    intro h,
    intro V,
    specialize h (f ⁻¹' V),
    simp [hsup] at h,
    simp [abierto],
    rw h,
  }
end

lemma H4cd (f : X → Y) (hbi: bijective f) :  (∀ (U : set X), abierto U ↔ abierto (f '' U )) ↔ (bijective (image f) ∧ (image f) '' abiertos = abiertos ∧ (image f) ⁻¹' abiertos = abiertos) :=
begin
  cases hbi with hinj hsup,
  split,
  {
    intro h,
    split,
    {
      split,
      {
        intros U V hfUV,
        calc
        U   =  f ⁻¹' (f '' U)   : by {simp [hinj],}
        ... =  f ⁻¹' (f '' V)   : by {rw hfUV,}
        ... = V                 : by {simp [hinj],}
      },
      intro V,
      use f ⁻¹' V,
      simp [hsup],
    },
    split,
    {
      ext V,
      split,
      {
        intro hV,
        cases hV with U hU,
        cases hU with hUab hUV,
        specialize h U,
        unfold abierto at h,
        rw h at hUab,
        rw hUV at hUab,
        exact hUab,
      },
      {
        intro hV,
        simp,
        use f ⁻¹' V,
        split,
        {
          specialize h (f ⁻¹' V),
          simp at h,
          rw h,
          simp [hsup],
          exact hV,
        },
        {
          simp [hsup],
        }
      },
    },
    {
      ext U,
      specialize h U,
      simp at h,
      simp,
      rw h,
    },
  },
  {
    intro h,
    cases h with hbijim h,
    cases h with himab hpreimab,
    intro U,
    simp [hinj, ← hpreimab],
  }
end


/-
## Ejercicios
-/

lemma ejer_2_1_3 (X : Type) [τ : espacio_topologico X] : τ = (discreta X) ↔ ∀ x : X, abierto ({x} : set X) :=
begin
  split,
  {
    intro hτ,
    intro x,
    simp,
    rw hτ,
    tauto,
  },
  {
    intro h,
    ext U,
    split,
    {
      intro h,
      tauto,
    },
    {
      have hU : U = ⋃₀ { ({x}) | x ∈ U},
      {
        ext x,
        simp,
      },
      intro hUab,
      rw hU,
      apply abierto_union,
      intros V hV,
      simp at hV,
      cases hV with x hx,
      cases hx with hxU hxV,
      rw ← hxV,
      apply h,
    },
  }
end


end topologicos
