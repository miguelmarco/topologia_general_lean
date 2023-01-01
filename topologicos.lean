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

class espacio_topologico (X : Type) :=
( abiertos : set (set X))
( abierto_total : (univ : set X) ∈ abiertos)
( abierto_vacio : ∅ ∈ abiertos)
( abierto_union : ∀ F : set (set X), (F ⊆ abiertos → ⋃₀ F ∈ abiertos ) )
( abierto_interseccion :   ∀ F : set (set X), (F ⊆ abiertos → F.finite →  ⋂₀ F ∈ abiertos ))


open espacio_topologico -- así podemos  escribir `abiertos` en lugar de `espacio_topologico.abiertos`


-- por comodidad, definimos la propiedad de ser abierto como pertenecer al conjunto de abiertos
-- (internamente, Lean los trata igual)
def abierto {X : Type} [espacio_topologico X] (U : set X) := U ∈ (abiertos  : set (set X))


-- y demostrar este lema trivial permite al simplificador aplicar la equivalencia automáticamente
@[simp]
lemma abierto_def  {X : Type} [espacio_topologico X] (U : set X) : abierto U ↔ U ∈ (abiertos : set (set X)) :=
begin
  refl,
end


lemma interseccion_2_eq {X : Type}  ( U V : set X) : U ∩ V = ⋂₀ {U,V} :=
begin
  simp only [set.sInter_insert, set.sInter_singleton],
end



lemma abierto_interseccion_2 {X : Type} [espacio_topologico X]  (U V : set X) (hU : abierto U)  (hV : abierto V) :
abierto (U ∩ V) :=
begin
  rw interseccion_2_eq,
  apply abierto_interseccion,
  {
    intros x hx,
    cases hx,
    {
      rw hx, exact hU,
    },
    {
      cases hx, assumption,
    },
  },
  simp,
end



def cerrado {X : Type} [espacio_topologico X] (C : set X) := abierto Cᶜ 
def cerrados {X : Type} [espacio_topologico X] : set (set X):= cerrado 

@[simp]
lemma cerrado_def {X : Type} [espacio_topologico X] (C : set X) : cerrado C ↔ abierto Cᶜ :=
begin
  refl,
end

@[simp]
lemma cerrados_def {X : Type} [espacio_topologico X] (C : set X) : C ∈ (cerrados : set (set X)) ↔ abierto Cᶜ :=
begin
  refl,
end

lemma cerrado_univ {X : Type} [espacio_topologico X] : cerrado (univ : set X) :=
begin
  simp only [cerrado,set.compl_univ],
  exact abierto_vacio,
end

lemma cerrado_vacio {X : Type} [espacio_topologico X] : cerrado (∅  : set X) :=
begin
  simp only [cerrado,set.compl_empty],
  exact abierto_total,
end

lemma cerrado_inter {X : Type} [espacio_topologico X] (F : set (set X)) (hf : F ⊆ cerrados) :
cerrado ⋂₀ F :=
begin
  simp only [topologicos.cerrado.equations._eqn_1],
  have haux : (⋂₀ F)ᶜ = ⋃₀ (compl '' F),
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
  simp at hf,
  rw hV2 at hf,
  exact hf,
end

lemma cerrado_union {X : Type} [espacio_topologico X] (C D : set X) : cerrado C → cerrado D → cerrado (C ∪ D ) :=
begin
  simp only [cerrado_def,compl_union, abierto_def],
  intros,
  apply abierto_interseccion_2,
  assumption,
  assumption,
end



def topologia_metrico {X : Type} [metricos.espacio_metrico X] : espacio_topologico X :=
{ abiertos := {U : set X | ∀ x ∈ U, metricos.entorno x U},
  abierto_total := 
  begin
    intros x h,
    use 1,
    simp only [set.subset_univ, gt_iff_lt, and_self, zero_lt_one],
  end,
  abierto_vacio := 
  begin
    intros x h,
    cases h,
  end,
  abierto_union := 
  begin
    intros F hF x hx,
    cases hx with U hU,
    cases hU with hUF hxU,
    specialize hF hUF x hxU,
    cases hF with r hr,
    cases hr with hrpos hrx,
    use r,
    split, assumption,
    intros y hy,
    use U,
    split, assumption,
    apply hrx hy,
  end,
  abierto_interseccion := 
  begin
    intros F hF hFin x hx,
    revert hF,
    revert hx,
    apply set.finite.induction_on hFin,
    {
      simp,
      use 1,
      simp,
    },
    {
      intros V C hV hCf hCen hxv hind,
      simp only [set.sInter_insert],
      have hVen : metricos.entorno x V,
      {
        apply hind, simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
        simp only [set.sInter_insert, set.mem_sInter, set.mem_inter_iff] at hxv,
        tauto,
      },
      have hInen : metricos.entorno x ⋂₀ C,
      {
        simp only [set.sInter_insert, set.mem_inter_iff] at hxv,
        specialize hCen hxv.2,
        apply hCen,
        intros A hA,
        apply hind,
        right,assumption,
      },
      cases hVen with r1 hr1,
      cases hr1 with hr1pos hr1,
      cases hInen with r2 hr2,
      cases hr2 with hr2pos hr2,
      use min r1 r2,
      split,
      {
        simp only [gt_iff_lt, lt_min_iff], tauto,
      },
      {
        simp only [set.subset_inter_iff],
        split,
        {
          intros y hy,
          apply hr1,
          simp only [set.sInter_insert,
 set.mem_sInter,
 gt_iff_lt,
 set.subset_sInter_iff,
 set.mem_set_of_eq,
 set.mem_inter_iff,
 metricos.bola.equations._eqn_1] at *,
          simp only [lt_min_iff] at hy,
          linarith,
        },
        {
          intros z hz,
          apply hr2,
          unfold metricos.bola at *,
          simp at *,
          exact hz.2,
        },
      },

    },
  end }


/-
Ahora podemos definir topologías concretas
-/

def discreta (X : Type) : espacio_topologico X :=
{ abiertos := univ,
  abierto_total := by triv,
  abierto_vacio := by triv,
  abierto_union := 
  begin
    intros,
    triv,
  end,
  abierto_interseccion := 
  begin
    intros,
    triv,
  end
}

def indiscreta (X : Type) : espacio_topologico X :=
{ abiertos := {x : set X | x = ∅  ∨ x = univ},
  abierto_total := 
  begin
    right, 
    refl
  end,
  abierto_vacio := 
  begin
    left,
    refl,
  end,
  abierto_union := 
  begin
    intros F  h,
    by_cases hF : univ ∈ F,
    {
      right,
      ext,
      simp only [set.mem_univ, set.mem_sUnion, iff_true],
      use univ,
      tauto,
    },
    {
      left,
      ext,
      simp only [not_exists, set.mem_empty_iff_false, set.mem_sUnion, iff_false],
      intros U hU hx,
      specialize h hU,
      cases h,
      {
        rw h at hx,
        exact hx,
      },
      {
        rw h at hU,
        apply hF hU,
      }
    }
  end,
  abierto_interseccion := 
  begin
    intros F hF hFfin,
    by_cases hem: ∅ ∈ F,
    {
      left,
      rw sInter_eq_empty_iff,
      intro x,
      use ∅,
      tauto,
    },
    {
      right,
      rw sInter_eq_univ,
      intros U hU,
      specialize hF hU,
      cases hF,
      {
        rw ← hF at hem,
        tauto,
      },
      {
        assumption,
      },
    }
  end
}

def cofinita (X : Type) : espacio_topologico X :=
{ abiertos := {U : set X | set.finite Uᶜ } ∪ {∅},
  abierto_total := 
  begin
    left,
    simp only [set.compl_univ, set.finite_empty, set.mem_set_of_eq],
  end,
  abierto_vacio := 
  begin
    right,
    tauto,
  end,
  abierto_union := 
  begin
    intros F hF,
    by_cases h : F ⊆ {∅ },
    {
      right,
      dsimp,
      rw sUnion_eq_empty,
      intros U hU,
      apply h,
      exact hU,
    },
    {
      simp only [set.subset_singleton_iff, not_forall] at h,
      cases h with U hU,
      cases hU with hU hU1,
      left,
      refine finite.subset _ _,
      {
        use Uᶜ,
      },
      {
        specialize hF hU,
        cases hF,
        {
          exact hF,
        },
        {
          specialize hU1 hF,
          tauto,
        },
      },
      {
        simp only [set.compl_subset_compl],
        exact subset_sUnion_of_mem hU,
      }
    }
  end,
  abierto_interseccion := 
  begin
    intros F hF hFfin,
    revert hF,
    apply finite.induction_on hFfin,
    {
      simp,
    },
    {
      intros U S hUs hSfin hS hin,
      specialize hS _,
      {
        refine subset_trans _ hin,
        apply subset_insert,
      },
      dsimp at *,
      by_cases hUcompl : U = ∅,
      {
        right,
        rw hUcompl,
        simp only [set.sInter_insert, eq_self_iff_true, set.empty_inter],
      },
      cases hS,
      {
        left,
        refine finite.subset _ _,  exact Uᶜ ∪ (⋂₀ S)ᶜ,
        {
          rw finite_union,
          split,
          {
            specialize hin _, exact U,
            {
              apply mem_insert,
            },
            cases hin,
            {
              exact hin,
            },
            tauto,
          },
          exact hS,
        },
        simp only [set.sInter_insert, compl_inter],
      },
      right,
      simp [hS],
    },
  end }

variables (X : Type) [ espacio_topologico X]



def continua {X Y : Type} [τX : espacio_topologico X] [τY : espacio_topologico Y] (f : X → Y) :=
∀ U : set Y,  U ∈ τY.abiertos → (f ⁻¹' U) ∈ τX.abiertos

example (X Y : Type) [espacio_topologico Y] (f : X → Y) : @continua _ _  (discreta X) _ f:=
begin
  tauto,
end

example (X Y : Type) [espacio_topologico X] (f : X → Y) : @continua _ _ _ (indiscreta Y) f:=
begin
  intros U hU,
  cases hU,
  {
    rw hU,
    apply abierto_vacio,
  },
  {
    rw hU,
    exact abierto_total,
  }
end


lemma composicion_continuas {X Y Z : Type} [espacio_topologico X] [espacio_topologico Y] [espacio_topologico Z]
(f : X → Y) (g : Y → Z) : continua f → continua g → continua (g ∘ f) :=
begin
  intro hf,
  intro hg,
  intro W,
  intro hW,
  specialize hg  W hW,
  specialize hf _ hg,
  exact hf,
end

lemma identidad_continua {X : Type} [espacio_topologico X] : continua (identidad : X → X) :=
begin
  intro U,
  intro hU,
  exact hU,
end

def homeomorfismo {X Y  : Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y) :=
continua f ∧ ∃ g : Y → X, continua g ∧ inversas f g

lemma identidad_homeo {X : Type} [espacio_topologico X]: homeomorfismo (identidad : X → X) :=
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

lemma inversa_homeo_es_homeo 
{X Y  : Type} 
[espacio_topologico X] 
[espacio_topologico Y]
(f : X → Y) (hom : homeomorfismo f) 
(g : Y → X) (hfg : inversas f g)
:
homeomorfismo g :=
begin
  split,
  {
    cases hom with hf hg',
    cases hg' with g' hg',
    have geqg' := inversa_unica f g g' hfg hg'.2,
    rw geqg',
    tauto,
  },
  use f,
  cases hom,
  rw inversas_sii,
  tauto,
end


end topologicos