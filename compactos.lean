import .topologicos
import .cerrados

import tactic

open topologicos
open set 

def cubrimiento {X : Type} (F : set (set X)) (S : set X) := S ⊆  ⋃₀ F  

lemma cubriminento_monotono {X : Type}  (A B :  set X) (F : set (set X)) (hF : cubrimiento F B) (hAB: A ⊆ B ) :
cubrimiento F A :=
begin
  exact subset.trans hAB hF,
end

def cubrimiento_abierto {X : Type} [espacio_topologico X] (F : set (set X)) (S : set X):=
cubrimiento F S ∧ F ⊆ abierto 

def compacto {X : Type} [espacio_topologico X] (S : set X) :=
∀ F : set ( set X), cubrimiento_abierto F S →  ∃ C : (set (set X)), C ⊆ F ∧
set.finite C ∧ cubrimiento C S

def espacio_compacto {X : Type} [espacio_topologico X] := compacto ( univ : set  X)

lemma completar_cubrimiento {X : Type} (S : set X) (F : set (set X)) (h : cubrimiento F S) :
cubrimiento (insert  SᶜF ) univ :=
begin
  intros x hx,
  by_cases hS : x ∈ S,
  {
    specialize h hS,
    cases h with U hU,
    use U,
    split,
    {
      right,
      cases hU, assumption,
    },
    {
      cases hU, assumption,
    },
  },
  {
    use Sᶜ,
    split,
    {
      left, refl,
    },
    {
      exact hS,
    }
  },
end

lemma completar_cubrimiento_abierto {X : Type} [espacio_topologico X] (S : set X) (F : set (set X))
(hF : cubrimiento_abierto F S) (hScer : cerrado S) : cubrimiento_abierto (insert Sᶜ F) univ :=
begin
  split,
  {
    apply completar_cubrimiento,
    cases hF,
    assumption,
  },
  {
    intros U hU,
    cases hU,
    {
      rw hU,
      exact hScer,
    },
    {
      cases hF with hFcubr hFab,
      apply hFab,
      exact hU,
    }
  }
end

lemma cerrados_en_compactos {X : Type} [espacio_topologico X] (K C : set X) : compacto K → cerrado C → C ⊆ K → compacto C :=
begin
  intros hcompK hcerC hCsubK,
  intros F hF,
  let F' := insert Cᶜ F,
  specialize hcompK F',
  have hcubrK : cubrimiento_abierto F' K,
  {
    let hcubruniv := completar_cubrimiento_abierto C F hF hcerC,
    split,
    {
      apply cubriminento_monotono _ univ,
      apply completar_cubrimiento,
      exact hF.1,
      apply subset_univ,
    },
    {
      intros U hU,
      cases hU,
      {
        rw hU,
        exact hcerC,
      },
      {
        apply hF.2 hU,
      },
    },
  },
  {
    specialize hcompK hcubrK,
    cases hcompK with S hS,
    cases hS with hSf' hS2,
    cases hS2 with hSfin hScubr,
    use S ∩ F,
    split,
    {
      simp,
    },
    split,
    {
      exact finite.inter_of_left hSfin F,  -- demostrar que subconjunto de finito es finito,
    },
    {
      intros x hX,
      specialize hCsubK hX,
      specialize hScubr hCsubK,
      cases hScubr with U hU,
      cases hU with hUS hUx,
      use U,
      split,
      {
        split,
        {
          exact hUS,
        },
        {
          specialize hSf' hUS,
          cases hSf',
          {
            rw hSf' at hUx,
            by_contradiction,
            apply hUx,
            exact hX,
          },
          {
            exact hSf',
          },
        },
      },
      exact hUx,
    },
  },
end