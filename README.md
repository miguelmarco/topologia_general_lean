# Topología general el Lean3

Este repositorio contiene material complementario para un curso de topología general. En particular, es el curso del segundo año del grado de Matemáticas
en la universidad de Zaragoza, durante el año académico 2023/2024. Este material consiste en archivos de Lean
que formalizan (la mayor parte de) las definiciones y resultados que se dan en el curso, y algunos ejercicios que se hacen semanalmente.

## Estructura.

Por cada tema del curso hay dos archivos: uno con el título del tema, que incluye el contenido del tema y algunos ejercicios que se dejan propuestos
(resueltos con `sorry`); y otro con las soluciones a dichos ejercicios.

Hay un archivo que sirve de ["chuleta"](resumen_tacticas.lean) con algunas tácticas y símbolos.

Inicialmente hay algunos temas preliminares, que sirven como repaso de la teoría básica de conjuntos, y como introducción a Lean. Estos temas son:

- [proposiciones](proposiciones.lean)
- [conjuntos](conjuntos.lean)
- [aplicaciones](funciones.lean)

También hay un [archivo auxiliar](subconjuntos.lean) que proporciona una notación útil para trabajar con subespacios, así como algunos lemas de simplificación. Este archivo sólo
se usa para importarse posteriormente.

Luego están los temas de topología propiamente dicha:

- [espacios métricos](metricos.lean)
- [espacios topológicos](topologicos.lean)
- [bases y subbases](bases.lean)
- [cerrados](cerrados.lean)
- [subespacios](subespacios.lean)
- [aplicaciones abiertas y cerradas](aplicaciones_abiertas.lean)
- [entornos](entornos.lean)
- [clausura e interior](clausura.lean)

