# Topología general el Lean3

Este repositorio contiene material complementario para un curso de topología general. En particular, es el curso del segundo año del grado de Matemáticas
en la universidad de Zaragoza, durante el año académico 2023/2024. Este material consiste en archivos de Lean
que formalizan (la mayor parte de) las definiciones y resultados que se dan en el curso, y algunos ejercicios que se hacen semanalmente.

## Estructura.

En algunos temas del curso hay dos archivos: uno con el título del tema, que incluye el contenido del tema y algunos ejercicios que se dejan propuestos
(resueltos con `sorry`); y otro con las soluciones a dichos ejercicios.

Hay un archivo que sirve de ["chuleta"](resumen_tacticas.lean) con algunas tácticas y símbolos.

En el directorio `ejercicios` hay algunos de los ejercicios semanales. En un archivo vienen sólo los enunciados, y en el correspondiente
archivo de soluciones, están resueltos.

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
- [clausura](clausura.lean) e [interior](interior.lean)
- [sucesiones](sucesiones.lean)

## Agradecimientos

Este repositorio se realiza gracias al apoyo institucional de la Convocatoria
competitiva de Proyectos de Innovación de la Universidad de Zaragoza
(PI_DTOST) en el año 2023 y con referencia ID 4934 con título "Uso de asistentes
de demostración en la enseñanza de las matemáticas ".
