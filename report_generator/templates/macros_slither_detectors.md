{% macro input(detector) %}
## {{ detector.name }}

* **Impact:** `{{ detector.impact }}`
* **Confidence:** `{{ detector.confidence }}`

### In Function

{{ detector.function }}

### Lines of Relevance

{% for line in detector.linesOfRelevance %}

{{ line }}

{% endfor %}

{% endmacro input %}