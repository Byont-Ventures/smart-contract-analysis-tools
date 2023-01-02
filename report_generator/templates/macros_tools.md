{% import "macros_slither_detectors.md" as macros_detectors %}

{% macro input(tool) %}

## {{ tool.name }}

**Total number of issues:** {{ tool.nrOfIssues }}

**Version of the tool:** {{ tool.version }}

{% if tool.hasDetectors %}
{% for detector in tool.detectors %}

{{ macros_detectors::input(detector=detector) }}

{% endfor %}
{% endif %}

{% endmacro input %}