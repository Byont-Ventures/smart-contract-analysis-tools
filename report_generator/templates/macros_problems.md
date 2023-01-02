{% macro input(problem) %}

**SWC ID:** {{ problem.swcId }}

**Severity:** `{{ problem.severity }}`

**Rarity:** `{{ problem.rarity }}`

**Line numbers of interest:** {{ problem.lineNumbersOfInterest }}

**Transaction flow:** {{ problem.transactionFlow }}

**Developer notes:** {{ problem.notes }}

{% endmacro input %}