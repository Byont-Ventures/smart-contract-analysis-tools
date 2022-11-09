{% import "macros_tools.md" as macros_tools %}
{% import "macros_problems.md" as macros_problems %}

# Code report

**Repository link:** {{ data.repositoryLink }}

**Commit number:** {{ data.commit }}

**Relative path to contract in the repository being verified:** {{ data.contractPath }}

**Solidity Version:** {{ data.solcVersion }}

**Foundry Version:** {{ data.foundryVersion }}

**Compiled Code Size:** {{ data.compiledCodeSize }}

**Notes from the developers:** {{ data.notes }}

**Number of vulnerabilities found per SWC:** {{ data.vulnerabilitiesPerSWC }}

**Parameters per Tool:**

{% for tool in data.tools %}

{{ macros_tools::input(tool=tool) }}

{% endfor %}

**Encountered problems/issues:**

{% for problem in data.problems %}

{{ macros_problems::input(problem=problem) }}

{% endfor %}
