# Report generator

## Intermediate output

All tools used during the analysis have their own output format. The reasons for an intermediate data structure are:

- Abstracting away the used tools.
  - The user only wants to know what the problems on the contract are and isn't concerned with which tool found id.
- Analyzing and combining the output of multiple tools can give a a better picture of the problems found.

The following structure will be filled on each run.

```json
{
  "repository_link": "",
  "commit": "",
  "tools_versions": [
    {
      "name": "",
      "version": ""
    }
  ],
  "runtime_seconds": 0,
  "bytecode": {
    "size_bytes": 0,
    "bytecode_string": ""
  },
  "found_swc": [
    {
      "id": "",
      "count": 0
    }
  ],
  "source_mapping": [
    {
      "swc": "",
      "severity": "",
      "source_file": "",
      "lines_of_interest": [],
      "tx_flow": [
        {
          "target_address": "",
          "caller_address": "",
          "function": {
            "signature": "",
            "arguments": [],
            "value": ""
          },
          "extra": {
            "block_number": 0,
            "block_timestamp": 0,
            "block_gas_limit": 0,
            "gas_limit": 0,
            "gas_price": 0
          }
        }
      ]
    }
  ]
}
```

Example content can be found in [output-data-template.json](./output-data-template.json)

Only the necessary data is stored. This way a new report can be generated when we would for example the layout of a report.

## Template

The template engine takes a template with general text about our approach and defines what the report looks like. Depending on the target audience the report will go more or less in depth.

It will also add a description and possible solution (based on the [official docs](https://swcregistry.io/docs/SWC-129)) to the found problems for each found SWC problems.

One a report is generated, there is an option to add notes manually for more specific information with regard to the context in which the smart contract will run.
