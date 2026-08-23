# Support Hunt #80: Fulcrum Tools Inventory

## Question
Which tools named `fulcrum_*` are available in this session?

## Finding
17 tools are available, accessed through the MCP (Model Context Protocol) as `mcp__fulcrum__fulcrum_*`:

| Tool | Description |
|------|-------------|
| fulcrum_adopt | Record an already-running external job against a roster row |
| fulcrum_capabilities | Query worker backend capabilities (messaging, polling, inbound calls) |
| fulcrum_collect | Finalize a run and ingest its completed artifacts into ledger |
| fulcrum_cost | Query what a run cost or the whole lab's costs |
| fulcrum_inspect | Retrieve one run in full by run_id |
| fulcrum_intervene | Deliver a correction to a live worker with ledger recording |
| fulcrum_land | Put a collected run's files on the pursuit main branch |
| fulcrum_launch | Launch a run from a roster row |
| fulcrum_map | Retrieve the dependency map as a ranked graph of the roster |
| fulcrum_observe | Append observations to an adopted external job or record its outcome |
| fulcrum_outbox | Query messages queued for live runs not yet sent |
| fulcrum_roster | Derive and refresh the work queue from the target lab repo |
| fulcrum_status | Query Fulcrum's full state: all runs, conclusions, live runs, threads |
| fulcrum_supersede | Record that later evidence overturned a run's conclusion |
| fulcrum_support | Ask for an independent support run on a bounded question |
| fulcrum_support_wait | Poll for completion of a support run |
| fulcrum_verify | Run control suite and state invariants; read or write the watermark |

## Total Count
**17 tools**

## Method
Listed via deferred tool schemas loaded with ToolSearch. No tools were invoked.
