# github-core-forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/yuusuke06/github-core-forge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/yuusuke06/github-core-forge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A GitHub-compatible git forge in a single TypeScript file (`main.ts`), built for Node 22 with no dependencies and no git binary. It serves git smart HTTP (protocol v0 and v2: ls-refs, fetch with shallow/deepen, fast-forward-only receive-pack with side-band report-status), the REST v3 API (repos, branches, commits, contents backed by real git trees, labels, issues, pull requests with squash merge), a GraphQL API with introspection, and an MCP endpoint (tools for repos, issues and pull requests) — all over one in-memory, content-addressed object store shared across repositories, with a deterministic state clock so repeated runs export byte-identical state.

## Run it

```sh
node --experimental-strip-types main.ts
```

---

<sub>Entered on [make.fun](https://make.fun/?ref=jcnyznqs&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
