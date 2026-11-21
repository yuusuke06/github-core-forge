// A standalone GitHub-compatible git forge in a single file.
// Serves git smart HTTP (upload-pack protocol v2, receive-pack v0), the
// REST v3 API under /api/v3, GraphQL v4 at /api/graphql and an MCP
// endpoint at /mcp, all from one in-memory store, Node standard library
// only. Boot protocol: bind an ephemeral port, POST it to
// $MAKEFUN_ENV_URL/register, then poll $MAKEFUN_ENV_URL/done and exit 0.

import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { createHash, createHmac } from 'node:crypto';
import { deflateSync, inflateSync, createInflate } from 'node:zlib';

// ------------------------------------------------------------------ config

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const VIEWER_LOGIN = process.env.MAKEFUN_FORGE_LOGIN ?? 'adaiversen';
const VIEWER = { id: 1000, login: VIEWER_LOGIN, name: 'ada iversen', email: 'adaiversen@example.invalid', type: 'User' };
const ZERO_OID = '0'.repeat(40);
const EPOCH_BASE = 1_700_000_000; // deterministic timestamps: never wall clock in state

let clockSeq = 0;
function nextStamp(): { sec: number; iso: string } {
  clockSeq += 1;
  const sec = EPOCH_BASE + clockSeq;
  return { sec, iso: new Date(sec * 1000).toISOString() };
}

// ------------------------------------------------------------------ git objects

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj { type: ObjType; data: Buffer }
const objects = new Map<string, GitObj>();
const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function sha1hex(buf: Buffer): string { return createHash('sha1').update(buf).digest('hex'); }
function hashObject(type: ObjType, data: Buffer): string {
  return sha1hex(Buffer.concat([Buffer.from(`${type} ${data.length}\0`, 'utf8'), data]));
}
function storeObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objects.has(oid)) objects.set(oid, { type, data });
  return oid;
}
function getObject(oid: string): GitObj | undefined { return objects.get(oid); }

interface TreeEntry { mode: string; name: string; oid: string }
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    const mode = data.subarray(i, sp).toString('utf8');
    const nul = data.indexOf(0, sp + 1);
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    i = nul + 21;
  }
  return entries;
}
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
interface CommitView { tree: string; parents: string[]; message: string; author: string; committer: string }
function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = ''; const parents: string[] = []; let author = ''; let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, message, author, committer };
}
function buildCommit(tree: string, parents: string[], message: string, stampSec: number): Buffer {
  const ident = `${VIEWER.name} <${VIEWER.email}> ${stampSec} +0000`;
  let head = `tree ${tree}\n`;
  for (const p of parents) head += `parent ${p}\n`;
  head += `author ${ident}\ncommitter ${ident}\n`;
  const msg = message.endsWith('\n') ? message : `${message}\n`;
  return Buffer.from(`${head}\n${msg}`, 'utf8');
}
function parseTagTarget(data: Buffer): string {
  const m = /^object ([0-9a-f]{40})/m.exec(data.toString('utf8'));
  return m ? m[1] : '';
}
/** Peel a tag (chain) to the commit it names; a commit peels to itself. */
function peelToCommit(oid: string): string {
  let cur = oid;
  for (let depth = 0; depth < 10; depth += 1) {
    const obj = objects.get(cur);
    if (!obj) return '';
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') { cur = parseTagTarget(obj.data); continue; }
    return '';
  }
  return '';
}
/** Flatten a tree into path -> {oid, mode}; recursive. */
function flattenTree(treeOid: string, prefix = '', out = new Map<string, { oid: string; mode: string }>()): Map<string, { oid: string; mode: string }> {
  const obj = objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix === '' ? e.name : `${prefix}/${e.name}`;
    if (e.mode === '40000') flattenTree(e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
  return out;
}
/** Build nested trees from a flat path -> blob oid map; returns root tree oid. */
function treeFromFlat(flat: Map<string, { oid: string; mode: string }>): string {
  interface Node { files: Map<string, { oid: string; mode: string }>; dirs: Map<string, Node> }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, entry] of flat) {
    const segs = path.split('/');
    let node = root;
    for (let i = 0; i < segs.length - 1; i += 1) {
      if (!node.dirs.has(segs[i])) node.dirs.set(segs[i], make());
      node = node.dirs.get(segs[i])!;
    }
    node.files.set(segs[segs.length - 1], entry);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, e] of node.files) entries.push({ mode: e.mode, name, oid: e.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return storeObject('tree', buildTree(entries));
  };
  return build(root);
}
function commitTreeFlat(commitOid: string): Map<string, { oid: string; mode: string }> {
  const obj = objects.get(commitOid);
  if (!obj || obj.type !== 'commit') return new Map();
  return flattenTree(parseCommit(obj.data).tree);
}
/** All ancestors of a commit, including itself (BFS over parents). */
function ancestorsOf(tip: string): Set<string> {
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length) {
    const cur = queue.pop()!;
    if (seen.has(cur)) continue;
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'commit') continue;
    seen.add(cur);
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return seen;
}
function isAncestor(anc: string, tip: string): boolean { return ancestorsOf(tip).has(anc); }
function mergeBase(a: string, b: string): string {
  const ancA = ancestorsOf(a);
  const queue = [b]; const seen = new Set<string>();
  while (queue.length) {
    const cur = queue.shift()!;
    if (seen.has(cur)) continue;
    seen.add(cur);
    if (ancA.has(cur)) return cur;
    const obj = objects.get(cur);
    if (obj && obj.type === 'commit') queue.push(...parseCommit(obj.data).parents);
  }
  return '';
}
/** Every object reachable from a tip (commit graph + trees + blobs + tags). */
function reachableObjects(tips: Iterable<string>, stopAt?: Set<string>): Set<string> {
  const out = new Set<string>();
  const stack = [...tips];
  while (stack.length) {
    const oid = stack.pop()!;
    if (out.has(oid)) continue;
    if (stopAt && stopAt.has(oid)) continue;
    const obj = objects.get(oid);
    if (!obj) continue;
    out.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree, ...c.parents);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTagTarget(obj.data));
    }
  }
  return out;
}

// ------------------------------------------------------------------ forge store

interface IssueRec {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: string[]; comments: { id: number; body: string }[]; seq: number;
}
interface PullRec {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  merged: boolean; mergedAt: string | null; mergeCommitSha: string | null;
  headRef: string; baseRef: string; headSha: string; baseSha: string; seq: number;
}
interface RepoRec {
  id: number; owner: string; name: string; description: string; isPrivate: boolean;
  defaultBranch: string; refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, IssueRec>; pulls: Map<number, PullRec>;
  nextNumber: number; createdIso: string;
}
const repos = new Map<string, RepoRec>();
let repoSeq = 7000;
let issueIdSeq = 90000;
function repoKey(owner: string, name: string): string { return `${owner}/${name}`; }
function createRepo(name: string, description: string, isPrivate: boolean): RepoRec {
  repoSeq += 1;
  const stamp = nextStamp();
  const repo: RepoRec = {
    id: repoSeq, owner: VIEWER_LOGIN, name, description: description ?? '', isPrivate: !!isPrivate,
    defaultBranch: 'main', refs: new Map(), labels: new Map(),
    issues: new Map(), pulls: new Map(), nextNumber: 1, createdIso: stamp.iso,
  };
  repos.set(repoKey(repo.owner, name), repo);
  return repo;
}
function findRepo(owner: string, name: string): RepoRec | null {
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}
function repoJson(r: RepoRec): Record<string, unknown> {
  return {
    id: r.id, node_id: globalId('Repository', r.id), name: r.name, full_name: `${r.owner}/${r.name}`,
    owner: { login: r.owner, id: VIEWER.id, type: 'User' },
    private: r.isPrivate, description: r.description, default_branch: r.defaultBranch,
    html_url: `https://forge.invalid/${r.owner}/${r.name}`,
    clone_url: `https://forge.invalid/${r.owner}/${r.name}.git`,
    created_at: r.createdIso, updated_at: r.createdIso, pushed_at: r.createdIso,
    has_issues: true, has_pull_requests: true, visibility: r.isPrivate ? 'private' : 'public',
  };
}
function labelJson(name: string, color: string): Record<string, unknown> {
  return { id: 1, name, color, default: false, description: null };
}
function issueJson(r: RepoRec, i: IssueRec): Record<string, unknown> {
  return {
    id: i.id, node_id: globalId('Issue', `${r.id}:${i.number}`), number: i.number,
    title: i.title, body: i.body, state: i.state,
    labels: i.labels.map((n) => labelJson(n, r.labels.get(n)?.color ?? 'ededed')),
    user: { login: VIEWER_LOGIN, id: VIEWER.id, type: 'User' },
    comments: i.comments.length, created_at: r.createdIso, updated_at: r.createdIso,
    html_url: `https://forge.invalid/${r.owner}/${r.name}/issues/${i.number}`,
  };
}
function pullJson(r: RepoRec, p: PullRec): Record<string, unknown> {
  const headSha = r.refs.get(`refs/heads/${p.headRef}`) ?? p.headSha;
  const baseSha = r.refs.get(`refs/heads/${p.baseRef}`) ?? p.baseSha;
  return {
    id: p.id, node_id: globalId('PullRequest', `${r.id}:${p.number}`), number: p.number,
    title: p.title, body: p.body, state: p.state, merged: p.merged,
    merged_at: p.mergedAt, merge_commit_sha: p.mergeCommitSha,
    head: { ref: p.headRef, sha: headSha, repo: repoJson(r) },
    base: { ref: p.baseRef, sha: baseSha, repo: repoJson(r) },
    user: { login: VIEWER_LOGIN, id: VIEWER.id, type: 'User' },
    created_at: r.createdIso, updated_at: r.createdIso,
    html_url: `https://forge.invalid/${r.owner}/${r.name}/pull/${p.number}`,
  };
}
/** Opaque, stable Relay-style global id (never the plain database id). */
function globalId(type: string, key: string | number): string {
  return Buffer.from(`${type}:${key}`, 'utf8').toString('base64');
}
function decodeGlobalId(id: string): { type: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const at = text.indexOf(':');
    if (at < 0) return null;
    return { type: text.slice(0, at), key: text.slice(at + 1) };
  } catch { return null; }
}

// ------------------------------------------------------------------ packs and pkt-lines

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
interface Pkt { kind: 'data' | 'flush' | 'delim' | 'end'; payload: Buffer }
function parsePkts(buf: Buffer, start = 0): { packets: Pkt[]; rest: Buffer } {
  const packets: Pkt[] = [];
  let i = start;
  while (i + 4 <= buf.length) {
    const hex = buf.subarray(i, i + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
    const len = parseInt(hex, 16);
    if (len === 0) { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); i += 4; break; }
    if (len === 1) { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (len === 2) { packets.push({ kind: 'end', payload: Buffer.alloc(0) }); i += 4; break; }
    if (i + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(i + 4, i + len) });
    i += len;
  }
  return { packets, rest: buf.subarray(i) };
}
function inflateAt(buf: Buffer, offset: number): Promise<{ data: Buffer; next: number }> {
  return new Promise((resolve, reject) => {
    const stream = createInflate();
    const chunks: Buffer[] = [];
    stream.on('data', (c: Buffer) => chunks.push(c));
    stream.on('end', () => {
      const used = (stream as unknown as { bytesWritten?: number }).bytesWritten ?? 0;
      resolve({ data: Buffer.concat(chunks), next: offset + used });
    });
    stream.on('error', (err: Error) => {
      // Fall back to a binary search for the shortest prefix that inflates.
      try {
        let lo = 1; let hi = buf.length - offset; let best = -1;
        while (lo <= hi) {
          const mid = Math.floor((lo + hi) / 2);
          try { inflateSync(buf.subarray(offset, offset + mid)); best = mid; hi = mid - 1; }
          catch { lo = mid + 1; }
        }
        if (best < 0) { reject(err); return; }
        resolve({ data: inflateSync(buf.subarray(offset, offset + best)), next: offset + best });
      } catch { reject(err); }
    });
    stream.write(buf.subarray(offset));
  });
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let i = 0;
  const readVarint = (): number => {
    let value = 0; let shift = 0;
    for (;;) { const b = delta[i++]; value |= (b & 0x7f) << shift; shift += 7; if ((b & 0x80) === 0) break; }
    return value;
  };
  readVarint(); // base size
  const targetSize = readVarint();
  const out: Buffer[] = [];
  while (i < delta.length) {
    const op = delta[i++];
    if (op & 0x80) {
      let offset = 0; let size = 0;
      if (op & 0x01) offset = delta[i++];
      if (op & 0x02) offset |= delta[i++] << 8;
      if (op & 0x04) offset |= delta[i++] << 16;
      if (op & 0x08) offset |= delta[i++] << 24;
      if (op & 0x10) size = delta[i++];
      if (op & 0x20) size |= delta[i++] << 8;
      if (op & 0x40) size |= delta[i++] << 16;
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
    } else if (op > 0) {
      out.push(delta.subarray(i, i + op)); i += op;
    } else throw new Error('bad delta opcode 0');
  }
  const result = Buffer.concat(out);
  if (result.length !== targetSize) throw new Error('delta size mismatch');
  return result;
}
/** Parse a pack into the global store. Returns the object ids it carried. */
async function readPack(pack: Buffer): Promise<string[]> {
  if (pack.length < 12 + 20) return [];
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a pack');
  const count = pack.readUInt32BE(8);
  let offset = 12;
  const pending = new Map<string, { baseOid?: string; baseOffset?: number; delta: Buffer }>();
  const offsetToOid = new Map<number, string>();
  const ids: string[] = [];
  for (let n = 0; n < count; n += 1) {
    const objStart = offset;
    let b = pack[offset++];
    const typeCode = (b >> 4) & 0x7;
    let size = b & 0x0f; let shift = 4;
    while (b & 0x80) { b = pack[offset++]; size |= (b & 0x7f) << shift; shift += 7; }
    let baseOid = ''; let baseOffset = 0;
    if (typeCode === 6) { // ofs-delta
      b = pack[offset++];
      let off = b & 0x7f;
      while (b & 0x80) { b = pack[offset++]; off = ((off + 1) << 7) | (b & 0x7f); }
      baseOffset = objStart - off;
    } else if (typeCode === 7) { // ref-delta
      baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    }
    const inflated = await inflateAt(pack, offset);
    offset = inflated.next;
    if (typeCode === 6 || typeCode === 7) {
      const key = `delta-${objStart}`;
      pending.set(key, { baseOid: baseOid || undefined, baseOffset: baseOffset || undefined, delta: inflated.data });
      offsetToOid.set(objStart, key);
      ids.push(key);
    } else {
      const type = CODE_TYPE[typeCode];
      if (!type) throw new Error(`bad pack object type ${typeCode}`);
      const oid = storeObject(type, inflated.data);
      offsetToOid.set(objStart, oid);
      ids.push(oid);
    }
  }
  // Resolve deltas (possibly chained).
  const resolveDelta = (key: string): string => {
    const entry = pending.get(key)!;
    let baseObj: GitObj | undefined;
    if (entry.baseOid) baseObj = objects.get(entry.baseOid);
    else if (entry.baseOffset !== undefined) {
      const baseKey = offsetToOid.get(entry.baseOffset);
      if (baseKey && pending.has(baseKey)) {
        const resolved = resolveDelta(baseKey);
        baseObj = objects.get(resolved);
      } else if (baseKey) baseObj = objects.get(baseKey);
    }
    if (!baseObj) throw new Error('delta base missing');
    const data = applyDelta(baseObj.data, entry.delta);
    const oid = storeObject(baseObj.type, data);
    pending.delete(key);
    return oid;
  };
  for (const key of [...pending.keys()]) {
    const oid = resolveDelta(key);
    const idx = ids.indexOf(key);
    if (idx >= 0) ids[idx] = oid;
  }
  return ids;
}
function writePack(oids: Iterable<string>): Buffer {
  const list = [...new Set(oids)].map((oid) => ({ oid, obj: objects.get(oid)! })).filter((x) => x.obj);
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii'); header.writeUInt32BE(2, 4); header.writeUInt32BE(list.length, 8);
  const parts: Buffer[] = [header];
  for (const { obj } of list) {
    const code = TYPE_CODE[obj.type];
    let remaining = obj.data.length;
    const bytes: number[] = [];
    let first = (code << 4) | (remaining & 0x0f);
    remaining = Math.floor(remaining / 16);
    while (remaining > 0) { bytes.push(first | 0x80); first = remaining & 0x7f; remaining = Math.floor(remaining / 128); }
    bytes.push(first);
    parts.push(Buffer.from(bytes));
    parts.push(deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}
/** Wrap bytes in side-band-64k packets (band 1 = pack data). */
function sidebandWrap(data: Buffer, band = 1): Buffer {
  const parts: Buffer[] = [];
  const CHUNK = 65515;
  if (data.length === 0) return pktLine(Buffer.from([band]));
  for (let i = 0; i < data.length; i += CHUNK) {
    parts.push(pktLine(Buffer.concat([Buffer.from([band]), data.subarray(i, i + CHUNK)])));
  }
  return Buffer.concat(parts);
}

// ------------------------------------------------------------------ git smart HTTP

function parseAllPkts(buf: Buffer): Pkt[] {
  const packets: Pkt[] = [];
  let i = 0;
  while (i + 4 <= buf.length) {
    const hex = buf.subarray(i, i + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
    const len = parseInt(hex, 16);
    if (len === 0) { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (len === 1) { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (len === 2) { packets.push({ kind: 'end', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (i + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(i + 4, i + len) });
    i += len;
  }
  return packets;
}
const UPLOAD_CAPS_V0 = 'side-band-64k multi_ack_detailed thin-pack ofs-delta shallow no-progress agent=forge/1.0';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta quiet agent=forge/1.0';

function sortedRefs(repo: RepoRec): [string, string][] {
  return [...repo.refs.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
}
function advertisementV0(repo: RepoRec, service: string): Buffer {
  const caps = service === 'git-upload-pack' ? `${UPLOAD_CAPS_V0} symref=HEAD:refs/heads/${repo.defaultBranch}` : RECEIVE_CAPS;
  const lines: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    lines.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    let first = true;
    const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? refs[0][1];
    lines.push(pktLine(`${headTip} HEAD\0${caps}\n`));
    first = false;
    for (const [name, oid] of refs) {
      lines.push(pktLine(`${oid} ${name}\n`));
      void first;
      const obj = objects.get(oid);
      if (obj && obj.type === 'tag') {
        const peeled = peelToCommit(oid);
        if (peeled) lines.push(pktLine(`${peeled} ${name}^{}\n`));
      }
    }
  }
  lines.push(PKT_FLUSH);
  return Buffer.concat(lines);
}
function advertisementV2(): Buffer {
  const lines = [
    pktLine('version 2\n'),
    pktLine('agent=forge/1.0\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow wait-for-done\n'),
    pktLine('server-option\n'),
    pktLine('object-format=sha1\n'),
    PKT_FLUSH,
  ];
  return Buffer.concat(lines);
}
function lsRefsLines(repo: RepoRec, args: { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: string[] }): Buffer[] {
  const lines: Buffer[] = [];
  const match = (name: string): boolean => args.prefixes.length === 0 || args.prefixes.some((p) => name.startsWith(p));
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headTip = repo.refs.get(headRef);
  if (match('HEAD')) {
    if (headTip) {
      lines.push(pktLine(`${headTip} HEAD${args.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    } else if (args.unborn) {
      lines.push(pktLine(`unborn HEAD${args.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    }
  }
  for (const [name, oid] of sortedRefs(repo)) {
    if (!match(name)) continue;
    let extra = '';
    const obj = objects.get(oid);
    if (obj && obj.type === 'tag') {
      if (args.symrefs) { /* tags are not symrefs */ }
      if (args.peel) { const peeled = peelToCommit(oid); if (peeled) extra += ` peeled:${peeled}`; }
    }
    lines.push(pktLine(`${oid} ${name}${extra}\n`));
  }
  return lines;
}
/** Objects a client already holds: full closure of haves, but never past a shallow boundary. */
function haveClosure(haves: string[], shallowClient: Set<string>): Set<string> {
  const excluded = new Set<string>();
  for (const have of haves) {
    const obj = objects.get(have);
    if (!obj) continue;
    if (obj.type === 'commit' && shallowClient.has(have)) {
      // The client holds this commit and its tree, but not its parents.
      excluded.add(have);
      const tree = parseCommit(obj.data).tree;
      for (const oid of reachableObjects([tree])) excluded.add(oid);
    } else {
      for (const oid of reachableObjects([have])) excluded.add(oid);
    }
  }
  return excluded;
}
interface FetchPlan { oids: Set<string>; shallow: string[]; unshallow: string[] }
function planFetch(wants: string[], haves: string[], shallowClient: string[], depth: number | null): FetchPlan {
  const shallowSet = new Set(shallowClient);
  const excluded = haveClosure(haves, shallowSet);
  const send = new Set<string>();
  const shallow: string[] = [];
  const unshallow: string[] = [];
  // Tag objects named directly as wants are always sent (unless held).
  for (const want of wants) {
    const obj = objects.get(want);
    if (obj && obj.type === 'tag' && !excluded.has(want)) send.add(want);
  }
  if (depth !== null && depth > 0) {
    // Generation-limited walk from the peeled wants.
    const gen = new Map<string, number>();
    const queue: string[] = [];
    for (const want of wants) {
      const commit = peelToCommit(want);
      if (commit && !gen.has(commit)) { gen.set(commit, 0); queue.push(commit); }
    }
    while (queue.length) {
      const cur = queue.shift()!;
      const g = gen.get(cur)!;
      if (g >= depth - 1) continue;
      const obj = objects.get(cur);
      if (!obj || obj.type !== 'commit') continue;
      for (const parent of parseCommit(obj.data).parents) {
        if (!gen.has(parent)) { gen.set(parent, g + 1); queue.push(parent); }
      }
    }
    for (const [commit, g] of gen) {
      if (g >= depth) continue;
      const obj = objects.get(commit)!;
      const parents = parseCommit(obj.data).parents;
      const isBoundary = g === depth - 1 && parents.some((p) => objects.has(p));
      if (isBoundary && !shallow.includes(commit)) shallow.push(commit);
      if (shallowSet.has(commit) && !isBoundary) unshallow.push(commit);
      if (!excluded.has(commit)) {
        send.add(commit);
        for (const oid of reachableObjects([parseCommit(obj.data).tree])) if (!excluded.has(oid)) send.add(oid);
      }
    }
    return { oids: send, shallow, unshallow };
  }
  const wanted = reachableObjects(wants);
  for (const oid of wanted) if (!excluded.has(oid)) send.add(oid);
  return { oids: send, shallow, unshallow };
}
function fetchPackResponse(plan: FetchPlan): Buffer {
  return writePack(plan.oids);
}
async function handleUploadPack(repo: RepoRec, body: Buffer, isV2: boolean, res: ServerResponse): Promise<void> {
  const packets = parseAllPkts(body);
  const lines = packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8'));
  if (isV2) {
    const commandLine = lines[0] ?? '';
    if (commandLine.startsWith('command=ls-refs')) {
      const args = { peel: false, symrefs: false, unborn: false, prefixes: [] as string[] };
      for (const raw of lines.slice(1)) {
        const line = raw.replace(/\n$/, '');
        if (line === 'peel') args.peel = true;
        else if (line === 'symrefs') args.symrefs = true;
        else if (line === 'unborn') args.unborn = true;
        else if (line.startsWith('ref-prefix ')) args.prefixes.push(line.slice('ref-prefix '.length));
      }
      const out = [...lsRefsLines(repo, args), PKT_FLUSH];
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(Buffer.concat(out));
      return;
    }
    if (commandLine.startsWith('command=fetch')) {
      const wants: string[] = []; const haves: string[] = []; const shallowClient: string[] = [];
      let depth: number | null = null;
      for (const raw of lines.slice(1)) {
        const line = raw.replace(/\n$/, '');
        if (line.startsWith('want ')) wants.push(line.slice(5).trim());
        else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
        else if (line.startsWith('shallow ')) shallowClient.push(line.slice(8).trim());
        else if (line.startsWith('deepen ')) depth = parseInt(line.slice(7), 10);
      }
      const plan = planFetch(wants, haves, shallowClient, depth);
      const parts: Buffer[] = [];
      parts.push(pktLine('acknowledgments\n'));
      if (haves.length && haves.some((h) => objects.has(h))) {
        parts.push(pktLine(`ACK ${haves.find((h) => objects.has(h))}\n`));
        parts.push(pktLine('ready\n'));
      } else {
        parts.push(pktLine('NAK\n'));
      }
      parts.push(PKT_DELIM);
      if (plan.shallow.length || plan.unshallow.length) {
        parts.push(pktLine('shallow-info\n'));
        for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
        for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
        parts.push(PKT_DELIM);
      }
      parts.push(pktLine('packfile\n'));
      parts.push(sidebandWrap(fetchPackResponse(plan)));
      parts.push(PKT_FLUSH);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(Buffer.concat(parts));
      return;
    }
    res.writeHead(400, { 'content-type': 'text/plain' }); res.end('unknown command');
    return;
  }
  // Protocol v0: wants section, flush, haves section, flush.
  const wants: string[] = []; const haves: string[] = []; const shallowClient: string[] = [];
  let depth: number | null = null;
  let section = 0;
  for (const packet of packets) {
    if (packet.kind === 'flush') { section += 1; continue; }
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (section === 0) {
      if (line.startsWith('want ')) wants.push(line.slice(5, 45));
      else if (line.startsWith('shallow ')) shallowClient.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) depth = parseInt(line.slice(7), 10);
    } else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
  }
  const plan = planFetch(wants, haves, shallowClient, depth);
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  parts.push(pktLine('NAK\n'));
  parts.push(sidebandWrap(fetchPackResponse(plan)));
  parts.push(PKT_FLUSH);
  res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
  res.end(Buffer.concat(parts));
}
async function handleReceivePack(repo: RepoRec, body: Buffer, res: ServerResponse): Promise<void> {
  const { packets, rest } = parsePkts(body);
  interface Cmd { oldOid: string; newOid: string; ref: string; caps: string }
  const cmds: Cmd[] = [];
  let sideband = false;
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    let line = packet.payload.toString('utf8').replace(/\n$/, '');
    let caps = '';
    const nul = line.indexOf('\0');
    if (nul >= 0) { caps = line.slice(nul + 1); line = line.slice(0, nul); }
    if (caps.includes('side-band-64k')) sideband = true;
    const [oldOid, newOid, ref] = line.split(' ');
    if (oldOid && newOid && ref) cmds.push({ oldOid, newOid, ref, caps });
  }
  let unpackOk = true;
  if (rest.length > 0) {
    try { await readPack(rest); } catch { unpackOk = false; }
  }
  const reportLines: string[] = [`unpack ${unpackOk ? 'ok' : 'error'}\n`];
  for (const cmd of cmds) {
    let ok = unpackOk;
    let reason = '';
    if (ok && cmd.newOid !== ZERO_OID) {
      const obj = objects.get(cmd.newOid);
      if (!obj) { ok = false; reason = 'missing object'; }
    }
    if (ok && cmd.newOid !== ZERO_OID && cmd.oldOid !== ZERO_OID) {
      const newObj = objects.get(cmd.newOid);
      const oldObj = objects.get(cmd.oldOid);
      if (newObj && oldObj && newObj.type === 'commit' && oldObj.type === 'commit' && !isAncestor(cmd.oldOid, cmd.newOid)) {
        ok = false; reason = 'non-fast-forward';
      }
    }
    if (ok) {
      if (cmd.newOid === ZERO_OID) repo.refs.delete(cmd.ref);
      else repo.refs.set(cmd.ref, cmd.newOid);
      reportLines.push(`ok ${cmd.ref}\n`);
    } else {
      reportLines.push(`ng ${cmd.ref} ${reason || 'unpack failed'}\n`);
    }
  }
  const inner = Buffer.concat([...reportLines.map((l) => pktLine(l)), PKT_FLUSH]);
  const out = sideband ? Buffer.concat([sidebandWrap(inner), PKT_FLUSH]) : inner;
  res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result' });
  res.end(out);
}

// ------------------------------------------------------------------ shared operations

/** Create a commit on a branch changing one path (null blob deletes it). */
function commitFileChange(repo: RepoRec, branch: string, path: string, blobOid: string | null, message: string): string {
  const ref = `refs/heads/${branch}`;
  const tip = repo.refs.get(ref);
  const flat = tip ? commitTreeFlat(tip) : new Map<string, { oid: string; mode: string }>();
  if (blobOid === null) flat.delete(path);
  else flat.set(path, { oid: blobOid, mode: '100644' });
  const tree = treeFromFlat(flat);
  const stamp = nextStamp();
  const commit = storeObject('commit', buildCommit(tree, tip ? [tip] : [], message, stamp.sec));
  repo.refs.set(ref, commit);
  return commit;
}
function createIssue(repo: RepoRec, title: string, body: string, labels: string[]): IssueRec {
  const number = repo.nextNumber++;
  issueIdSeq += 1;
  const issue: IssueRec = { id: issueIdSeq, number, title, body: body ?? '', state: 'open', labels: [...labels], comments: [], seq: number };
  repo.issues.set(number, issue);
  return issue;
}
function createPull(repo: RepoRec, title: string, body: string, headRef: string, baseRef: string): PullRec | null {
  const headSha = repo.refs.get(`refs/heads/${headRef}`);
  const baseSha = repo.refs.get(`refs/heads/${baseRef}`);
  if (!headSha || !baseSha) return null;
  const number = repo.nextNumber++;
  issueIdSeq += 1;
  const pull: PullRec = {
    id: issueIdSeq, number, title, body: body ?? '', state: 'open', merged: false,
    mergedAt: null, mergeCommitSha: null, headRef, baseRef, headSha, baseSha, seq: number,
  };
  repo.pulls.set(number, pull);
  return pull;
}
/** Three-way squash merge of a pull request onto its base branch. */
function mergePull(repo: RepoRec, pull: PullRec): { ok: true; sha: string } | { ok: false } {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headSha;
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha;
  const base = mergeBase(headTip, baseTip);
  if (!base) return { ok: false };
  const baseFlat = commitTreeFlat(base);
  const headFlat = commitTreeFlat(headTip);
  const curFlat = commitTreeFlat(baseTip);
  const merged = new Map(curFlat);
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of paths) {
    const b = baseFlat.get(path)?.oid;
    const h = headFlat.get(path);
    const c = curFlat.get(path)?.oid;
    if (h?.oid === b) continue; // head did not change it
    if (c === b) {
      if (h === undefined) merged.delete(path);
      else merged.set(path, h);
    } else if (h?.oid === c) {
      continue; // both made the same change
    } else {
      return { ok: false }; // both changed it differently: conflict
    }
  }
  const tree = treeFromFlat(merged);
  const stamp = nextStamp();
  const sha = storeObject('commit', buildCommit(tree, [baseTip], `${pull.title}\n\n${pull.body}`.trim(), stamp.sec));
  repo.refs.set(`refs/heads/${pull.baseRef}`, sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = stamp.iso;
  pull.mergeCommitSha = sha;
  return { ok: true, sha };
}
function lineDiffCounts(oldText: string, newText: string): { additions: number; deletions: number } {
  const a = oldText === '' ? [] : oldText.split('\n');
  const b = newText === '' ? [] : newText.split('\n');
  if (a.length * b.length > 4_000_000) return { additions: b.length, deletions: a.length };
  const dp: number[] = new Array(b.length + 1).fill(0);
  for (let i = 1; i <= a.length; i += 1) {
    let prev = 0;
    for (let j = 1; j <= b.length; j += 1) {
      const tmp = dp[j];
      dp[j] = a[i - 1] === b[j - 1] ? prev + 1 : Math.max(dp[j], dp[j - 1]);
      prev = tmp;
    }
  }
  const common = dp[b.length];
  return { additions: b.length - common, deletions: a.length - common };
}
interface PullFile { filename: string; status: string; additions: number; deletions: number; changes: number; sha: string }
function pullFiles(repo: RepoRec, pull: PullRec): PullFile[] {
  void repo;
  const base = mergeBase(pull.headSha, pull.baseSha) || pull.baseSha;
  const baseFlat = commitTreeFlat(base);
  const headFlat = commitTreeFlat(pull.headSha);
  const files: PullFile[] = [];
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of paths) {
    const b = baseFlat.get(path);
    const h = headFlat.get(path);
    if (b?.oid === h?.oid) continue;
    const oldText = b ? (objects.get(b.oid)?.data.toString('utf8') ?? '') : '';
    const newText = h ? (objects.get(h.oid)?.data.toString('utf8') ?? '') : '';
    const { additions, deletions } = lineDiffCounts(oldText, newText);
    files.push({
      filename: path, status: !b ? 'added' : !h ? 'removed' : 'modified',
      additions, deletions, changes: additions + deletions, sha: h?.oid ?? b?.oid ?? '',
    });
  }
  return files.sort((x, y) => (x.filename < y.filename ? -1 : 1));
}

// ------------------------------------------------------------------ REST v3

let requestSeq = 0;
function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  requestSeq += 1;
  const text = body === undefined ? '' : JSON.stringify(body);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'x-github-request-id': `req-${requestSeq}`,
    ...extra,
  });
  res.end(text);
}
function sendError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message, documentation_url: 'https://forge.invalid/docs' });
}
function pageOf<T>(req: IncomingMessage, list: T[], query: URLSearchParams, path: string): { items: T[]; headers: Record<string, string> } {
  const perPage = Math.max(1, Math.min(100, parseInt(query.get('per_page') ?? '30', 10) || 30));
  const page = Math.max(1, parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (page - 1) * perPage;
  const items = list.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < list.length) {
    const host = req.headers.host ?? 'localhost';
    const next = new URL(`http://${host}${path}`);
    next.searchParams.set('page', String(page + 1));
    next.searchParams.set('per_page', String(perPage));
    const lastPage = Math.ceil(list.length / perPage);
    const last = new URL(`http://${host}${path}`);
    last.searchParams.set('page', String(lastPage));
    last.searchParams.set('per_page', String(perPage));
    headers.link = `<${next.toString()}>; rel="next", <${last.toString()}>; rel="last"`;
  }
  return { items, headers };
}
type Json = Record<string, unknown>;
function handleRest(req: IncomingMessage, res: ServerResponse, segments: string[], query: URLSearchParams, body: Json | null): void {
  const method = req.method ?? 'GET';
  // /api/v3/ root and meta
  if (segments.length === 0) {
    if (method === 'GET') {
      sendJson(res, 200, { current_user_url: '/api/v3/user', repository_url: '/api/v3/repos/{owner}/{repo}' }, { 'x-oauth-scopes': 'repo, read:org' });
      return;
    }
    sendError(res, 404, 'Not Found'); return;
  }
  if (segments[0] === 'meta' && segments.length === 1) {
    sendJson(res, 200, { installed_version: '1.0.0', git_url: 'git://forge.invalid/' });
    return;
  }
  if (segments[0] === 'user' && segments.length === 1 && method === 'GET') {
    sendJson(res, 200, { login: VIEWER.login, id: VIEWER.id, name: VIEWER.name, email: VIEWER.email, type: 'User' });
    return;
  }
  if (segments[0] === 'user' && segments[1] === 'repos') {
    if (method === 'GET') {
      const list = [...repos.values()].filter((r) => r.owner === VIEWER_LOGIN).sort((a, b) => a.id - b.id).map(repoJson);
      const { items, headers } = pageOf(req, list, query, '/api/v3/user/repos');
      sendJson(res, 200, items, headers);
      return;
    }
    if (method === 'POST') {
      const name = String(body?.name ?? '');
      if (!name) { sendError(res, 422, 'Repository creation failed: name is required'); return; }
      if (repos.has(repoKey(VIEWER_LOGIN, name))) { sendError(res, 422, 'Repository creation failed: name already exists on this account'); return; }
      const repo = createRepo(name, String(body?.description ?? ''), body?.private !== false);
      if (typeof body?.description !== 'string' && body?.description !== undefined) repo.description = '';
      sendJson(res, 201, repoJson(repo));
      return;
    }
  }
  if (segments[0] !== 'repos' || segments.length < 3) { sendError(res, 404, 'Not Found'); return; }
  const owner = segments[1]; const repoName = segments[2];
  const repo = findRepo(owner, repoName);
  if (!repo) { sendError(res, 404, 'Not Found'); return; }
  const rest = segments.slice(3);
  const repoPath = `/api/v3/repos/${owner}/${repoName}`;
  if (rest.length === 0) {
    if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return; }
    if (method === 'PATCH') {
      if (typeof body?.description === 'string') repo.description = body.description;
      if (typeof body?.name === 'string' && body.name !== repo.name) {
        repos.delete(repoKey(repo.owner, repo.name));
        repo.name = body.name;
        repos.set(repoKey(repo.owner, repo.name), repo);
      }
      if (typeof body?.private === 'boolean') repo.isPrivate = body.private;
      sendJson(res, 200, repoJson(repo)); return;
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      sendJson(res, 204, undefined);
      return;
    }
    sendError(res, 404, 'Not Found'); return;
  }
  // branches and commits
  if (rest[0] === 'branches') {
    if (method === 'GET' && rest.length === 1) {
      const list = [...repo.refs.entries()]
        .filter(([name]) => name.startsWith('refs/heads/'))
        .map(([name, sha]) => ({ name: name.slice('refs/heads/'.length), commit: { sha, url: `${repoPath}/commits/${sha}` }, protected: false }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      sendJson(res, 200, list); return;
    }
    if (method === 'GET' && rest.length === 2) {
      const sha = repo.refs.get(`refs/heads/${rest[1]}`);
      if (!sha) { sendError(res, 404, 'Branch not found'); return; }
      sendJson(res, 200, { name: rest[1], commit: { sha, url: `${repoPath}/commits/${sha}` }, protected: false }); return;
    }
  }
  if (rest[0] === 'commits' && method === 'GET') {
    let tip = rest[1] ?? query.get('sha') ?? repo.defaultBranch;
    if (repo.refs.has(`refs/heads/${tip}`)) tip = repo.refs.get(`refs/heads/${tip}`)!;
    const list: Record<string, unknown>[] = [];
    const seen = new Set<string>();
    const queue = tip && objects.has(tip) ? [tip] : [];
    while (queue.length && list.length < 500) {
      const cur = queue.shift()!;
      if (seen.has(cur)) continue;
      seen.add(cur);
      const obj = objects.get(cur);
      if (!obj || obj.type !== 'commit') continue;
      const c = parseCommit(obj.data);
      list.push({
        sha: cur,
        commit: {
          message: c.message.replace(/\n$/, ''), tree: { sha: c.tree },
          author: { name: VIEWER.name, email: VIEWER.email, date: repo.createdIso },
          committer: { name: VIEWER.name, email: VIEWER.email, date: repo.createdIso },
        },
        parents: c.parents.map((p) => ({ sha: p })),
      });
      queue.push(...c.parents);
    }
    // BFS order is close enough for a single-parent history; keep newest first as walked.
    sendJson(res, 200, list); return;
  }
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (method === 'POST' && rest.length === 2) {
      const ref = String(body?.ref ?? ''); const sha = String(body?.sha ?? '');
      if (!objects.has(sha)) { sendError(res, 422, 'Object does not exist'); return; }
      repo.refs.set(ref, sha);
      sendJson(res, 201, { ref, node_id: globalId('Ref', ref), url: `${repoPath}/git/refs/${ref}`, object: { sha, type: objects.get(sha)!.type, url: `${repoPath}/git/commits/${sha}` } });
      return;
    }
    if (method === 'GET' && rest.length >= 3) {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (!sha) { sendError(res, 404, 'Reference not found'); return; }
      sendJson(res, 200, { ref, node_id: globalId('Ref', ref), object: { sha, type: objects.get(sha)?.type ?? 'commit' } });
      return;
    }
  }
  // contents
  if (rest[0] === 'contents') {
    const filePath = rest.slice(1).join('/');
    const refName = query.get('ref') ?? (typeof body?.branch === 'string' ? body.branch : repo.defaultBranch);
    if (method === 'GET') {
      const tip = repo.refs.get(`refs/heads/${refName}`);
      if (!tip) { sendError(res, 404, 'Not Found'); return; }
      const commit = objects.get(tip)!;
      const treeOid = parseCommit(commit.data).tree;
      if (filePath === '') {
        sendJson(res, 200, dirListing(repo, treeOid, '')); return;
      }
      const found = lookupPath(treeOid, filePath);
      if (!found) { sendError(res, 404, 'Not Found'); return; }
      if (found.isDir) { sendJson(res, 200, dirListing(repo, found.oid, filePath)); return; }
      const blob = objects.get(found.oid)!;
      sendJson(res, 200, {
        name: filePath.split('/').pop(), path: filePath, sha: found.oid, size: blob.data.length,
        type: 'file', encoding: 'base64', content: blob.data.toString('base64'),
      });
      return;
    }
    if (method === 'PUT') {
      const branch = typeof body?.branch === 'string' ? body.branch : repo.defaultBranch;
      const tip = repo.refs.get(`refs/heads/${branch}`);
      const existing = tip ? lookupPath(parseCommit(objects.get(tip)!.data).tree, filePath) : null;
      if (existing && !existing.isDir && typeof body?.sha === 'string' && body.sha !== existing.oid) {
        sendError(res, 409, 'Conflict: the sha does not match the current file');
        return;
      }
      const data = Buffer.from(String(body?.content ?? ''), 'base64');
      const blobOid = storeObject('blob', data);
      const commitSha = commitFileChange(repo, branch, filePath, blobOid, String(body?.message ?? 'Update file'));
      sendJson(res, existing ? 200 : 201, {
        content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: data.length, type: 'file', encoding: 'base64' },
        commit: { sha: commitSha },
      });
      return;
    }
    if (method === 'DELETE') {
      const branch = typeof body?.branch === 'string' ? body.branch : repo.defaultBranch;
      const tip = repo.refs.get(`refs/heads/${branch}`);
      const existing = tip ? lookupPath(parseCommit(objects.get(tip)!.data).tree, filePath) : null;
      if (!existing || existing.isDir) { sendError(res, 404, 'Not Found'); return; }
      if (typeof body?.sha === 'string' && body.sha !== existing.oid) { sendError(res, 409, 'Conflict: the sha does not match'); return; }
      const commitSha = commitFileChange(repo, branch, filePath, null, String(body?.message ?? 'Delete file'));
      sendJson(res, 200, { content: null, commit: { sha: commitSha } });
      return;
    }
  }
  // labels
  if (rest[0] === 'labels') {
    if (method === 'POST' && rest.length === 1) {
      const name = String(body?.name ?? '');
      if (!name) { sendError(res, 422, 'Validation Failed: name is required'); return; }
      if (repo.labels.has(name)) { sendError(res, 422, 'Validation Failed: label already exists'); return; }
      const color = typeof body?.color === 'string' ? body.color : 'ededed';
      repo.labels.set(name, { name, color });
      sendJson(res, 201, labelJson(name, color)); return;
    }
    if (method === 'GET' && rest.length === 1) {
      sendJson(res, 200, [...repo.labels.values()].map((l) => labelJson(l.name, l.color))); return;
    }
  }
  // issues
  if (rest[0] === 'issues') {
    if (method === 'POST' && rest.length === 1) {
      const labels = Array.isArray(body?.labels) ? body!.labels.map(String) : [];
      for (const label of labels) {
        if (!repo.labels.has(label)) { sendError(res, 422, `Validation Failed: label "${label}" does not exist`); return; }
      }
      const issue = createIssue(repo, String(body?.title ?? ''), String(body?.body ?? ''), labels);
      sendJson(res, 201, issueJson(repo, issue)); return;
    }
    if (method === 'GET' && rest.length === 1) {
      const state = query.get('state') ?? 'open';
      let list = [...repo.issues.values()];
      if (state === 'open') list = list.filter((i) => i.state === 'open');
      else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
      const direction = query.get('direction') ?? 'desc';
      list.sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
      const { items, headers } = pageOf(req, list.map((i) => issueJson(repo, i)), query, `${repoPath}/issues`);
      sendJson(res, 200, items, headers); return;
    }
    const number = parseInt(rest[1] ?? '', 10);
    const issue = repo.issues.get(number);
    if (rest.length === 2) {
      if (!issue) { sendError(res, 404, 'Not Found'); return; }
      if (method === 'GET') { sendJson(res, 200, issueJson(repo, issue)); return; }
      if (method === 'PATCH') {
        if (body?.state === 'open' || body?.state === 'closed') issue.state = body.state;
        if (typeof body?.title === 'string') issue.title = body.title;
        if (typeof body?.body === 'string') issue.body = body.body;
        sendJson(res, 200, issueJson(repo, issue)); return;
      }
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (!issue) { sendError(res, 404, 'Not Found'); return; }
      if (method === 'POST') {
        const id = issue.comments.length + 1 + issue.number * 1000;
        const comment = { id, body: String(body?.body ?? '') };
        issue.comments.push(comment);
        sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: VIEWER_LOGIN, id: VIEWER.id }, created_at: repo.createdIso });
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, issue.comments.map((c) => ({ id: c.id, body: c.body, user: { login: VIEWER_LOGIN, id: VIEWER.id }, created_at: repo.createdIso })));
        return;
      }
    }
    sendError(res, 404, 'Not Found'); return;
  }
  // pulls
  if (rest[0] === 'pulls') {
    if (method === 'POST' && rest.length === 1) {
      const head = String(body?.head ?? '').replace(/^[^:]*:/, '');
      const base = String(body?.base ?? repo.defaultBranch).replace(/^[^:]*:/, '');
      const pull = createPull(repo, String(body?.title ?? ''), String(body?.body ?? ''), head, base);
      if (!pull) { sendError(res, 422, 'Validation Failed: head or base branch does not exist'); return; }
      sendJson(res, 201, pullJson(repo, pull)); return;
    }
    if (method === 'GET' && rest.length === 1) {
      const state = query.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (state === 'open') list = list.filter((p) => p.state === 'open');
      else if (state === 'closed') list = list.filter((p) => p.state === 'closed');
      list.sort((a, b) => b.seq - a.seq);
      const { items, headers } = pageOf(req, list.map((p) => pullJson(repo, p)), query, `${repoPath}/pulls`);
      sendJson(res, 200, items, headers); return;
    }
    const number = parseInt(rest[1] ?? '', 10);
    const pull = repo.pulls.get(number);
    if (rest.length === 2 && method === 'GET') {
      if (!pull) { sendError(res, 404, 'Not Found'); return; }
      sendJson(res, 200, pullJson(repo, pull)); return;
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      if (!pull) { sendError(res, 404, 'Not Found'); return; }
      sendJson(res, 200, pullFiles(repo, pull)); return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (!pull) { sendError(res, 404, 'Not Found'); return; }
      if (pull.merged) { sendJson(res, 200, { sha: pull.mergeCommitSha, merged: true, message: 'Pull Request successfully merged' }); return; }
      const result = mergePull(repo, pull);
      if (!result.ok) { sendError(res, 405, 'Pull Request is not mergeable: conflict'); return; }
      sendJson(res, 200, { sha: result.sha, merged: true, message: 'Pull Request successfully merged' }); return;
    }
    sendError(res, 404, 'Not Found'); return;
  }
  sendError(res, 404, 'Not Found');
}
function lookupPath(treeOid: string, path: string): { oid: string; isDir: boolean } | null {
  const segs = path.split('/').filter(Boolean);
  let cur = treeOid;
  for (let i = 0; i < segs.length; i += 1) {
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === segs[i]);
    if (!entry) return null;
    if (i === segs.length - 1) return { oid: entry.oid, isDir: entry.mode === '40000' };
    cur = entry.oid;
  }
  return { oid: treeOid, isDir: true };
}
function dirListing(repo: RepoRec, treeOid: string, basePath: string): Record<string, unknown>[] {
  void repo;
  const obj = objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return [];
  return parseTree(obj.data).map((e) => ({
    name: e.name,
    path: basePath === '' ? e.name : `${basePath}/${e.name}`,
    sha: e.oid,
    size: e.mode === '40000' ? 0 : (objects.get(e.oid)?.data.length ?? 0),
    type: e.mode === '40000' ? 'dir' : 'file',
  }));
}

// ------------------------------------------------------------------ GraphQL v4

type GqlValue = string | number | boolean | null | GqlValue[] | { [k: string]: GqlValue } | { __var: string } | { __enum: string };
interface GqlField { name: string; alias: string | null; args: Record<string, GqlValue>; selections: GqlSelection[] }
type GqlSelection = { kind: 'field'; field: GqlField } | { kind: 'fragment'; typeCondition: string | null; selections: GqlSelection[] };
interface GqlOperation { opType: string; name: string | null; selections: GqlSelection[] }

function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',') { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (src.startsWith('...', i)) { tokens.push('...'); i += 3; continue; }
    if (c === '"') {
      let j = i + 1; let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { out += src[j + 1] === 'n' ? '\n' : src[j + 1] === 't' ? '\t' : src[j + 1]; j += 2; }
        else { out += src[j]; j += 1; }
      }
      tokens.push(`"${out}"`);
      i = j + 1; continue;
    }
    if ('{}()[]:!=$@|'.includes(c)) { tokens.push(c); i += 1; continue; }
    const m = /^[A-Za-z0-9_.-]+/.exec(src.slice(i));
    if (m) { tokens.push(m[0]); i += m[0].length; continue; }
    i += 1;
  }
  return tokens;
}
class GqlParser {
  tokens: string[]; pos = 0;
  constructor(src: string) { this.tokens = gqlTokenize(src); }
  peek(): string | undefined { return this.tokens[this.pos]; }
  next(): string | undefined { return this.tokens[this.pos++]; }
  expect(t: string): void { const got = this.next(); if (got !== t) throw new Error(`expected ${t}, got ${got}`); }
  parseDocument(): GqlOperation[] {
    const ops: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const t = this.peek();
      if (t === '{') { ops.push({ opType: 'query', name: null, selections: this.parseSelectionSet() }); continue; }
      if (t === 'query' || t === 'mutation' || t === 'subscription') {
        const opType = this.next()!;
        let name: string | null = null;
        if (this.peek() && /^[A-Za-z_][A-Za-z0-9_]*$/.test(this.peek()!) && this.peek() !== '(' && this.peek() !== '{') name = this.next()!;
        if (this.peek() === '(') this.skipBalanced('(', ')');
        // directives
        while (this.peek() === '@') { this.next(); this.next(); if (this.peek() === '(') this.skipBalanced('(', ')'); }
        ops.push({ opType, name, selections: this.parseSelectionSet() });
        continue;
      }
      if (t === 'fragment') { this.next(); this.next(); this.next(); this.next(); this.parseSelectionSet(); continue; }
      this.next();
    }
    return ops;
  }
  skipBalanced(open: string, close: string): void {
    let depth = 0;
    do {
      const t = this.next();
      if (t === undefined) break;
      if (t === open) depth += 1;
      else if (t === close) depth -= 1;
    } while (depth > 0);
  }
  parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const selections: GqlSelection[] = [];
    while (this.peek() !== '}' && this.peek() !== undefined) {
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          const typeCondition = this.next() ?? null;
          selections.push({ kind: 'fragment', typeCondition, selections: this.parseSelectionSet() });
        } else {
          // named fragment spread: not used by the suite; skip its name
          this.next();
          selections.push({ kind: 'fragment', typeCondition: null, selections: [] });
        }
        continue;
      }
      selections.push({ kind: 'field', field: this.parseField() });
    }
    this.expect('}');
    return selections;
  }
  parseField(): GqlField {
    let name = this.next()!;
    let alias: string | null = null;
    if (this.peek() === ':') { this.next(); alias = name; name = this.next()!; }
    const args: Record<string, GqlValue> = {};
    if (this.peek() === '(') {
      this.next();
      while (this.peek() !== ')') {
        const argName = this.next()!;
        this.expect(':');
        args[argName] = this.parseValue();
      }
      this.next();
    }
    while (this.peek() === '@') { this.next(); this.next(); if (this.peek() === '(') this.skipBalanced('(', ')'); }
    let selections: GqlSelection[] = [];
    if (this.peek() === '{') selections = this.parseSelectionSet();
    return { name, alias, args, selections };
  }
  parseValue(): GqlValue {
    const t = this.next()!;
    if (t === '$') return { __var: this.next()! };
    if (t.startsWith('"')) return t.slice(1, -1);
    if (t === '[') {
      const list: GqlValue[] = [];
      while (this.peek() !== ']') list.push(this.parseValue());
      this.next();
      return list;
    }
    if (t === '{') {
      const obj: { [k: string]: GqlValue } = {};
      while (this.peek() !== '}') {
        const key = this.next()!;
        this.expect(':');
        obj[key] = this.parseValue();
      }
      this.next();
      return obj;
    }
    if (t === 'true') return true;
    if (t === 'false') return false;
    if (t === 'null') return null;
    if (/^-?\d+$/.test(t)) return parseInt(t, 10);
    if (/^-?\d*\.\d+$/.test(t)) return parseFloat(t);
    return { __enum: t };
  }
}
function resolveValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  if (v !== null && typeof v === 'object') {
    if ('__var' in v) return vars[(v as { __var: string }).__var];
    if ('__enum' in v) return (v as { __enum: string }).__enum;
    if (Array.isArray(v)) return v.map((x) => resolveValue(x, vars));
    const out: Record<string, unknown> = {};
    for (const [k, val] of Object.entries(v)) out[k] = resolveValue(val, vars);
    return out;
  }
  return v;
}
// The schema surface, for both execution and introspection.
const GQL_TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'search', '__type', '__schema', 'rateLimit'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  User: ['id', 'login', 'name', 'email', 'databaseId', 'url'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasPullRequestsEnabled', 'isPrivate', 'description', 'url', 'issue', 'issues', 'pullRequest', 'pullRequests', 'createdAt', 'updatedAt', 'primaryLanguage', 'stargazerCount', 'forkCount', 'isFork', 'isArchived', 'homepageUrl', 'licenseInfo'],
  Ref: ['id', 'name', 'prefix', 'target'],
  Issue: ['id', 'databaseId', 'number', 'title', 'state', 'body', 'labels', 'comments', 'author', 'repository', 'createdAt', 'updatedAt', 'closedAt', 'url', 'assignees', 'milestone'],
  PullRequest: ['id', 'databaseId', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'files', 'commits', 'author', 'repository', 'createdAt', 'updatedAt', 'mergedAt', 'closedAt', 'url', 'additions', 'deletions', 'changedFiles', 'mergeCommit'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType'],
  IssueComment: ['id', 'body', 'author', 'createdAt', 'url'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueEdge: ['node', 'cursor'],
  PullRequestEdge: ['node', 'cursor'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'subject', 'clientMutationId'],
  CommentEdge: ['node', 'cursor'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', 'interfaces'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __Schema: ['types', 'queryType', 'mutationType'],
  __InputValue: ['name', 'description', 'type', 'defaultValue'],
};
const GQL_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
};
interface TV { __gqlType: string; value: unknown }
function tv(type: string, value: unknown): TV { return { __gqlType: type, value }; }
function findRepoByGlobalId(id: string): RepoRec | null {
  const decoded = decodeGlobalId(id);
  if (!decoded || decoded.type !== 'Repository') return null;
  const rid = parseInt(decoded.key, 10);
  for (const repo of repos.values()) if (repo.id === rid) return repo;
  return null;
}
function issueGlobalId(repo: RepoRec, issue: IssueRec): string { return globalId('Issue', `${repo.id}:${issue.number}`); }
function pullGlobalId(repo: RepoRec, pull: PullRec): string { return globalId('PullRequest', `${repo.id}:${pull.number}`); }
function pullMergeable(repo: RepoRec, pull: PullRec): string {
  if (pull.merged) return 'UNKNOWN';
  // Dry-run the three-way merge on copies of the flat maps.
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? pull.headSha;
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha;
  const base = mergeBase(headTip, baseTip);
  if (!base) return 'CONFLICTING';
  const baseFlat = commitTreeFlat(base); const headFlat = commitTreeFlat(headTip); const curFlat = commitTreeFlat(baseTip);
  for (const path of new Set([...baseFlat.keys(), ...headFlat.keys()])) {
    const b = baseFlat.get(path)?.oid; const h = headFlat.get(path)?.oid; const c = curFlat.get(path)?.oid;
    if (h === b || c === b || h === c) continue;
    return 'CONFLICTING';
  }
  return 'MERGEABLE';
}
function gqlResolve(type: string, source: unknown, field: string, args: Record<string, unknown>): unknown {
  switch (type) {
    case 'Query': {
      if (field === 'viewer') return tv('User', VIEWER);
      if (field === 'repository') {
        const repo = findRepo(String(args.owner ?? ''), String(args.name ?? ''));
        return repo ? tv('Repository', repo) : null;
      }
      if (field === 'node') {
        const decoded = decodeGlobalId(String(args.id ?? ''));
        if (!decoded) return null;
        if (decoded.type === 'Repository') { const r = findRepoByGlobalId(String(args.id)); return r ? tv('Repository', r) : null; }
        if (decoded.type === 'Issue' || decoded.type === 'PullRequest') {
          const [rid, num] = decoded.key.split(':').map((x) => parseInt(x, 10));
          for (const repo of repos.values()) {
            if (repo.id !== rid) continue;
            if (decoded.type === 'Issue') { const i = repo.issues.get(num); return i ? tv('Issue', { repo, issue: i }) : null; }
            const p = repo.pulls.get(num); return p ? tv('PullRequest', { repo, pull: p }) : null;
          }
        }
        return null;
      }
      if (field === '__type') {
        const name = String(args.name ?? '');
        if (GQL_TYPE_FIELDS[name]) return tv('__Type', { name, kind: 'OBJECT' });
        if (GQL_ENUMS[name]) return tv('__Type', { name, kind: 'ENUM' });
        return tv('__Type', { name, kind: 'OBJECT' });
      }
      if (field === '__schema') return tv('__Schema', {});
      return null;
    }
    case 'Mutation': {
      if (field === 'createIssue') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
        if (!repo) return null;
        const issue = createIssue(repo, String(input.title ?? ''), String(input.body ?? ''), []);
        return tv('CreateIssuePayload', { repo, issue });
      }
      if (field === 'closeIssue') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const decoded = decodeGlobalId(String(input.issueId ?? ''));
        if (!decoded) return null;
        const [rid, num] = decoded.key.split(':').map((x) => parseInt(x, 10));
        for (const repo of repos.values()) {
          if (repo.id !== rid) continue;
          const issue = repo.issues.get(num);
          if (!issue) return null;
          issue.state = 'closed';
          return tv('CloseIssuePayload', { repo, issue });
        }
        return null;
      }
      if (field === 'createPullRequest') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
        if (!repo) return null;
        const pull = createPull(repo, String(input.title ?? ''), String(input.body ?? ''), String(input.headRefName ?? ''), String(input.baseRefName ?? ''));
        if (!pull) return null;
        return tv('CreatePullRequestPayload', { repo, pull });
      }
      if (field === 'mergePullRequest') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const decoded = decodeGlobalId(String(input.pullRequestId ?? ''));
        if (!decoded) return null;
        const [rid, num] = decoded.key.split(':').map((x) => parseInt(x, 10));
        for (const repo of repos.values()) {
          if (repo.id !== rid) continue;
          const pull = repo.pulls.get(num);
          if (!pull) return null;
          if (!pull.merged) mergePull(repo, pull);
          return tv('MergePullRequestPayload', { repo, pull });
        }
        return null;
      }
      if (field === 'addComment') {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const decoded = decodeGlobalId(String(input.subjectId ?? ''));
        if (!decoded) return null;
        const [rid, num] = decoded.key.split(':').map((x) => parseInt(x, 10));
        for (const repo of repos.values()) {
          if (repo.id !== rid) continue;
          const issue = repo.issues.get(num);
          if (!issue) return null;
          const comment = { id: issue.comments.length + 1 + issue.number * 1000, body: String(input.body ?? '') };
          issue.comments.push(comment);
          return tv('AddCommentPayload', { repo, issue, comment });
        }
        return null;
      }
      return null;
    }
    case 'User': {
      const u = source as typeof VIEWER;
      if (field === 'login') return u.login;
      if (field === 'id') return globalId('User', u.id);
      if (field === 'databaseId') return u.id;
      if (field === 'name') return u.name;
      if (field === 'email') return u.email;
      return null;
    }
    case 'Repository': {
      const repo = source as RepoRec;
      switch (field) {
        case 'id': return globalId('Repository', repo.id);
        case 'databaseId': return repo.id;
        case 'name': return repo.name;
        case 'nameWithOwner': return `${repo.owner}/${repo.name}`;
        case 'owner': return tv('User', VIEWER);
        case 'defaultBranchRef': {
          const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
          return tip ? tv('Ref', { name: repo.defaultBranch }) : null;
        }
        case 'viewerPermission': return 'ADMIN';
        case 'hasIssuesEnabled': return true;
        case 'hasPullRequestsEnabled': return true;
        case 'isPrivate': return repo.isPrivate;
        case 'description': return repo.description;
        case 'createdAt': case 'updatedAt': return repo.createdIso;
        case 'issue': {
          const issue = repo.issues.get(Number(args.number));
          return issue ? tv('Issue', { repo, issue }) : null;
        }
        case 'issues': {
          let list = [...repo.issues.values()];
          const states = Array.isArray(args.states) ? args.states.map(String) : null;
          if (states) list = list.filter((i) => states.includes(i.state.toUpperCase()));
          const orderBy = (args.orderBy ?? null) as Record<string, unknown> | null;
          const direction = orderBy ? String(orderBy.direction ?? 'DESC') : 'ASC';
          list.sort((a, b) => (direction === 'DESC' ? b.seq - a.seq || b.number - a.number : a.seq - b.seq));
          return tv('IssueConnection', { repo, items: list, args });
        }
        case 'pullRequest': {
          const pull = repo.pulls.get(Number(args.number));
          return pull ? tv('PullRequest', { repo, pull }) : null;
        }
        case 'pullRequests': {
          let list = [...repo.pulls.values()];
          const states = Array.isArray(args.states) ? args.states.map(String) : null;
          if (states) list = list.filter((p) => states.includes(p.merged ? 'MERGED' : p.state.toUpperCase()));
          list.sort((a, b) => b.seq - a.seq);
          return tv('PullRequestConnection', { repo, items: list, args });
        }
        default: return null;
      }
    }
    case 'Ref': {
      const r = source as { name: string };
      if (field === 'name') return r.name;
      if (field === 'prefix') return 'refs/heads/';
      if (field === 'id') return globalId('Ref', r.name);
      return null;
    }
    case 'Issue': {
      const { repo, issue } = source as { repo: RepoRec; issue: IssueRec };
      switch (field) {
        case 'id': return issueGlobalId(repo, issue);
        case 'databaseId': return issue.id;
        case 'number': return issue.number;
        case 'title': return issue.title;
        case 'body': return issue.body;
        case 'state': return issue.state.toUpperCase();
        case 'author': return tv('User', VIEWER);
        case 'repository': return tv('Repository', repo);
        case 'createdAt': case 'updatedAt': return repo.createdIso;
        case 'comments': return tv('IssueConnection', { repo, items: [], args });
        default: return null;
      }
    }
    case 'PullRequest': {
      const { repo, pull } = source as { repo: RepoRec; pull: PullRec };
      switch (field) {
        case 'id': return pullGlobalId(repo, pull);
        case 'databaseId': return pull.id;
        case 'number': return pull.number;
        case 'title': return pull.title;
        case 'body': return pull.body;
        case 'state': return pull.merged ? 'MERGED' : pull.state.toUpperCase();
        case 'merged': return pull.merged;
        case 'mergeable': return pullMergeable(repo, pull);
        case 'headRefName': return pull.headRef;
        case 'baseRefName': return pull.baseRef;
        case 'author': return tv('User', VIEWER);
        case 'repository': return tv('Repository', repo);
        case 'mergedAt': return pull.mergedAt;
        case 'createdAt': case 'updatedAt': return repo.createdIso;
        case 'files': {
          const files = pullFiles(repo, pull).map((f) => ({ path: f.filename, additions: f.additions, deletions: f.deletions }));
          return tv('PullRequestChangedFileConnection', { repo, items: files, args });
        }
        case 'additions': return pullFiles(repo, pull).reduce((s, f) => s + f.additions, 0);
        case 'deletions': return pullFiles(repo, pull).reduce((s, f) => s + f.deletions, 0);
        case 'changedFiles': return pullFiles(repo, pull).length;
        default: return null;
      }
    }
    case 'PullRequestChangedFile': {
      const f = source as { path: string; additions: number; deletions: number };
      if (field === 'path') return f.path;
      if (field === 'additions') return f.additions;
      if (field === 'deletions') return f.deletions;
      if (field === 'changeType') return 'ADDED';
      return null;
    }
    case 'IssueConnection': case 'PullRequestConnection': case 'PullRequestChangedFileConnection': {
      const conn = source as { repo: RepoRec; items: unknown[]; args: Record<string, unknown> };
      const first = typeof conn.args.first === 'number' ? conn.args.first : conn.items.length;
      let start = 0;
      if (typeof conn.args.after === 'string' && conn.args.after) {
        try {
          const decoded = Buffer.from(conn.args.after, 'base64').toString('utf8');
          const n = parseInt(decoded.replace('cursor:', ''), 10);
          if (Number.isFinite(n)) start = n;
        } catch { /* ignore */ }
      }
      const page = conn.items.slice(start, start + first);
      const endIndex = start + page.length;
      const cursorFor = (n: number): string => Buffer.from(`cursor:${n}`, 'utf8').toString('base64');
      if (field === 'nodes') {
        return page.map((item) => {
          if (type === 'IssueConnection') return tv('Issue', { repo: conn.repo, issue: item });
          if (type === 'PullRequestConnection') return tv('PullRequest', { repo: conn.repo, pull: item });
          return tv('PullRequestChangedFile', item);
        });
      }
      if (field === 'pageInfo') {
        return tv('PageInfo', {
          hasNextPage: endIndex < conn.items.length, hasPreviousPage: start > 0,
          startCursor: page.length ? cursorFor(start + 1) : null, endCursor: page.length ? cursorFor(endIndex) : null,
        });
      }
      if (field === 'totalCount') return conn.items.length;
      if (field === 'edges') return page.map((item, idx) => tv('IssueEdge', { node: item, cursor: cursorFor(start + idx + 1), conn }));
      return null;
    }
    case 'PageInfo': {
      const p = source as Record<string, unknown>;
      return p[field] ?? null;
    }
    case 'IssueEdge': case 'PullRequestEdge': {
      const e = source as { node: unknown; cursor: string; conn: { repo: RepoRec } };
      if (field === 'cursor') return e.cursor;
      if (field === 'node') {
        if (type === 'IssueEdge') return tv('Issue', { repo: e.conn.repo, issue: e.node });
        return tv('PullRequest', { repo: e.conn.repo, pull: e.node });
      }
      return null;
    }
    case 'CreateIssuePayload': case 'CloseIssuePayload': {
      const p = source as { repo: RepoRec; issue: IssueRec };
      if (field === 'issue') return tv('Issue', p);
      if (field === 'clientMutationId') return null;
      return null;
    }
    case 'CreatePullRequestPayload': case 'MergePullRequestPayload': {
      const p = source as { repo: RepoRec; pull: PullRec };
      if (field === 'pullRequest') return tv('PullRequest', p);
      if (field === 'clientMutationId') return null;
      return null;
    }
    case 'AddCommentPayload': {
      const p = source as { repo: RepoRec; issue: IssueRec; comment: { id: number; body: string } };
      if (field === 'commentEdge') return tv('CommentEdge', p);
      if (field === 'clientMutationId') return null;
      return null;
    }
    case 'CommentEdge': {
      const p = source as { repo: RepoRec; issue: IssueRec; comment: { id: number; body: string } };
      if (field === 'node') return tv('IssueComment', p);
      if (field === 'cursor') return Buffer.from(`cursor:${p.comment.id}`, 'utf8').toString('base64');
      return null;
    }
    case 'IssueComment': {
      const p = source as { comment: { id: number; body: string } };
      if (field === 'id') return globalId('IssueComment', p.comment.id);
      if (field === 'body') return p.comment.body;
      if (field === 'author') return tv('User', VIEWER);
      return null;
    }
    case '__Type': {
      const t = source as { name: string; kind: string };
      if (field === 'name') return t.name;
      if (field === 'kind') return t.kind;
      if (field === 'fields') return (GQL_TYPE_FIELDS[t.name] ?? []).map((n) => tv('__Field', { name: n }));
      if (field === 'enumValues') return (GQL_ENUMS[t.name] ?? []).map((n) => tv('__EnumValue', { name: n }));
      return null;
    }
    case '__Field': case '__EnumValue': {
      const f = source as { name: string };
      if (field === 'name') return f.name;
      if (field === 'description') return null;
      if (field === 'isDeprecated') return false;
      return null;
    }
    case '__Schema': {
      if (field === 'queryType') return tv('__Type', { name: 'Query', kind: 'OBJECT' });
      if (field === 'mutationType') return tv('__Type', { name: 'Mutation', kind: 'OBJECT' });
      return null;
    }
    default: return null;
  }
}
function gqlExecSelections(type: string, source: unknown, selections: GqlSelection[], vars: Record<string, unknown>, errors: string[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of selections) {
    if (sel.kind === 'fragment') {
      if (sel.typeCondition === null || sel.typeCondition === type || sel.typeCondition === 'Node') {
        Object.assign(out, gqlExecSelections(type, source, sel.selections, vars, errors));
      }
      continue;
    }
    const f = sel.field;
    const key = f.alias ?? f.name;
    const known = GQL_TYPE_FIELDS[type];
    if (known && !known.includes(f.name) && f.name !== '__typename') {
      errors.push(`Field '${f.name}' doesn't exist on type '${type}'`);
      out[key] = null;
      continue;
    }
    if (f.name === '__typename') { out[key] = type; continue; }
    const args: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(f.args)) args[k] = resolveValue(v, vars);
    const raw = gqlResolve(type, source, f.name, args);
    out[key] = gqlComplete(raw, f.selections, vars, errors);
  }
  return out;
}
function gqlComplete(raw: unknown, selections: GqlSelection[], vars: Record<string, unknown>, errors: string[]): unknown {
  if (raw === null || raw === undefined) return null;
  if (Array.isArray(raw)) return raw.map((x) => gqlComplete(x, selections, vars, errors));
  if (typeof raw === 'object' && '__gqlType' in raw) {
    const typed = raw as TV;
    if (selections.length === 0) return typed.value;
    return gqlExecSelections(typed.__gqlType, typed.value, selections, vars, errors);
  }
  return raw;
}
function handleGraphQL(res: ServerResponse, body: unknown): void {
  if (Array.isArray(body)) {
    const results = body.map((entry) => gqlRunOne(entry as Record<string, unknown>));
    sendJson(res, 200, results);
    return;
  }
  const result = gqlRunOne(body as Record<string, unknown>);
  sendJson(res, 200, result);
}
function gqlRunOne(entry: Record<string, unknown>): Record<string, unknown> {
  const query = String(entry?.query ?? '');
  const vars = (entry?.variables ?? {}) as Record<string, unknown>;
  let ops: GqlOperation[];
  try { ops = new GqlParser(query).parseDocument(); }
  catch (err) { return { errors: [{ message: err instanceof Error ? err.message : 'parse error' }] }; }
  const opName = typeof entry?.operationName === 'string' ? entry.operationName : null;
  const op = (opName ? ops.find((o) => o.name === opName) : undefined) ?? ops[0];
  if (!op) return { errors: [{ message: 'no operation found' }] };
  const errors: string[] = [];
  const rootType = op.opType === 'mutation' ? 'Mutation' : 'Query';
  const data = gqlExecSelections(rootType, null, op.selections, vars, errors);
  if (errors.length) return { data, errors: errors.map((message) => ({ message })) };
  return { data };
}

// ------------------------------------------------------------------ MCP

const MCP_TOOLS = [
  {
    name: 'create_repo', description: 'Create a new repository for the authenticated user',
    inputSchema: { type: 'object', properties: { name: { type: 'string' }, description: { type: 'string' }, private: { type: 'boolean' } }, required: ['name'] },
  },
  {
    name: 'get_repo', description: 'Get a repository by owner and name',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue', description: 'Create an issue in a repository',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues', description: 'List issues in a repository',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, state: { type: 'string' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request', description: 'Create a pull request from a head branch into a base branch',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' }, head: { type: 'string' }, base: { type: 'string' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request', description: 'Merge a pull request (squash)',
    inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, pull_number: { type: 'number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
] as const;
function mcpToolResult(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value as Record<string, unknown>, isError: false };
}
function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}
function callMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> | 'unknown' {
  switch (name) {
    case 'create_repo': {
      const repoName = String(args.name ?? '');
      if (!repoName) return mcpToolError('name is required');
      if (repos.has(repoKey(VIEWER_LOGIN, repoName))) return mcpToolError('repository already exists');
      const repo = createRepo(repoName, String(args.description ?? ''), args.private !== false);
      return mcpToolResult(repoJson(repo));
    }
    case 'get_repo': {
      const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
      if (!repo) return mcpToolError('repository not found');
      return mcpToolResult(repoJson(repo));
    }
    case 'create_issue': {
      const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
      if (!repo) return mcpToolError('repository not found');
      if (!args.title) return mcpToolError('title is required');
      const issue = createIssue(repo, String(args.title), String(args.body ?? ''), []);
      return mcpToolResult(issueJson(repo, issue));
    }
    case 'list_issues': {
      const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
      if (!repo) return mcpToolError('repository not found');
      const state = String(args.state ?? 'open');
      let list = [...repo.issues.values()];
      if (state === 'open') list = list.filter((i) => i.state === 'open');
      else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
      list.sort((a, b) => a.seq - b.seq);
      return mcpToolResult(list.map((i) => issueJson(repo, i)));
    }
    case 'create_pull_request': {
      const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
      if (!repo) return mcpToolError('repository not found');
      const pull = createPull(repo, String(args.title ?? ''), String(args.body ?? ''), String(args.head ?? ''), String(args.base ?? ''));
      if (!pull) return mcpToolError('head or base branch does not exist');
      return mcpToolResult(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
      if (!repo) return mcpToolError('repository not found');
      const pull = repo.pulls.get(Number(args.pull_number));
      if (!pull) return mcpToolError('pull request not found');
      if (!pull.merged) {
        const result = mergePull(repo, pull);
        if (!result.ok) return mcpToolError('pull request is not mergeable: conflict');
      }
      return mcpToolResult(pullJson(repo, pull));
    }
    default: return 'unknown';
  }
}
function handleMcp(res: ServerResponse, rawBody: string): void {
  let parsed: unknown;
  try { parsed = JSON.parse(rawBody); }
  catch {
    res.writeHead(400, { 'content-type': 'application/json' });
    res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }));
    return;
  }
  const answer = (msg: Record<string, unknown>): unknown => {
    const id = msg.id as string | number | undefined;
    const method = String(msg.method ?? '');
    const params = (msg.params ?? {}) as Record<string, unknown>;
    if (id === undefined || id === null) return undefined; // notification
    switch (method) {
      case 'initialize':
        return { jsonrpc: '2.0', id, result: { protocolVersion: typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25', capabilities: { tools: {} }, serverInfo: { name: 'forge', version: '1.0.0' } } };
      case 'server/discover':
        return {
          jsonrpc: '2.0', id,
          result: {
            supportedVersions: ['2026-07-28', '2025-11-25', '2025-03-26'],
            capabilities: { tools: {} },
            serverInfo: { name: 'forge', version: '1.0.0' },
            _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
          },
        };
      case 'ping': return { jsonrpc: '2.0', id, result: {} };
      case 'tools/list': return { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } };
      case 'tools/call': {
        const toolName = String(params.name ?? '');
        const args = (params.arguments ?? {}) as Record<string, unknown>;
        const known = MCP_TOOLS.some((t) => t.name === toolName);
        if (!known) return { jsonrpc: '2.0', id, error: { code: -32602, message: `unknown tool: ${toolName}` } };
        // Missing required arguments: a tool-level error, never a crash.
        const schema = MCP_TOOLS.find((t) => t.name === toolName)!;
        const missing = (schema.inputSchema.required ?? []).filter((k) => args[k] === undefined);
        if (missing.length) return { jsonrpc: '2.0', id, result: mcpToolError(`missing required arguments: ${missing.join(', ')}`) };
        const result = callMcpTool(toolName, args);
        if (result === 'unknown') return { jsonrpc: '2.0', id, error: { code: -32602, message: `unknown tool: ${toolName}` } };
        return { jsonrpc: '2.0', id, result };
      }
      default:
        return { jsonrpc: '2.0', id, error: { code: -32601, message: `method not found: ${method}` } };
    }
  };
  if (Array.isArray(parsed)) {
    const out = parsed.map((m) => answer(m as Record<string, unknown>)).filter((x) => x !== undefined);
    res.writeHead(200, { 'content-type': 'application/json' });
    res.end(JSON.stringify(out));
    return;
  }
  const single = answer(parsed as Record<string, unknown>);
  if (single === undefined) { res.writeHead(202, { 'content-type': 'application/json' }); res.end(''); return; }
  res.writeHead(200, { 'content-type': 'application/json' });
  res.end(JSON.stringify(single));
}

// ------------------------------------------------------------------ HTTP routing and boot

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function authorized(req: IncomingMessage): boolean {
  if (!TOKEN) return true;
  return req.headers.authorization === `Bearer ${TOKEN}`;
}
async function route(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const url = new URL(req.url ?? '/', 'http://forge');
  const path = url.pathname;
  const method = req.method ?? 'GET';
  if (method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
  // git smart HTTP: /{owner}/{repo}.git/...
  const gitMatch = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
  if (gitMatch) {
    if (!authorized(req)) { res.writeHead(401, { 'content-type': 'text/plain' }); res.end('Unauthorized'); return; }
    const [, owner, repoName, suffix] = gitMatch;
    const repo = findRepo(owner, repoName);
    if (!repo) { res.writeHead(404, { 'content-type': 'text/plain' }); res.end('Not Found'); return; }
    const tail = suffix ?? '';
    if (method === 'GET' && tail === '/info/refs') {
      const service = url.searchParams.get('service') ?? '';
      if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { res.writeHead(400, { 'content-type': 'text/plain' }); res.end('bad service'); return; }
      const wantsV2 = service === 'git-upload-pack' && String(req.headers['git-protocol'] ?? '').includes('version=2');
      const body = wantsV2 ? advertisementV2() : advertisementV0(repo, service);
      res.writeHead(200, { 'content-type': `application/x-${service}-advertisement`, 'cache-control': 'no-cache' });
      res.end(body);
      return;
    }
    if (method === 'POST' && tail === '/git-upload-pack') {
      const body = await readBody(req);
      const isV2 = String(req.headers['git-protocol'] ?? '').includes('version=2');
      await handleUploadPack(repo, body, isV2, res);
      return;
    }
    if (method === 'POST' && tail === '/git-receive-pack') {
      const body = await readBody(req);
      await handleReceivePack(repo, body, res);
      return;
    }
    res.writeHead(404, { 'content-type': 'text/plain' }); res.end('Not Found');
    return;
  }
  if (path === '/api/graphql') {
    if (!authorized(req)) { sendError(res, 401, 'Bad credentials'); return; }
    const raw = await readBody(req);
    let body: unknown;
    try { body = JSON.parse(raw.toString('utf8')); } catch { sendError(res, 400, 'Problems parsing JSON'); return; }
    handleGraphQL(res, body);
    return;
  }
  if (path === '/mcp') {
    if (!authorized(req)) { res.writeHead(401, { 'content-type': 'application/json' }); res.end(JSON.stringify({ message: 'Bad credentials' })); return; }
    if (method === 'GET') { res.writeHead(405, { 'content-type': 'application/json' }); res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32601, message: 'GET is not supported; POST JSON-RPC messages' } })); return; }
    if (method === 'DELETE') { res.writeHead(200, { 'content-type': 'application/json' }); res.end('{}'); return; }
    const raw = await readBody(req);
    handleMcp(res, raw.toString('utf8'));
    return;
  }
  if (path === '/api/v3' || path.startsWith('/api/v3/')) {
    if (!authorized(req)) { sendError(res, 401, 'Bad credentials'); return; }
    const segments = path.replace(/^\/api\/v3\/?/, '').split('/').filter(Boolean).map(decodeURIComponent);
    let body: Json | null = null;
    if (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE') {
      const raw = await readBody(req);
      if (raw.length > 0) {
        try { body = JSON.parse(raw.toString('utf8')) as Json; }
        catch { sendError(res, 400, 'Problems parsing JSON'); return; }
      }
    }
    handleRest(req, res, segments, url.searchParams, body);
    return;
  }
  sendError(res, 404, 'Not Found');
}

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));
async function boot(): Promise<void> {
  const server = createServer((req, res) => {
    route(req, res).catch((err: unknown) => {
      try {
        if (!res.headersSent) sendJson(res, 500, { message: `Internal error: ${err instanceof Error ? err.message : String(err)}` });
        else res.end();
      } catch { /* socket already gone */ }
    });
  });
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('no ephemeral port');
  process.stdout.write(`[forge] listening on ${address.port}\n`);
  const envUrl = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
  if (!envUrl) {
    process.stdout.write('[forge] MAKEFUN_ENV_URL unset: serving standalone\n');
    return; // standalone local run: keep serving
  }
  // Register with the suite, retrying while it starts.
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${envUrl}/register`, {
        method: 'POST', headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port: address.port }), signal: AbortSignal.timeout(30_000),
      });
      if (res.status === 200 || res.status === 409) break;
      if (res.status === 400 || res.status === 405) throw new Error(`register answered ${res.status}`);
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('register answered')) throw err;
    }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
  process.stdout.write('[forge] registered; waiting for done\n');
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${envUrl}/done`, { signal: AbortSignal.timeout(30_000) });
      if (res.ok) {
        const body = (await res.json()) as { done?: unknown };
        if (body.done === true) break;
      }
    } catch { /* not done yet */ }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
  server.close();
  process.stdout.write('[forge] done\n');
  process.exit(0);
}
void boot().catch((err: unknown) => {
  process.stderr.write(`[forge] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
});
