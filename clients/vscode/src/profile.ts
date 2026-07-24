import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";

// ---- Profile data types (matches xark_ir::profile) -------------------------

export type ConstraintKind =
  | "Mul"
  | "Booleanity"
  | "RangeCheck"
  | "Comparison"
  | "Equality"
  | "Xor"
  | "Or"
  | "HintPin"
  | "Other";

export interface ConstraintProfile {
  id: number;
  file: string;
  line: number; // 1-based
  col: number; // 1-based
  chain: string[];
  kind: ConstraintKind;
}

export interface ProfileProgram {
  source_root: string;
  constraints: ConstraintProfile[];
}

// ---- Aggregated views -------------------------------------------------------

export interface LineCost {
  file: string;
  line: number;
  total: number;
  kinds: Map<ConstraintKind, number>;
  /** The source text of that line (best-effort; empty if unreadable). */
  src: string;
  /** Function call-chains for this line (top-level only). */
  chains: Map<string, number>;
}

export interface ProfileSummary {
  sourceRoot: string;
  lines: LineCost[];
  totalConstraints: number;
}

// ---- Parse & aggregate ------------------------------------------------------

/** Parse a `profile.json` file and return the sorted, aggregated view. */
export function loadProfile(profilePath: string): ProfileSummary | null {
  let text: string;
  try {
    text = fs.readFileSync(profilePath, "utf-8");
  } catch {
    return null;
  }

  let prog: ProfileProgram;
  try {
    prog = JSON.parse(text) as ProfileProgram;
  } catch {
    return null;
  }

  return aggregate(prog);
}

function aggregate(prog: ProfileProgram): ProfileSummary {
  // Group by (file, line)
  const lineMap = new Map<string, LineCost>();

  for (const c of prog.constraints) {
    if (!c.file) continue;
    const key = `${c.file}:${c.line}`;
    let entry = lineMap.get(key);
    if (!entry) {
      entry = {
        file: c.file,
        line: c.line,
        total: 0,
        kinds: new Map(),
        src: "",
        chains: new Map(),
      };
      lineMap.set(key, entry);
    }
    entry.total++;
    entry.kinds.set(c.kind, (entry.kinds.get(c.kind) ?? 0) + 1);
    // Top-level function name (first segment of chain)
    const topFn = c.chain[0] ?? "(top-level)";
    entry.chains.set(topFn, (entry.chains.get(topFn) ?? 0) + 1);
  }

  // Sort by cost descending, then file/line for determinism
  const lines = [...lineMap.values()];
  lines.sort((a, b) => b.total - a.total || a.file.localeCompare(b.file) || a.line - b.line);

  const total = lines.reduce((sum, l) => sum + l.total, 0);

  // Best-effort source line reading (lazy, cached per file)
  const srcCache = new Map<string, string[]>();
  for (const l of lines) {
    l.src = readSourceLine(prog.source_root, l.file, l.line, srcCache);
  }

  return { sourceRoot: prog.source_root, lines, totalConstraints: total };
}

function readSourceLine(
  sourceRoot: string,
  file: string,
  line: number,
  cache: Map<string, string[]>
): string {
  if (!cache.has(file)) {
    const absPath = path.isAbsolute(file) ? file : path.join(sourceRoot, file);
    let lines: string[];
    try {
      lines = fs.readFileSync(absPath, "utf-8").split("\n");
    } catch {
      lines = [];
    }
    cache.set(file, lines);
  }
  const fileLines = cache.get(file)!;
  return fileLines[line - 1]?.trim() ?? "";
}

// ---- Query helpers ----------------------------------------------------------

/** Return the line costs for a given file (for annotations). */
export function linesForFile(summary: ProfileSummary, filePath: string): Map<number, LineCost> {
  const result = new Map<number, LineCost>();
  for (const l of summary.lines) {
    const absPath = path.resolve(summary.sourceRoot, l.file);
    if (absPath === filePath) {
      result.set(l.line, l);
    }
  }
  return result;
}

/** Format a kind breakdown as a compact string. */
export function formatKinds(kinds: Map<ConstraintKind, number>): string {
  const parts: string[] = [];
  for (const [kind, count] of [...kinds.entries()].sort((a, b) => b[1] - a[1])) {
    parts.push(`${count} ${kind}`);
  }
  return parts.join(", ");
}

/** Format a short inline annotation, e.g. "12c (8 Mul, 4 Bool)". */
export function formatInline(line: LineCost): string {
  if (line.total === 0) return "";
  const detail = formatKinds(line.kinds);
  return `${line.total}c (${detail})`;
}

// ---- Gadget cost aggregation -------------------------------------------------

/** Aggregated cost for a named function/gadget call. */
export interface GadgetCost {
  name: string;
  total: number;
  kinds: Map<ConstraintKind, number>;
}

/** Aggregate constraint costs by the top-level function name from chain data.
 *  Returns gadgets sorted by cost descending. */
export function gadgetCosts(summary: ProfileSummary): GadgetCost[] {
  const map = new Map<string, { total: number; kinds: Map<ConstraintKind, number> }>();

  for (const line of summary.lines) {
    for (const [chainFn, count] of line.chains) {
      // Skip the entry `circuit` function itself; only show gadget calls
      if (chainFn === "(top-level)") continue;
      const entry = map.get(chainFn) ?? { total: 0, kinds: new Map() };
      if (!map.has(chainFn)) map.set(chainFn, entry);
      entry.total += count;
      // Approximate: assign all of this line's kinds to this gadget
      // (a single line is typically dominated by one call chain)
      for (const [kind, kc] of line.kinds) {
        entry.kinds.set(kind, (entry.kinds.get(kind) ?? 0) + kc);
      }
    }
  }

  const result: GadgetCost[] = [];
  for (const [name, { total, kinds }] of map) {
    result.push({ name, total, kinds });
  }
  result.sort((a, b) => b.total - a.total);
  return result;
}

/** Check if a line's constraints include hints (HintPin kind). */
export function hasHints(line: LineCost): boolean {
  return (line.kinds.get("HintPin") ?? 0) > 0;
}

// ---- Circuit metadata -------------------------------------------------------

/** Variable visibility from metadata.json. */
export interface InputMeta {
  name: string;
  role: "public" | "private" | "derived";
}

/** Circuit-level metadata written alongside profile.json. */
export interface CircuitMetadata {
  field: string;
  num_vars: number;
  num_constraints: number;
  num_witness_ops: number;
  inputs: InputMeta[];
}

/** Load metadata.json from the same directory as profile.json. */
export function loadMetadata(profilePath: string): CircuitMetadata | null {
  const dir = path.dirname(profilePath);
  const metaPath = path.join(dir, "metadata.json");
  try {
    const text = fs.readFileSync(metaPath, "utf-8");
    return JSON.parse(text) as CircuitMetadata;
  } catch {
    return null;
  }
}
