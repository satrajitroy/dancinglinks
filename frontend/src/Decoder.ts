export type DecodedRow = Record<string, unknown>;
export type decodeSolutions = DecodedRow[];

function intParam(params: URLSearchParams, name: string, fallback?: number): number {
  const raw = params.get(name);
  if (raw == null || raw === "") {
    if (fallback !== undefined) return fallback;
    throw new Error(`Missing required parameter: ${name}`);
  }

  const n = Number(raw);
  if (!Number.isInteger(n) || n < 0) {
    throw new Error(`Parameter ${name} must be a non-negative integer`);
  }

  return n;
}

function range(n: number): number[] {
  return Array.from({ length: n }, (_, i) => i);
}

function rowsCount(R: number, r: number): number {
  return R * r;
}

function colsCount(C: number, c: number): number {
  return C * c;
}

function boxSize(r: number, c: number): number {
  return r * c;
}

function alphabetSize(R: number, C: number, r: number, c: number): number {
  return Math.max(rowsCount(R, r), colsCount(C, c), boxSize(r, c));
}

function combinationsFrom(k: number, start: number, n: number): number[][] {
  if (k === 0) return [[]];

  const out: number[][] = [];
  for (let v = start; v < n; v++) {
    for (const rest of combinationsFrom(k - 1, v + 1, n)) {
      out.push([v, ...rest]);
    }
  }
  return out;
}

function combinations(k: number, n: number): number[][] {
  return combinationsFrom(k, 0, n);
}

function sum(xs: number[]): number {
  return xs.reduce((a, b) => a + b, 0);
}

function nonincreasing(xs: number[]): boolean {
  for (let i = 1; i < xs.length; i++) {
    if (xs[i] > xs[i - 1]) return false;
  }
  return true;
}

function partitionsBounded(fuel: number, n: number, maxPart: number): number[][] {
  if (fuel === 0) return [];
  if (n === 0) return [[]];

  const out: number[][] = [];

  for (let x = 1; x <= maxPart; x++) {
    const nextN = Math.max(0, n - x);
    for (const rest of partitionsBounded(fuel - 1, nextN, x)) {
      out.push([x, ...rest]);
    }
  }

  return out;
}

function partitionsOf(n: number): number[][] {
  return partitionsBounded(n + 1, n, n).filter(
    (xs) => sum(xs) === n && nonincreasing(xs)
  );
}

function partitionsOfK(n: number, k: number): number[][] {
  return partitionsBounded(n + 1, n, n).filter(
    (xs) => sum(xs) === n && nonincreasing(xs) && xs.length === k
  );
}

function subsets(xs: number[]): number[][] {
  if (xs.length === 0) return [[]];

  const [x, ...rest] = xs;
  const ss = subsets(rest);
  return ss.concat(ss.map((s) => [x, ...s]));
}

function nonemptySubsets(xs: number[]): number[][] {
  return subsets(xs).filter((s) => s.length > 0);
}

function generatedMultiset(n: number, labelCount: number): number[] {
  if (labelCount === 0) return [];
  return range(n).map((i) => i % labelCount);
}

function decodeSudokuId(id: number, params: URLSearchParams): DecodedRow {
  const R = intParam(params, "R");
  const C = intParam(params, "C");
  const r = intParam(params, "r");
  const c = intParam(params, "c");

  const cols = colsCount(C, c);
  const alpha = alphabetSize(R, C, r, c);

  const row = Math.floor(id / (cols * alpha));
  const rem = id % (cols * alpha);
  const col = Math.floor(rem / alpha);
  const sym = rem % alpha;

  return {
    kind: "sudoku-placement",
    id,
    row,
    col,
    symbol: sym
  };
}

function decodeQueenId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  return {
    kind: "queen",
    id,
    row: Math.floor(id / n),
    col: id % n
  };
}

function decodeLangfordId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const base = 2 * n;
  const k = Math.floor(id / base) + 1;
  const start = id % base;
  const second = start + k + 1;

  return {
    kind: "langford-placement",
    id,
    value: k,
    positions: [start, second]
  };
}

function decodeTupleLikeId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  return {
    kind: "assignment",
    id,
    slot: Math.floor(id / n),
    value: id % n
  };
}

function decodeCombinationId(id: number, params: URLSearchParams): DecodedRow {
  const k = intParam(params, "k");
  const n = intParam(params, "n");
  const xs = combinations(k, n)[id];

  return {
    kind: "combination",
    id,
    values: xs ?? null
  };
}

function decodePartitionId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const xs = partitionsOf(n)[id];

  return {
    kind: "integer-partition",
    id,
    partition: xs ?? null
  };
}

function decodePartitionKId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const k = intParam(params, "k");
  const xs = partitionsOfK(n, k)[id];

  return {
    kind: "integer-partition-k",
    id,
    partition: xs ?? null
  };
}

function decodeSetPartitionId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const block = nonemptySubsets(range(n))[id];

  return {
    kind: "set-block",
    id,
    block: block ?? null
  };
}

function decodeSetPartitionKId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const blockCount = 2 ** n;

  const slot = Math.floor(id / blockCount);
  const blockId = id % blockCount;
  const block = nonemptySubsets(range(n))[blockId];

  return {
    kind: "labeled-set-block",
    id,
    slot,
    blockId,
    block: block ?? null
  };
}

function decodeMultisetPartitionId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const labelCount = intParam(params, "label_count", n);
  const values = generatedMultiset(n, labelCount);
  const occurrenceBlock = nonemptySubsets(range(n))[id];

  return {
    kind: "multiset-block",
    id,
    occurrences: occurrenceBlock ?? null,
    values: occurrenceBlock?.map((i) => values[i]) ?? null
  };
}

function decodeMultisetPartitionKId(id: number, params: URLSearchParams): DecodedRow {
  const n = intParam(params, "n");
  const labelCount = intParam(params, "label_count", n);
  const values = generatedMultiset(n, labelCount);

  const blockCount = 2 ** n;
  const slot = Math.floor(id / blockCount);
  const blockId = id % blockCount;
  const occurrenceBlock = nonemptySubsets(range(n))[blockId];

  return {
    kind: "labeled-multiset-block",
    id,
    slot,
    blockId,
    occurrences: occurrenceBlock ?? null,
    values: occurrenceBlock?.map((i) => values[i]) ?? null
  };
}

function decodeWarehouseId(id: number, params: URLSearchParams): DecodedRow {
  const nSources = intParam(params, "n_sources");

  return {
    kind: "warehouse-row",
    id,
    witness: Math.floor(id / nSources),
    source: id % nSources
  };
}

function decodeWaerdenId(id: number): DecodedRow {
  return {
    kind: "waerden-good-coloring-row",
    id,
    note: "Row id indexes one generated AP-avoiding coloring."
  };
}

function decodeRowId(api: string, id: number, params: URLSearchParams): DecodedRow {
  switch (api) {
    case "nqueens":
      return decodeQueenId(id, params);

    case "langford":
      return decodeLangfordId(id, params);

    case "tuple":
    case "permutation":
      return decodeTupleLikeId(id, params);

    case "combination":
      return decodeCombinationId(id, params);

    case "partition":
      return decodePartitionId(id, params);

    case "partition_k":
      return decodePartitionKId(id, params);

    case "set_partition_generated":
      return decodeSetPartitionId(id, params);

    case "set_partition_k_generated":
      return decodeSetPartitionKId(id, params);

    case "multiset_partition_generated":
      return decodeMultisetPartitionId(id, params);

    case "multiset_partition_k_generated":
      return decodeMultisetPartitionKId(id, params);

    case "sudoku_exact":
    case "sudoku_at_most":
      return decodeSudokuId(id, params);

    case "warehouse_guaranteed":
    case "warehouse_guaranteed_colored":
      return decodeWarehouseId(id, params);

    case "waerden":
      return decodeWaerdenId(id);

    default:
      return {
        kind: "raw-row-id",
        id
      };
  }
}

export function decodeSolutions(
  api: string,
  params: URLSearchParams,
  solutions: number[][]
): decodeSolutions[] {
  return solutions.map((solution) =>
    solution.map((id) => decodeRowId(api, id, params))
  );
}

export function mathematicalResult(
  api: string,
  params: URLSearchParams,
  rowIdSolutions: number[][]
): unknown {
  switch (api) {
    case "partition": {
      const n = intParam(params, "n");
      const parts = partitionsOf(n);

      return rowIdSolutions.map((sol) => {
        const id = sol[0];
        return parts[id] ?? null;
      });
    }

    case "partition_k": {
      const n = intParam(params, "n");
      const k = intParam(params, "k");
      const parts = partitionsOfK(n, k);

      return rowIdSolutions.map((sol) => {
        const id = sol[0];
        return parts[id] ?? null;
      });
    }

    case "combination": {
      const k = intParam(params, "k");
      const n = intParam(params, "n");
      const combos = combinations(k, n);

      return rowIdSolutions.map((sol) => {
        const id = sol[0];
        return combos[id] ?? null;
      });
    }

    case "nqueens": {
      const n = intParam(params, "n");

      // Return queen columns by row.
      // Example: [1,3,0,2]
      return rowIdSolutions.map((sol) =>
        sol.map((id) => id % n)
      );
    }

    case "langford": {
      const n = intParam(params, "n");
      const base = 2 * n;

      return rowIdSolutions.map((sol) => {
        const positions = Array(2 * n).fill(null);

        for (const id of sol) {
          const value = Math.floor(id / base) + 1;
          const start = id % base;
          const second = start + value + 1;

          if (start < positions.length) positions[start] = value;
          if (second < positions.length) positions[second] = value;
        }

        return positions;
      });
    }

    case "tuple":
    case "permutation": {
      const n = intParam(params, "n");

      // Return selected values by slot.
      return rowIdSolutions.map((sol) =>
        sol.map((id) => id % n)
      );
    }

    case "set_partition_generated": {
      const n = intParam(params, "n");
      const blocks = nonemptySubsets(range(n));

      return rowIdSolutions.map((sol) =>
        sol.map((id) => blocks[id] ?? null)
      );
    }

    case "set_partition_k_generated": {
      const n = intParam(params, "n");
      const blocks = nonemptySubsets(range(n));
      const blockCount = 2 ** n;

      return rowIdSolutions.map((sol) =>
        sol.map((id) => {
          const blockId = id % blockCount;
          return blocks[blockId] ?? null;
        })
      );
    }

    case "multiset_partition_generated": {
      const n = intParam(params, "n");
      const labelCount = intParam(params, "label_count", n);
      const values = generatedMultiset(n, labelCount);
      const blocks = nonemptySubsets(range(n));

      return rowIdSolutions.map((sol) =>
        sol.map((id) => {
          const occs = blocks[id] ?? [];
          return occs.map((i) => values[i]);
        })
      );
    }

    case "multiset_partition_k_generated": {
      const n = intParam(params, "n");
      const labelCount = intParam(params, "label_count", n);
      const values = generatedMultiset(n, labelCount);
      const blocks = nonemptySubsets(range(n));
      const blockCount = 2 ** n;

      return rowIdSolutions.map((sol) =>
        sol.map((id) => {
          const blockId = id % blockCount;
          const occs = blocks[blockId] ?? [];
          return occs.map((i) => values[i]);
        })
      );
    }

    case "sudoku_exact":
    case "sudoku_at_most": {
      const R = intParam(params, "R");
      const C = intParam(params, "C");
      const r = intParam(params, "r");
      const c = intParam(params, "c");

      const cols = colsCount(C, c);
      const alpha = alphabetSize(R, C, r, c);

      return rowIdSolutions.map((sol) =>
        sol.map((id) => {
          const row = Math.floor(id / (cols * alpha));
          const rem = id % (cols * alpha);
          const col = Math.floor(rem / alpha);
          const sym = rem % alpha;
          return [row, col, sym];
        })
      );
    }

    case "warehouse_guaranteed":
    case "warehouse_guaranteed_colored": {
      const nSources = intParam(params, "n_sources");

      return rowIdSolutions.map((sol) =>
        sol.map((id) => ({
          witness: Math.floor(id / nSources),
          source: id % nSources
        }))
      );
    }

    case "waerden": {
      // Unless we expose a coloring-row decoder from Rocq,
      // this remains an index into generated good colorings.
      return rowIdSolutions.map((sol) => sol.map((id) => id));
    }

    default:
      return rowIdSolutions;
  }
}