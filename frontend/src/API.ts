import * as GDance from "./generated/gdance.js";
import { mathematicalResult  } from "./Decoder";

export type ApiResult = {
  ok: boolean;
  api: string;
  params: Record<string, string>;
  result?: unknown;
  rawRowIds?: number[][];
  decoded?: unknown;
  error?: string;
};

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

function paramsObject(params: URLSearchParams): Record<string, string> {
  const out: Record<string, string> = {};
  params.forEach((value, key) => {
    out[key] = value;
  });
  return out;
}

/*
  Extracted Rocq nat:
    0       = O
    {_0:n}  = S n

  The earlier _0 error happens when a plain JS number like 10 is passed
  where extracted Rocq code expects this Peano shape.
*/
function toNat(n: number): any {
  let out: any = 0;
  for (let i = 0; i < n; i++) {
    out = { TAG: 0, _0: out };
  }
  return out;
}

function fromNat(n: any): number {
  if (typeof n === "number") {
    return n;
  }

  let out = 0;

  while (n !== 0) {
    if (n == null || typeof n !== "object" || !("_0" in n)) {
      throw new Error(`Malformed extracted nat: ${JSON.stringify(n)}`);
    }

    out++;
    n = n._0;
  }

  return out;
}

/*
  Extracted Rocq list:
    0                    = []
    { hd: x, tl: xs }     = x :: xs
*/
function listToArray(xs: any): any[] {
  const out: any[] = [];

  while (xs !== 0) {
    if (xs == null || typeof xs !== "object") {
      throw new Error(`Malformed extracted list: ${JSON.stringify(xs)}`);
    }

    // Melange/OCaml list encoding variant 1:
    //   { hd: x, tl: xs }
    if ("hd" in xs && "tl" in xs) {
      out.push(xs.hd);
      xs = xs.tl;
      continue;
    }

    // Melange/OCaml list encoding variant 2:
    //   { _0: x, _1: xs }
    if ("_0" in xs && "_1" in xs) {
      out.push(xs._0);
      xs = xs._1;
      continue;
    }

    throw new Error(
      `Unknown extracted list node shape: ${JSON.stringify(xs)}`
    );
  }

  return out;
}

function listListNatToArray(xs: any): number[][] {
  return listToArray(xs).map((inner) =>
    listToArray(inner).map(fromNat)
  );
}

function callPublic(name: string, ...args: number[]): number[][] {
  const publicApi = (GDance as any).PublicAPI;

  if (!publicApi) {
    throw new Error(
      `GDance.PublicAPI is missing. Did you re-extract the PublicAPI wrappers and rebuild Melange?`
    );
  }

  const fn = publicApi[name];

  if (typeof fn !== "function") {
    throw new Error(
      `Missing PublicAPI.${name}. Available: ${Object.keys(publicApi).sort().join(", ")}`
    );
  }

  const rocqArgs = args.map(toNat);

  /*
    Melange is emitting multi-arg functions as ordinary JS functions in your build,
    e.g. solve_ids(h,h0,fuel,p). So direct spread call is correct here.
  */
  const raw = fn(...rocqArgs);

  return listListNatToArray(raw);
}

export const publicApis = [
  "nqueens",
  "langford",
  "waerden",

  "tuple",
  "permutation",
  "combination",

  "partition",
  "partition_k",

  "set_partition_generated",
  "set_partition_k_generated",

  "multiset_partition_generated",
  "multiset_partition_k_generated",

  "sudoku_exact",
  "sudoku_at_most",

  "warehouse_guaranteed",
  "warehouse_guaranteed_colored"
] as const;

export function runApiFromUrl(search: string): ApiResult {
  const params = new URLSearchParams(search);
  const api = params.get("api") ?? "nqueens";

  try {
    const fuel = intParam(params, "fuel", 20);

    let result: number[][];

    switch (api) {
      case "nqueens": {
        const n = intParam(params, "n");
        result = callPublic("api_nqueens_ids", fuel, n);
        break;
      }

      case "langford": {
        const n = intParam(params, "n");
        result = callPublic("api_langford_ids", fuel, n);
        break;
      }

      case "waerden": {
        const n = intParam(params, "n");
        const q = intParam(params, "q");
        const k = intParam(params, "k");
        result = callPublic("api_waerden_ids", fuel, n, q, k);
        break;
      }

      case "tuple": {
        const k = intParam(params, "k");
        const n = intParam(params, "n");
        result = callPublic("api_tuple_ids", fuel, k, n);
        break;
      }

      case "permutation": {
        const k = intParam(params, "k");
        const n = intParam(params, "n");
        result = callPublic("api_permutation_ids", fuel, k, n);
        break;
      }

      case "combination": {
        const k = intParam(params, "k");
        const n = intParam(params, "n");
        result = callPublic("api_combination_ids", fuel, k, n);
        break;
      }

      case "partition": {
        const n = intParam(params, "n");
        result = callPublic("api_partition_ids", fuel, n);
        break;
      }

      case "partition_k": {
        const n = intParam(params, "n");
        const k = intParam(params, "k");
        result = callPublic("api_partition_k_ids", fuel, n, k);
        break;
      }

      case "set_partition_generated": {
        const n = intParam(params, "n");
        result = callPublic("api_set_partition_generated_ids", fuel, n);
        break;
      }

      case "set_partition_k_generated": {
        const k = intParam(params, "k");
        const n = intParam(params, "n");
        result = callPublic("api_set_partition_k_generated_ids", fuel, k, n);
        break;
      }

      case "multiset_partition_generated": {
        const n = intParam(params, "n");
        const label_count = intParam(params, "label_count");
        result = callPublic("api_multiset_partition_generated_ids", fuel, n, label_count);
        break;
      }

      case "multiset_partition_k_generated": {
        const k = intParam(params, "k");
        const n = intParam(params, "n");
        const label_count = intParam(params, "label_count");
        result = callPublic(
          "api_multiset_partition_k_generated_ids",
          fuel,
          k,
          n,
          label_count
        );
        break;
      }

      case "sudoku_exact": {
        const R = intParam(params, "R");
        const C = intParam(params, "C");
        const r = intParam(params, "r");
        const c = intParam(params, "c");
        result = callPublic("api_sudoku_exact_ids", fuel, R, C, r, c);
        break;
      }

      case "sudoku_at_most": {
        const R = intParam(params, "R");
        const C = intParam(params, "C");
        const r = intParam(params, "r");
        const c = intParam(params, "c");
        result = callPublic("api_sudoku_at_most_ids", fuel, R, C, r, c);
        break;
      }

      case "warehouse_guaranteed": {
        const n_items = intParam(params, "n_items");
        const n_sources = intParam(params, "n_sources");
        const k = intParam(params, "k");
        result = callPublic("api_warehouse_guaranteed_ids", fuel, n_items, n_sources, k);
        break;
      }

      case "warehouse_guaranteed_colored": {
        const n_items = intParam(params, "n_items");
        const n_sources = intParam(params, "n_sources");
        const n_product_colors = intParam(params, "n_product_colors");
        const n_source_reqs = intParam(params, "n_source_reqs");
        const k = intParam(params, "k");

        result = callPublic(
          "api_warehouse_guaranteed_colored_ids",
          fuel,
          n_items,
          n_sources,
          n_product_colors,
          n_source_reqs,
          k
        );
        break;
      }

      default:
        throw new Error(`Unknown api: ${api}`);
    }

  const rawRowIds = result;
  const showRaw = params.get("debug") === "1" || params.get("raw") === "1";
  const math = mathematicalResult(api, params, result);

  return {
    ok: true,
    api,
    params: paramsObject(params),
    result: math,
    ...(showRaw ? { rawRowIds } : {})
  };
  } catch (err: any) {
    return {
      ok: false,
      api,
      params: paramsObject(params),
      error: String(err?.stack || err?.message || err)
    };
  }
}