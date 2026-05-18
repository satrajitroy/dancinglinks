import React, { useMemo } from "react";
import { publicApis, runApiFromUrl } from "./API";

function exampleUrl(api: string, query: string) {
  return `/?api=${api}&${query}`;
}

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function containsPlainObjectBelow(value: unknown): boolean {
  if (value === null || typeof value !== "object") {
    return false;
  }

  if (Array.isArray(value)) {
    return value.some((x) => isPlainObject(x) || containsPlainObjectBelow(x));
  }

  return Object.values(value).some(
    (v) => isPlainObject(v) || containsPlainObjectBelow(v)
  );
}

function compactJson(value: unknown, indent = 2, level = 0): string {
  const pad = " ".repeat(level * indent);
  const nextPad = " ".repeat((level + 1) * indent);

  if (value === null || typeof value !== "object") {
    return JSON.stringify(value);
  }

  /*
    Arrays that contain no objects are leaf-like from a JSON-object perspective.
    Keep them horizontal.

    Examples:
      [1,3,0,2]
      [[1,3,0,2],[2,0,3,1]]
      [[[1],[2]],[[3],[4]]]
  */
  if (Array.isArray(value)) {
    if (!containsPlainObjectBelow(value)) {
      return JSON.stringify(value);
    }

    if (value.length === 0) {
      return "[]";
    }

    return (
      "[\n" +
      value
        .map((x) => nextPad + compactJson(x, indent, level + 1))
        .join(",\n") +
      "\n" +
      pad +
      "]"
    );
  }

  /*
    If this object has no child object anywhere below it, print the whole object
    horizontally, even if it contains arrays.

    Examples:
      {"api":"nqueens","n":"4","fuel":"10"}
      {"ok":true,"api":"partition_k","result":[[1,1,1,1,1]]}
      {"witness":0,"source":1}
  */
  if (!containsPlainObjectBelow(Object.values(value))) {
    return JSON.stringify(value);
  }

  const entries = Object.entries(value);

  if (entries.length === 0) {
    return "{}";
  }

  return (
    "{\n" +
    entries
      .map(
        ([k, v]) =>
          nextPad + JSON.stringify(k) + ": " + compactJson(v, indent, level + 1)
      )
      .join(",\n") +
    "\n" +
    pad +
    "}"
  );
}


export default function App() {
  const result = useMemo(() => runApiFromUrl(window.location.search), []);

  return (
    <main style={{ fontFamily: "system-ui, sans-serif", padding: "2rem" }}>
      <h1>GDance / DLX GET API Demo</h1>

      <p>
        Pass parameters in the URL query string. Example:
        <br />
        <code>?api=nqueens&amp;n=4&amp;fuel=10</code>
      </p>

      <h2>Public APIs</h2>
      <ul>
        {publicApis.map((api) => (
          <li key={api}>
            <code>{api}</code>
          </li>
        ))}
      </ul>

      <h2>Example links</h2>
      <ul>
        <li>
          <a href={exampleUrl("nqueens", "n=4&fuel=10")}>4-Queens</a>
        </li>
        <li>
          <a href={exampleUrl("langford", "n=3&fuel=10")}>Langford n=3</a>
        </li>
        <li>
          <a href={exampleUrl("waerden", "n=3&q=2&k=3&fuel=10")}>
            Van der Waerden n=3 q=2 k=3
          </a>
        </li>
        <li>
          <a href={exampleUrl("set_partition_generated", "n=3&fuel=10")}>
            Set partitions of 3
          </a>
        </li>
        <li>
          <a href={exampleUrl("warehouse_guaranteed", "n_items=4&n_sources=2&k=2&fuel=10")}>
            Guaranteed warehouse
          </a>
        </li>
        <li>
          <a href={exampleUrl("sudoku_exact", "R=2&C=1&r=1&c=2&fuel=10")}>
            Exact 2x2 Sudoku
          </a>
        </li>
      </ul>

      <h2>Result</h2>
      <pre
        style={{
          background: result.ok ? "#f5f5f5" : "#fff0f0",
          padding: "1rem",
          borderRadius: "8px",
          overflowX: "auto",
          whiteSpace: "pre-wrap"
        }}
      >
        {compactJson(result, null, 2)}
      </pre>
    </main>
  );
}