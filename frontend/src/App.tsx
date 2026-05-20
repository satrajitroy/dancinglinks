import React, { useMemo, useState } from "react";
import { runApiFromUrl } from "./API";

const BASE = import.meta.env.BASE_URL;

function href(path: string): string {
  return `${BASE}${path.replace(/^\/+/, "")}`;
}

function apiHref(api: string, params: [string, string][]): string {
  const q = new URLSearchParams();
  q.set("api", api);

  for (const [name, value] of params) {
    q.set(name, value);
  }

  return `${BASE}?${q.toString()}`;
}

type ParamSpec = {
  name: string;
  defaultValue: string;
  hint?: string;
};

type ApiSpec = {
  id: string;
  title: string;
  description: string;
  params: ParamSpec[];
  note?: string;
};

const API_SPECS: ApiSpec[] = [
  {
    id: "nqueens",
    title: "N-Queens",
    description: "Place n queens on an n×n board so that no two attack each other.",
    params: [
      { name: "n", defaultValue: "4" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "langford",
    title: "Langford pairs",
    description:
      "Arrange two copies of each number 1..n so the two copies of k are separated by k positions.",
    params: [
      { name: "n", defaultValue: "3", hint: "Solutions exist for n ≡ 0 or 3 mod 4." },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "waerden",
    title: "Van der Waerden colorings",
    description:
      "Generate q-colorings of 0..n−1 that avoid monochromatic arithmetic progressions of length k.",
    params: [
      { name: "n", defaultValue: "3" },
      { name: "q", defaultValue: "2" },
      { name: "k", defaultValue: "3" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "tuple",
    title: "Tuples",
    description: "Generated tuple universe encoded as an exact-cover problem.",
    params: [
      { name: "n", defaultValue: "3" },
      { name: "k", defaultValue: "2" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "permutation",
    title: "Permutations",
    description: "Generate ordered selections without repetition.",
    params: [
      { name: "n", defaultValue: "4" },
      { name: "k", defaultValue: "2" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "combination",
    title: "Combinations",
    description: "Generate unordered selections.",
    params: [
      { name: "n", defaultValue: "5" },
      { name: "k", defaultValue: "3" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "partition",
    title: "Integer partitions",
    description: "Generate integer partitions of n.",
    params: [
      { name: "n", defaultValue: "5" },
      { name: "fuel", defaultValue: "20" }
    ]
  },
  {
    id: "partition_k",
    title: "Integer partitions into k parts",
    description: "Generate integer partitions of n using exactly k parts.",
    params: [
      { name: "n", defaultValue: "5" },
      { name: "k", defaultValue: "2" },
      { name: "fuel", defaultValue: "20" }
    ]
  },
  {
    id: "set_partition_generated",
    title: "Set partitions",
    description: "Generate partitions of a finite set.",
    params: [
      { name: "n", defaultValue: "4" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "set_partition_k_generated",
    title: "Set partitions into k blocks",
    description:
      "Generate set partitions using exactly k blocks. This labeled-block encoding may grow quickly.",
    params: [
      { name: "n", defaultValue: "5" },
      { name: "k", defaultValue: "2" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
{
  id: "multiset_partition_generated",
  title: "Multiset partitions",
  description: "Generate partitions of a multiset-style universe.",
  params: [
    { name: "n", defaultValue: "4" },
    { name: "label_count", defaultValue: "2" },
    { name: "fuel", defaultValue: "20" }
  ]
},
{
  id: "multiset_partition_k_generated",
  title: "Multiset partitions into k parts",
  description: "Generate multiset partitions using exactly k parts.",
  params: [
    { name: "n", defaultValue: "4" },
    { name: "k", defaultValue: "2" },
    { name: "label_count", defaultValue: "2" },
    { name: "fuel", defaultValue: "20" }
  ]
},
{
  id: "sudoku_exact",
  title: "Exact generalized Sudoku",
  description:
    "Sudoku-like exact-cover encoding where cell, row-symbol, column-symbol, and box-symbol constraints are primary.",
  params: [
    { name: "R", defaultValue: "2", hint: "Block/grid row factor." },
    { name: "C", defaultValue: "2", hint: "Block/grid column factor." },
    { name: "r", defaultValue: "2", hint: "Box row size." },
    { name: "c", defaultValue: "2", hint: "Box column size." },
    { name: "fuel", defaultValue: "20" }
  ]
},
{
  id: "sudoku_at_most",
  title: "At-most generalized Sudoku",
  description:
    "Sudoku-like encoding with cells as primary constraints and row/column/box symbol constraints as at-most-once constraints.",
  note:
    "This API is kept as a modeling example, but nontrivial cases that truly exploit at-most-once constraints usually generate search spaces too large for the browser demo.",
  params: [
    { name: "R", defaultValue: "2", hint: "Block/grid row factor." },
    { name: "C", defaultValue: "2", hint: "Block/grid column factor." },
    { name: "r", defaultValue: "2", hint: "Box row size." },
    { name: "c", defaultValue: "2", hint: "Box column size." },
    { name: "fuel", defaultValue: "20" }
  ]
},
  {
    id: "warehouse_guaranteed",
    title: "Guaranteed warehouse",
    description:
      "Generated warehouse/scheduling-style problem with at least k intended witness solutions.",
    params: [
      { name: "n_items", defaultValue: "12" },
      { name: "n_sources", defaultValue: "4" },
      { name: "k", defaultValue: "3" },
      { name: "fuel", defaultValue: "10" }
    ]
  },
  {
    id: "warehouse_guaranteed_colored",
    title: "Guaranteed colored warehouse",
    description:
      "Colored variant of the generated warehouse/scheduling-style problem.",
    params: [
      { name: "n_items", defaultValue: "12" },
      { name: "n_sources", defaultValue: "4" },
      { name: "n_product_colors", defaultValue: "3" },
      { name: "n_source_reqs", defaultValue: "2" },
      { name: "k", defaultValue: "3" },
      { name: "fuel", defaultValue: "10" }
    ]
  }
];

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

function ApiCard({ spec }: { spec: ApiSpec }) {
  const initial = Object.fromEntries(
    spec.params.map((p) => [p.name, p.defaultValue])
  ) as Record<string, string>;

  const [values, setValues] = useState<Record<string, string>>(initial);

  const url = apiHref(
    spec.id,
    spec.params.map((p) => [
      p.name,
      values[p.name] ?? p.defaultValue
    ])
  );

  return (
    <section
      style={{
        border: "1px solid #ddd",
        borderRadius: "12px",
        padding: "1rem",
        background: "#fff",
        boxShadow: "0 1px 4px rgba(0,0,0,0.06)",
        minWidth: 0
      }}
    >
      <h3 style={{ marginTop: 0 }}>{spec.title}</h3>

      <p style={{ marginBottom: "0.75rem", color: "#444", lineHeight: 1.45 }}>
        <code>{spec.id}</code> — {spec.description}
      </p>

      {spec.note ? (
        <p
          style={{
            marginTop: "-0.25rem",
            marginBottom: "0.75rem",
            padding: "0.6rem 0.75rem",
            borderRadius: "8px",
            background: "#fff8e1",
            border: "1px solid #e6d28a",
            color: "#5f4b00",
            fontSize: "0.9rem",
            lineHeight: 1.4
          }}
        >
          <strong>Browser note:</strong> {spec.note}
        </p>
      ) : null}

      <div
        style={{
          display: "grid",
          gridTemplateColumns: "repeat(auto-fit, minmax(140px, 1fr))",
          gap: "0.75rem",
          marginBottom: "0.75rem",
          minWidth: 0
        }}
      >
        {spec.params.map((param) => (
          <label
            key={param.name}
            style={{
              display: "grid",
              gap: "0.25rem",
              minWidth: 0
            }}
          >
            <span style={{ fontWeight: 600 }}>{param.name}</span>

            <input
              value={values[param.name] ?? ""}
              onChange={(e) =>
                setValues((old) => ({
                  ...old,
                  [param.name]: e.target.value
                }))
              }
              style={{
                width: "100%",
                minWidth: 0,
                boxSizing: "border-box",
                padding: "0.45rem",
                border: "1px solid #ccc",
                borderRadius: "6px",
                fontFamily: "monospace"
              }}
            />

            {param.hint ? (
              <small
                style={{
                  color: "#666",
                  overflowWrap: "anywhere",
                  lineHeight: 1.35
                }}
              >
                {param.hint}
              </small>
            ) : null}
          </label>
        ))}
      </div>

      <div
        style={{
          display: "flex",
          gap: "0.75rem",
          flexWrap: "wrap",
          alignItems: "center",
          minWidth: 0
        }}
      >
        <a
          href={url}
          style={{
            display: "inline-block",
            padding: "0.5rem 0.8rem",
            borderRadius: "8px",
            background: "#111",
            color: "white",
            textDecoration: "none",
            fontWeight: 700
          }}
        >
          Run
        </a>

        <code
          style={{
            display: "block",
            padding: "0.5rem",
            background: "#f5f5f5",
            borderRadius: "8px",
            overflowX: "auto",
            maxWidth: "100%",
            minWidth: 0,
            whiteSpace: "nowrap"
          }}
        >
          {url}
        </code>
      </div>
    </section>
  );
}

export default function App() {
  const search = window.location.search;
  const result = useMemo(() => runApiFromUrl(search), [search]);
  return (
      <main
        style={{
          maxWidth: "1500px",
          margin: "0 auto",
          padding: "2rem",
          fontFamily:
            'system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif'
        }}
      >
      <header style={{ marginBottom: "2rem" }}>
        <h1>GDance browser demo</h1>

        <p style={{ fontSize: "1.05rem", lineHeight: 1.5 }}>
          A Rocq-verified functional Dancing Links / Algorithm X solver with
          colored constraints. Each entry below shows the public API name,
          editable URL parameters, and a runnable example.
        </p>

        <p>
          <a href={href("README.md")}>README</a>
          {" · "}
          <a href={href("coqdoc/GDance.html")}>Rocq/coqdoc documentation</a>
        </p>
      </header>

      <section style={{ marginBottom: "2rem" }}>
        <h2>Public APIs</h2>

        <div
          style={{
            display: "grid",
            gridTemplateColumns: "repeat(auto-fit, minmax(330px, 1fr))",
            gap: "1rem"
          }}
        >
        <div
          style={{
            display: "grid",
            gridTemplateColumns: "repeat(auto-fit, minmax(260px, 1fr))",
            gap: "1rem"
          }}
        >
          {API_SPECS.map((spec) => (
            <ApiCard key={spec.id} spec={spec} />
          ))}
        </div>
        </div>
      </section>

      <section>
        <h2>Result</h2>

        <pre
          style={{
            background: "#f5f5f5",
            padding: "1rem",
            borderRadius: "8px",
            overflowX: "auto",
            whiteSpace: "pre",
            maxHeight: "75vh",
            fontSize: "0.9rem",
            lineHeight: 1.4
          }}
        >
          {compactJson(result, 2)}
        </pre>
      </section>

      <footer
        style={{
          marginTop: "2.5rem",
          paddingTop: "1rem",
          borderTop: "1px solid #ddd",
          color: "#555",
          fontSize: "0.95rem",
          lineHeight: 1.5
        }}
      >
        <p>
          <strong>Roadmap:</strong> The generic solver is proved sound for
          well-formed problems. A natural next step is proving that the public
          generated problem families are themselves well formed.
        </p>

        <p>
          GDance is free for research, education, and experimentation. Stars,
          feedback, citations, issue reports, and small donations are appreciated
          but never required.
        </p>
      </footer>

    </main>
  );
}