#!/usr/bin/env bash
set -Eeuo pipefail

###############################################################################
# Melange + React build script
#
# Assumed project shape:
#
#   .
#   ├── dune-project
#   ├── dune / src/... dune files with (melange.emit ...)
#   ├── web/
#   │   ├── package.json
#   │   ├── src/
#   │   └── dist/              # created by npm run build / Vite
#   └── scripts/
#       └── build-react.sh
#
# Override any variable from the shell:
#
#   FRONTEND_DIR=frontend ./scripts/build-react.sh
#   MELANGE_DEST=web/src/generated ./scripts/build-react.sh
#   DEPLOY_DIR=/var/www/html ./scripts/build-react.sh
#
###############################################################################

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/." && pwd)"

FRONTEND_DIR="${FRONTEND_DIR:-$ROOT_DIR/web}"
MELANGE_DEST="${MELANGE_DEST:-$FRONTEND_DIR/src/generated}"
WEB_DUNE_TARGET="@web/melange"
DUNE_TARGET="${DUNE_TARGET:-@melange}"
NPM_BUILD_SCRIPT="${NPM_BUILD_SCRIPT:-build}"
DEPLOY_DIR="${DEPLOY_DIR:-}"

# If you know the exact Melange output directory, set:
#
#   MELANGE_OUT=/path/to/project/_build/default/app/output
#
# Otherwise the script will try to auto-detect generated .js files.
MELANGE_OUT="${MELANGE_OUT:-}"

log() {
  printf '\n\033[1;34m==>\033[0m %s\n' "$*"
}

die() {
  printf '\n\033[1;31mERROR:\033[0m %s\n' "$*" >&2
  exit 1
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "Missing command: $1"
}

rocq_compile() {
  log "Compiling GDance.v to generate .vo/.glob"

  if command -v rocq >/dev/null 2>&1; then
    rocq compile GDance.v
  elif command -v coqc >/dev/null 2>&1; then
    coqc GDance.v
  else
    die "Neither rocq nor coqc was found"
  fi
}

copy_generated_ocaml() {
  log "Copying generated OCaml to native and web build directories"

  mkdir -p "$ROOT_DIR/exe" "$ROOT_DIR/web"

  if [ ! -f "$ROOT_DIR/src/gdance.ml" ]; then
    die "Missing generated file: $ROOT_DIR/src/gdance.ml"
  fi

  if [ ! -f "$ROOT_DIR/src/gdance.mli" ]; then
    die "Missing generated file: $ROOT_DIR/src/gdance.mli"
  fi

  cp "$ROOT_DIR/src/gdance.ml" "$ROOT_DIR/exe/gdance.ml"
  cp "$ROOT_DIR/src/gdance.mli" "$ROOT_DIR/exe/gdance.mli"

  cp "$ROOT_DIR/src/gdance.ml" "$ROOT_DIR/web/gdance.ml"
  cp "$ROOT_DIR/src/gdance.mli" "$ROOT_DIR/web/gdance.mli"
}

rocq_stats() {
  log "Generating Rocq build summary/stats"

  mkdir -p "$ROOT_DIR/src"
  mkdir -p "$ROOT_DIR/docs/stats"

  local stats="$ROOT_DIR/docs/stats/GDance-summary.md"
  local time_log="$ROOT_DIR/docs/stats/GDance-time.log"
  local profile_json="$ROOT_DIR/docs/stats/GDance-profile.json"

  {
    echo "# GDance build summary"
    echo
    echo "Generated: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
    echo
    echo "## Tool versions"
    echo
    echo '```text'
    if command -v rocq >/dev/null 2>&1; then
      rocq --version || true
    fi
    if command -v coqc >/dev/null 2>&1; then
      coqc --version || true
    fi
    if command -v dune >/dev/null 2>&1; then
      dune --version || true
    fi
    if command -v node >/dev/null 2>&1; then
      node --version || true
    fi
    if command -v npm >/dev/null 2>&1; then
      npm --version || true
    fi
    echo '```'
    echo
    echo "## Source size"
    echo
    echo '```text'
    wc -l "$ROOT_DIR/GDance.v" "$ROOT_DIR/README.md" 2>/dev/null || true
    echo '```'
    echo
    echo "## Rocq declarations"
    echo
    echo '```text'
    printf "Definitions: "; grep -Ec '^[[:space:]]*(Definition|Program Definition)\b' "$ROOT_DIR/GDance.v" || true
    printf "Fixpoints:    "; grep -Ec '^[[:space:]]*Fixpoint\b' "$ROOT_DIR/GDance.v" || true
    printf "Records:      "; grep -Ec '^[[:space:]]*Record\b' "$ROOT_DIR/GDance.v" || true
    printf "Inductives:   "; grep -Ec '^[[:space:]]*Inductive\b' "$ROOT_DIR/GDance.v" || true
    printf "Classes:      "; grep -Ec '^[[:space:]]*Class\b' "$ROOT_DIR/GDance.v" || true
    printf "Instances:    "; grep -Ec '^[[:space:]]*(Global Instance|Instance)\b' "$ROOT_DIR/GDance.v" || true
    printf "Lemmas:       "; grep -Ec '^[[:space:]]*Lemma\b' "$ROOT_DIR/GDance.v" || true
    printf "Theorems:     "; grep -Ec '^[[:space:]]*Theorem\b' "$ROOT_DIR/GDance.v" || true
    printf "Examples:     "; grep -Ec '^[[:space:]]*Example\b' "$ROOT_DIR/GDance.v" || true
    echo '```'
    echo
    echo "## Generated artifacts"
    echo
    echo '```text'
    ls -lh "$ROOT_DIR"/GDance.vo "$ROOT_DIR"/GDance.glob "$ROOT_DIR"/gdance.ml "$ROOT_DIR"/gdance.mli 2>/dev/null || true
    ls -lh "$ROOT_DIR"/frontend/src/generated/gdance.js 2>/dev/null || true
    echo '```'
    echo
    echo "## Timing"
    echo
    echo "Detailed command timing is in \`docs/stats/GDance-time.log\`."
    echo
    echo "## Profiling"
    echo
    echo "Detailed Rocq profiling trace is in \`docs/stats/GDance-profile.json\`."
  } > "$stats"

  log "Writing Rocq command timings to $time_log"

  if command -v rocq >/dev/null 2>&1; then
    rocq compile -time-file "$time_log" "$ROOT_DIR/GDance.v"
  elif command -v coqc >/dev/null 2>&1; then
    coqc -time-file "$time_log" "$ROOT_DIR/GDance.v"
  else
    die "Neither rocq nor coqc was found"
  fi

  log "Writing Rocq profile trace to $profile_json"

  if command -v rocq >/dev/null 2>&1; then
    rocq compile -profile "$profile_json" "$ROOT_DIR/GDance.v" || true
  elif command -v coqc >/dev/null 2>&1; then
    coqc -profile "$profile_json" "$ROOT_DIR/GDance.v" || true
  fi

  log "Rocq build summary written to $stats"
}

rocq_doc() {
  log "Generating Rocq documentation"

  mkdir -p "$ROOT_DIR/docs/coqdoc"
  mkdir -p "$ROOT_DIR/frontend/public/coqdoc"

  if command -v rocq >/dev/null 2>&1; then
    rocq doc --html -g -toc -d "$ROOT_DIR/docs/coqdoc" "$ROOT_DIR/GDance.v"
  elif command -v coqdoc >/dev/null 2>&1; then
    coqdoc --html -g -toc -d "$ROOT_DIR/docs/coqdoc" "$ROOT_DIR/GDance.v"
  else
    die "Neither rocq doc nor coqdoc was found"
  fi

  rsync -a --delete "$ROOT_DIR/docs/coqdoc/" "$ROOT_DIR/frontend/public/coqdoc/"
}

resolve_frontend_dir() {
  local requested="${FRONTEND_DIR:-frontend}"

  # If current directory itself looks like the frontend.
  if [ -f "package.json" ] && [ -d "src" ]; then
    pwd -P
    return 0
  fi

  # If FRONTEND_DIR exists relative to current directory.
  if [ -d "$requested" ]; then
    (cd "$requested" && pwd -P)
    return 0
  fi

  # If FRONTEND_DIR exists relative to project root.
  if [ -d "$ROOT_DIR/$requested" ]; then
    (cd "$ROOT_DIR/$requested" && pwd -P)
    return 0
  fi

  die "Could not find frontend directory. Tried: current dir, $requested, $ROOT_DIR/$requested"
}

###############################################################################
# Preconditions
###############################################################################

require_cmd opam
require_cmd dune
require_cmd npm
require_cmd find
require_cmd rsync

[ -f "$ROOT_DIR/dune-project" ] || die "No dune-project found at $ROOT_DIR"
[ -d "$FRONTEND_DIR" ] || die "FRONTEND_DIR does not exist: $FRONTEND_DIR"
[ -f "$FRONTEND_DIR/package.json" ] || die "No package.json found in $FRONTEND_DIR"



###############################################################################
# Activate OPAM environment
###############################################################################

log "Activating OPAM environment"

# This is safe even if the shell is already inside the switch.
eval "$(opam env)"

###############################################################################
# Clean stale generated JS destination
###############################################################################

log "Preparing Melange destination: $MELANGE_DEST"

rm -rf "$MELANGE_DEST"
mkdir -p "$MELANGE_DEST"

###############################################################################
# Build Melange
###############################################################################

rocq_compile
rocq_stats
copy_generated_ocaml
rocq_doc

log "Copying README.md into frontend public assets"
mkdir -p "$ROOT_DIR/frontend/public"
cp "$ROOT_DIR/README.md" "$ROOT_DIR/frontend/public/README.md"

log "Building Melange target: dune build $WEB_DUNE_TARGET"

cd "$ROOT_DIR"
opam exec -- dune build "$WEB_DUNE_TARGET"

log "Building native exe"
opam exec -- dune build ./exe/xcvr.exe

log "Copying native executable to repo root"

NATIVE_EXE="$ROOT_DIR/_build/default/exe/xcvr.exe"

if [ ! -f "$NATIVE_EXE" ]; then
  die "Native executable not found: $NATIVE_EXE"
fi

cp "$NATIVE_EXE" "$ROOT_DIR/xcvr"
chmod 755 "$ROOT_DIR/xcvr"

###############################################################################
# Locate Melange output
###############################################################################

if [ -z "$MELANGE_OUT" ]; then
  log "Auto-detecting Melange output directory"

  # Find directories under _build/default that contain generated JS.
  # Prefer directories containing more than one JS file.
  MELANGE_OUT="$(
    find "$ROOT_DIR/_build/default" -type f -name '*.js' \
      -not -path '*/node_modules/*' \
      -not -path '*/.cache/*' \
      -printf '%h\n' 2>/dev/null \
    | sort \
    | uniq -c \
    | sort -nr \
    | awk 'NR==1 {print $2}'
  )"

  [ -n "$MELANGE_OUT" ] || die "Could not auto-detect Melange JS output. Set MELANGE_OUT manually."
fi

[ -d "$MELANGE_OUT" ] || die "MELANGE_OUT is not a directory: $MELANGE_OUT"

log "Using Melange output: $MELANGE_OUT"

###############################################################################
# Copy generated JS into React source tree
###############################################################################

log "Copying Melange JS to React app"

rsync -a --delete \
  --include='*/' \
  --include='*.js' \
  --include='*.mjs' \
  --include='*.json' \
  --exclude='*' \
  "$MELANGE_OUT/" \
  "$MELANGE_DEST/"

###############################################################################
# Install frontend dependencies
###############################################################################

log "Installing frontend dependencies"

cd "$FRONTEND_DIR"

if [ -f package-lock.json ]; then
  npm ci
else
  npm install
fi

###############################################################################
# Build React/Vite app
###############################################################################

log "Building React app: npm run $NPM_BUILD_SCRIPT"

FRONTEND_DIR="$(resolve_frontend_dir)"

if [ "$(pwd -P)" != "$FRONTEND_DIR" ]; then
  cd "$FRONTEND_DIR"
fi

log "Frontend directory: $(pwd -P)"

npm run "$NPM_BUILD_SCRIPT"

if [ ! -d "dist" ]; then
  die "React build did not produce $(pwd -P)/dist"
fi

if [ -n "$DEPLOY_DIR" ]; then
  log "Deploying dist/ to $DEPLOY_DIR"
  mkdir -p "$DEPLOY_DIR"
  rsync -a --delete "dist/" "$DEPLOY_DIR/"
else
  log "No DEPLOY_DIR set; build artifact is at $(pwd)/dist"
fi

###############################################################################
# Optional deployment copy
###############################################################################

if [ -n "$DEPLOY_DIR" ]; then
  log "Deploying dist/ to $DEPLOY_DIR"

  mkdir -p "$DEPLOY_DIR"
  rsync -a --delete "$FRONTEND_DIR/dist/" "$DEPLOY_DIR/"
else
  log "No DEPLOY_DIR set; build artifact is at $FRONTEND_DIR/dist"
fi

log "Done"