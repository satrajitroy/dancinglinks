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
rocq_doc

log "Building Melange target: dune build $DUNE_TARGET"

cd "$ROOT_DIR"
opam exec -- dune build "$DUNE_TARGET"

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