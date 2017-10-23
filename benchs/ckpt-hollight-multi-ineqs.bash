#!/usr/bin/env bash
set -meu
# Erik Martin-Dorel, 2017

function die_hard() {
    echo -e "$@" >&2
    exit 1
}

function stderr() {
    echo -e "$@" >&2
}

function usage() {
    cat >&2 <<EOF
Usage:
$ $(basename "$0") HOLLIGHT_DIR
EOF
}

function pause() {
    read -r -p 'Press Enter to continue...'
}

function ckpt-exit() {
    fi="$1"
    stderr "\n$ dmtcp_command --checkpoint"
    dmtcp_command --checkpoint || true
    sleep 1s
    exec 3>&-
    rm -f "$fi"
    stderr "The End."
}

# Possible enhancement: replace output file with a fifo to earn space
function main() {
    # dmtcp=(../dmtcp-multi/dmtcp_restart_script.sh --ckptdir ./) # --ckptdir doesn't seem to work
    dmtcp=(../dmtcp-multi/dmtcp_restart_script.sh)
    # mlargs=(/usr/bin/ocaml -I +../camlp5)
    mlcode='#use "../Formal_ineqs/make.ml";;
print_endline "Done.";;'
    subdir="dmtcp-multi-ineqs"

    if [[ $# -lt 1 ]]; then
	usage
	exit 0
    fi
    export HOLLIGHT_DIR="${1%/}"
    if [[ ! -d "$HOLLIGHT_DIR" ]]; then
	die_hard "Error: directory '$HOLLIGHT_DIR' doesn't exist."
    fi
    if [[ -d "$HOLLIGHT_DIR/$subdir" ]]; then
	die_hard "Error: directory '$HOLLIGHT_DIR/$subdir' already exists."
    fi

    cd "$HOLLIGHT_DIR"
    mkdir "$subdir" && cd "$subdir"
    fi="$PWD/input"
    out="$PWD/output"

    if [[ ! -p "$fi" ]]; then
	mkfifo "$fi"
    else
	stderr "Info: fifo '$fi' already exists."
    fi
    if [[ -r "$out" ]]; then
	stderr "Info: file '$out' already exists, saving..."
	cp --backup=t -fv "$out" "$out"
    fi
    >"$out"

    trap 'ckpt-exit "$fi"' EXIT

    stderr "
The script is about to send the code below to an OCaml REPL:
================================================================
$mlcode
================================================================
Additional input can be send:
  echo 'print_endline \"OK\";;' >'$fi'
The output is shown below by:
  tail -f '$out'
In the very end, type ^C to automatically checkpoint & exit.
"
    pause

    export DMTCP_CHECKPOINT_DIR=$(readlink -f .)
    cat "$fi" | "${dmtcp[@]}" >"$out" &
    exec 3>"$fi"
    echo "$mlcode" > "$fi"
    tail -f "$out"
}

main "$@"
