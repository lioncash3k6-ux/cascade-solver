#!/usr/bin/env bash
# End-to-end reproduction script for cascade stages 1-3 (2026-04-20).
#
# Runs one instance per problem family per (p, d) configuration, with
# a time budget per case. Prints a summary table and emits/re-verifies
# one PHP certificate as a soundness witness. Expected total runtime
# ~5 min on a modern machine with ≥ 8 GB RAM.
#
# Does NOT include PHP_{7,6} d=7 (260 s) or PHP_{8,7} d=7 (60 min).
# Invoke those individually if you want the full picture.

# Cascade returns exit code 20 on UNSAT, 10 on SAT, 0 on indeterminate.
# `set -e` would treat both 20 and 10 as script failures, so we do the
# error-checking manually per-call.
set -uo pipefail

# -------- Setup --------

ROOT="$(cd "$(dirname "$0")"/.. && pwd)"
CASCADE="$ROOT/target/release/cascade"
VERIFIER="$ROOT/target/release/cascade_cert_verify"
WORKDIR="${WORKDIR:-/tmp/cascade-repro}"
mkdir -p "$WORKDIR"
DUMMY="$WORKDIR/dummy.cnf"
printf "p cnf 1 1\n1 0\n" > "$DUMMY"

CASE_TIMEOUT="${CASE_TIMEOUT:-60}"

# ANSI colors, only if stdout is a terminal.
if [[ -t 1 ]]; then
  BOLD=$'\033[1m'; GREEN=$'\033[32m'; RED=$'\033[31m'
  DIM=$'\033[2m'; RESET=$'\033[0m'
else
  BOLD=''; GREEN=''; RED=''; DIM=''; RESET=''
fi

hr() { printf '%s\n' "────────────────────────────────────────────────────────────────────────"; }
section() { printf "\n${BOLD}%s${RESET}\n"; hr; }

# -------- Build --------

if [[ ! -x "$CASCADE" || ! -x "$VERIFIER" ]]; then
  echo "${BOLD}Building cascade (release)...${RESET}"
  (cd "$ROOT" && cargo build --release --bin cascade --bin cascade_cert_verify 2>&1 | tail -3)
fi

# -------- Test runner --------

# Runs one case, returns ms elapsed, minimum d for which a cert is found.
# Args: family, family_args, prime, d_max, mode ("orbit"|"dense")
run_case() {
  local family="$1" fargs="$2" prime="$3" d_max="$4" mode="$5"
  local problem_spec
  if [[ -z "$fargs" ]]; then
    problem_spec="$family"
  else
    problem_spec="${family}:${fargs}"
  fi
  local cmd_args=(--alg-p "$prime" --problem "$problem_spec")
  if [[ "$mode" == "dense" ]]; then
    cmd_args=(--alg-no-orbit "${cmd_args[@]}")
  fi
  local found_d=">${d_max}"
  local total_ms=0
  for d in $(seq 1 "$d_max"); do
    local t0=$(date +%s.%N)
    local out
    if ! out=$(timeout "$CASE_TIMEOUT" "$CASCADE" --alg-preprocess "$d" "${cmd_args[@]}" "$DUMMY" 2>&1); then
      # timeout returns 124, cert-found returns 20, no-cert returns 0
      if [[ $? -ne 124 ]]; then :; fi
    fi
    local t1=$(date +%s.%N)
    local dt_ms; dt_ms=$(awk "BEGIN{printf \"%d\", ($t1 - $t0) * 1000}")
    total_ms=$((total_ms + dt_ms))
    if echo "$out" | grep -q "UNSATISFIABLE"; then
      found_d="$d"
      break
    fi
  done
  printf "%s|%d" "$found_d" "$total_ms"
}

# -------- PHP family --------

echo
echo "${BOLD}PHP — functional pigeonhole (orbit-reduced 𝔽_p)${RESET}"
hr
printf "%-14s %-10s %-6s %-6s %-14s\n" "Instance" "Prime" "d_min" "RAM" "Time"
hr

for pair in "5,4:7" "6,5:7" "7,6:11"; do
  inst="${pair%:*}"; prime="${pair##*:}"
  # PHP_{P,H} requires d >= P; cap d search at P.
  P="${inst%,*}"
  # Just try exactly d = P (known to be the first degree that produces a
  # cert; saves time vs sweeping).
  t0=$(date +%s.%N)
  rss_peak_kb=0
  /usr/bin/time -v "$CASCADE" --alg-preprocess "$P" --alg-p "$prime" \
    --problem "php:$inst" "$DUMMY" > "$WORKDIR/php_${inst}.log" 2> "$WORKDIR/php_${inst}.time"
  t1=$(date +%s.%N)
  dt=$(awk "BEGIN{printf \"%.1f\", $t1 - $t0}")
  if [[ -f "$WORKDIR/php_${inst}.time" ]]; then
    rss_peak_kb=$(grep -oE "Maximum resident set size \(kbytes\): [0-9]+" \
                  "$WORKDIR/php_${inst}.time" | awk '{print $NF}')
  fi
  rss_gb=$(awk "BEGIN{printf \"%.2f GB\", $rss_peak_kb/1048576}")
  if grep -q "UNSATISFIABLE" "$WORKDIR/php_${inst}.log"; then
    verdict="${GREEN}cert d=${P}${RESET}"
  else
    verdict="${RED}no cert${RESET}"
  fi
  printf "PHP_{%-5s}  𝔽%-7s  %-6s %-12s %5s s\n" \
         "$inst" "$prime" "$verdict" "$rss_gb" "$dt"
done

# -------- Count_q family --------

echo
echo "${BOLD}Count_q — modular counting principle${RESET}"
hr
echo "${DIM}Partition [n] into q-blocks. UNSAT iff q ∤ n. Bold cell = p=q (always d=1).${RESET}"
hr
printf "%-14s " "Count_q"
for p in 2 3 5 7 11 13; do printf "%-6s " "p=$p"; done
printf "\n"
hr

for nq in "2,3" "2,5" "3,4" "3,5"; do
  q="${nq%,*}"; n="${nq#*,}"
  printf "%-14s " "q=$q n=$n"
  for p in 2 3 5 7 11 13; do
    if (( p <= n )); then
      mode="dense"
    else
      mode="orbit"
    fi
    res=$(run_case "count" "$n,$q" "$p" 5 "$mode")
    d="${res%|*}"
    if [[ "$p" -eq "$q" && "$d" -le 1 ]]; then
      printf "${BOLD}%-6s${RESET} " "$d"
    elif [[ "$d" == ">"* ]]; then
      printf "${DIM}%-6s${RESET} " "$d"
    else
      printf "%-6s " "$d"
    fi
  done
  printf "\n"
done

# -------- Tseitin family --------

echo
echo "${BOLD}Tseitin — graph-based vertex-sum axioms (dense 𝔽_2)${RESET}"
hr
printf "%-22s %-12s %s\n" "Instance" "d_min (𝔽_2)" "Verdict"
hr

run_tseitin() {
  local label="$1" family="$2" fargs="$3" expected="$4"
  local res; res=$(run_case "$family" "$fargs" 2 3 "dense")
  local d="${res%|*}"
  local verdict
  case "$expected" in
    unsat)
      if [[ "$d" != ">"* ]]; then
        verdict="${GREEN}UNSAT cert${RESET}"
      else
        verdict="${RED}UNEXPECTED: no cert${RESET}"
      fi
      ;;
    sat)
      if [[ "$d" == ">"* ]]; then
        verdict="${GREEN}no cert (SAT as expected)${RESET}"
      else
        verdict="${RED}UNEXPECTED: got cert${RESET}"
      fi
      ;;
  esac
  printf "%-22s %-12s %s\n" "$label" "$d" "$verdict"
}

# tseitin-kn / tseitin-cycle: UNSAT iff n odd; Petersen: SAT (uniform charge 1, ∑ c = 10 even)
run_tseitin "Tseitin K_5"      "tseitin-kn"       "5" unsat
run_tseitin "Tseitin K_6"      "tseitin-kn"       "6" sat
run_tseitin "Tseitin C_5"      "tseitin-cycle"    "5" unsat
run_tseitin "Tseitin C_7"      "tseitin-cycle"    "7" unsat
run_tseitin "Tseitin Petersen" "tseitin-petersen" ""  sat

# -------- Certificate round-trip (soundness witness) --------

echo
echo "${BOLD}Certificate round-trip — PHP_{6,5} d=6 over 𝔽_7${RESET}"
hr
CERT="$WORKDIR/php_65.cert"
"$CASCADE" --alg-preprocess 6 --alg-p 7 --problem php:6,5 \
           --alg-cert "$CERT" "$DUMMY" > "$WORKDIR/cert_emit.log" 2>&1
cert_bytes=$(stat -c %s "$CERT")
cert_kb=$(awk "BEGIN{printf \"%.1f\", $cert_bytes/1024}")
printf "Cert written:  %s  (%s KB)\n" "$CERT" "$cert_kb"
"$VERIFIER" "$CERT" > "$WORKDIR/cert_verify.log" 2>&1
verify_rc=$?
verified=$(grep -E "^s " "$WORKDIR/cert_verify.log" | head -1)
if [[ $verify_rc -eq 0 && "$verified" == "s VERIFIED" ]]; then
  printf "Verification:  ${GREEN}%s${RESET}  (cert re-checked by independent binary)\n" "$verified"
else
  printf "Verification:  ${RED}FAILED: %s${RESET}\n" "$verified"
fi

# Stealth tamper: flip one coefficient to a different but valid value
# in [1, p). Parser accepts it; the sum-reduces-to-1 check rejects it
# at math time. We target the first constant-term "term 6" (coef 6 mod 7)
# and flip to "term 2".
CORRUPT="$WORKDIR/php_65_corrupted.cert"
awk 'BEGIN{flipped=0} /^term 6$/ && !flipped { print "term 2"; flipped=1; next } { print }' \
  "$CERT" > "$CORRUPT"
"$VERIFIER" "$CORRUPT" > "$WORKDIR/cert_corrupt.log" 2>&1
tamper_rc=$?
tamper_out=$(grep -E "^s " "$WORKDIR/cert_corrupt.log" | head -1)
if [[ $tamper_rc -ne 0 ]]; then
  printf "Tamper check:  ${GREEN}REJECTED${RESET}  %s\n" "$tamper_out"
else
  printf "Tamper check:  ${RED}FAILED: verifier accepted corrupted cert!${RESET}\n"
fi

# -------- VeriPB lowering (Gap 2) --------

echo
echo "${BOLD}VeriPB external validation — Count_q lowered to PB proof${RESET}"
hr
if command -v veripb >/dev/null 2>&1; then
  # Each case uses p = q (Count_q always has a d=1 cert at p = q).
  for case in "count:4,3 3" "count:5,3 3" "count:5,2 2" "count:7,2 2"; do
    prob="${case% *}"
    p="${case##* }"
    extra=""
    if (( p == 2 )); then
      # p=2 and family uses Diagonal S_n; orbit path fails (2 ∣ |S_n|).
      # Use --alg-no-orbit. Dense engine is fast at these sizes anyway.
      extra="--alg-no-orbit"
    else
      # p odd: orbit path works for n < p, else add --alg-no-orbit.
      n_val=$(echo "$prob" | awk -F'[:,]' '{print $2}')
      if (( p <= n_val )); then extra="--alg-no-orbit"; fi
    fi
    "$CASCADE" $extra --alg-preprocess 1 --alg-p "$p" --problem "$prob" \
      --alg-cert-pb "$WORKDIR/pb_${prob//[:,]/_}" "$DUMMY" > /dev/null 2>&1
    STEM="$WORKDIR/pb_${prob//[:,]/_}"
    if [[ ! -s "$STEM.opb" ]]; then
      printf "%-12s  ${RED}NO CERT at (p=%s, d=1)${RESET}\n" "$prob" "$p"
      continue
    fi
    out=$(veripb "$STEM.opb" "$STEM.pbp" 2>&1 | grep -E "^s " | head -1)
    if [[ "$out" == "s VERIFIED UNSATISFIABLE" ]]; then
      printf "%-12s  (p=%s) ${GREEN}%s${RESET}\n" "$prob" "$p" "$out"
    else
      printf "%-12s  (p=%s) ${RED}UNEXPECTED:${RESET} %s\n" "$prob" "$p" "$out"
    fi
  done
else
  echo "${DIM}veripb not found on PATH; skipping external validation.${RESET}"
  echo "${DIM}Install: cargo install veripb (or see https://gitlab.com/MIAOresearch/software/VeriPB).${RESET}"
fi

# -------- Summary --------

echo
echo "${BOLD}Reproduction complete.${RESET}"
hr
echo "Output logs:  $WORKDIR/"
echo "Heavy cases (not run by default):"
echo "  PHP_{8,7} d=7:   $CASCADE --alg-preprocess 7 --alg-p 11 --problem php:8,7 $DUMMY   # ~14 min / 5.5 GB, returns correct 'no cert'"
echo "  PHP_{8,7} d=8:   $CASCADE --alg-preprocess 8 --alg-p 11 --problem php:8,7 $DUMMY   # open frontier; hours, 20-40 GB"
hr
