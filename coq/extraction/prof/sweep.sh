#!/usr/bin/env bash
# sweep.sh LABEL BIN LIMIT SHAPE K... : time BIN on each machine, timeout LIMIT s.
P=$(dirname "$0"); label=$1; bin=$2; lim=$3; shape=$4; shift 4
for k in "$@"; do
  out=$( { /usr/bin/time -l timeout $lim $bin $P/$shape$k.m >/dev/null; } 2>&1 ); rc=$?
  real=$(echo "$out" | awk '/real/ {print $1}'); rss=$(echo "$out" | awk '/maximum resident/ {printf "%.0f", $1/1048576}')
  echo "$label $shape k=$k rc=$rc real=${real}s rss=${rss}MiB"
done
