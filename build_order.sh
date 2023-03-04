#!/usr/bin/env bash

checkpoints=(
"proposition_01"
"proposition_02"
"proposition_03"
"lemma_equalanglesNC"
"lemma_layoffunique"
"proposition_04"
"proposition_05"
"proposition_10"
"proposition_12"
"lemma_planeseparation"
"lemma_collinearright"
"proposition_07"
)

make clean >/dev/null
for checkpoint in "${checkpoints[@]}"; do
	make $checkpoint".glob" | grep -E -v 'COQDEP VFILES' | sed -E 's/COQC //;s/^"coqc".*ProofCheckingEuclid //'
done
