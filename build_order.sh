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
"proposition_06"
"proposition_08"
"proposition_09"
"proposition_11"
"proposition_13"
"proposition_14"
"proposition_15"
"proposition_16"
"proposition_17"
"proposition_18"
"proposition_19"
"proposition_20"
"proposition_21"
"proposition_22"
"proposition_23"
"proposition_24"
"lemma_Euclid4"
"proposition_25"
"proposition_26A"
"proposition_27"
)

make clean >/dev/null
for checkpoint in "${checkpoints[@]}"; do
	make $checkpoint".glob" | grep -E -v 'COQDEP VFILES' | sed -E 's/COQC //;s/^"coqc".*ProofCheckingEuclid //'
done
