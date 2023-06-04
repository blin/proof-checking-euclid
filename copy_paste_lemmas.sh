#!/usr/bin/env bash


grep "$1" copy_paste_lemmas.txt | sed "s/X/$2/g;s/Y/$3/g;s/Z/$4/g"
