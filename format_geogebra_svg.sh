#!/usr/bin/env bash

remove_tag_with_values=(
'font-family="geogebra-sans-serif, sans-serif"'
'font-family="geogebra-sans-serif, sans-serif"'
'font-style="normal"'
'paint-order="fill stroke markers"'
'font-weight="normal"'
'text-decoration="normal"'
'dominant-baseline="alphabetic"'
'fill-opacity="1"'
'font-size="16px"'
'text-anchor="start"'
)

for remove_tag_with_value in "${remove_tag_with_values[@]}"; do
    sed -i "/$remove_tag_with_value/d" $1
done
