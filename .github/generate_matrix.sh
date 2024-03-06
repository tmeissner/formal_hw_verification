#!/usr/bin/env bash

_matrix=''
for item in $(cat tests.txt); do
  _matrix+="'$item', "
done

echo "matrix=[$_matrix]" >> "$GITHUB_ENV"
