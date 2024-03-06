#!/usr/bin/env bash

_matrix=''
for item in $(cat tests.txt); do
  _matrix+="'$item', "
done

echo "name=matrix::[$_matrix]" >> "$GITHUB_ENV"
