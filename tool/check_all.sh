#!/bin/bash

# Change into the repositories root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

set -e
for f in $(find . -name "*.agda")
do
  agda "$f"
done
