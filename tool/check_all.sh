#!/bin/bash

# Change into the repositories root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

echo "module Everything where" > Everything.agda
for f in $(find . -name "*.agda")
do
  if [ "$f" = "./Everything.agda" ]; then
    continue
  fi
  echo "import$( grep -m 1 -Po "(?<=module)\s+[a-zA-Z\.0-9]+\s+(?=where)" $f )" >> Everything.agda
done
agda --verbose=2 -i "." Everything.agda
