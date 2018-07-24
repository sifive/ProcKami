# !/bin/bash

files=$(ls $1/rv64ui-p-*.dump)

for g in $files; do
  f=${g%.dump}
  ./runSingle.sh $f
done
