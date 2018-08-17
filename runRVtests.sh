# !/bin/bash

ufiles=$(ls $1/rv64ui-p-*.dump)
mfiles=$(ls $1/rv64mi-p-*.dump)

for g in $ufiles; do
  f=${g%.dump}
  ./runELF.sh $f
done
for g in $mfiles; do
  f=${g%.dump}
  ./runELF.sh $f
done
