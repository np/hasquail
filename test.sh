#!/bin/sh
set -e
bnfc  quail.cf
alex  Lexquail.x
happy Parquail.y
ghc --make -O2  -Wall -fno-warn-name-shadowing Run.hs -rtsopts
for i; do
  echo "$i"
  ./Run "$i"
done
