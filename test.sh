#!/bin/sh
set -e
bnfc  quail.cf
alex  Lexquail.x
happy Parquail.y
ghc --make  -Wall -fno-warn-name-shadowing Run.hs
for i; do
  echo "$i"
  ./Run "$i"
done
