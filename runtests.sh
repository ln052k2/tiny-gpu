#!/bin/bash
for file in test/*.sv; do
  vsim -c `basename $file .sv` -L gpu -L base -do "run -all"
done