for file in tests/*.sv; do
  vsim -c `basename $file` -L gpu -L base -do "run -all"
done
